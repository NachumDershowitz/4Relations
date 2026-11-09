#!/usr/bin/env python3
"""Audit archived case coverage and saved outcomes; does not rerun SMT solving."""
from collections import Counter
from itertools import product
from pathlib import Path
import argparse
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rows(folder, filename, header=False):
    data = [line.split("\t") for line in (folder / filename).read_text().splitlines()
            if line.strip()]
    return data[1:] if header else data


def expected_roots(n):
    result = set()
    for length in range(2, n):
        patterns = (["DC" + "".join(t) for t in product("CD", repeat=length-2)]
                    if length <= n // 2 else ["DC" + "X" * (length-2)])
        for pattern in patterns:
            for s0 in range(length, n):
                for s1 in range(length, s0+1):
                    result.add((pattern, s0, s1))
    return result


def root_rows(folder, n):
    result = {}
    direct = f"n{n}_strong_results_results.tsv"
    data = rows(folder, direct)
    data += [r[1:] for r in rows(folder, "remaining_strong_results_results.tsv")
             if r[0] == str(n)]
    for r in data:
        key = (r[0], int(r[1]), int(r[2]))
        require(key not in result, f"Duplicate n={n} root: {key}")
        require(r[3] in {"unsat", "unknown"}, f"Unexpected outcome: {r}")
        require(r[3] != "unsat" or r[-1] == "0", f"Failed UNSAT run: {r}")
        result[key] = r[3]
    require(set(result) == expected_roots(n), f"Incomplete n={n} root partition")
    return result


def verify(root=ROOT):
    tables = root / "finite/computation"
    nine = root_rows(tables, 9)
    ten = root_rows(tables, 10)
    require(set(nine.values()) == {"unsat"}, "Unresolved nine-point case")
    for name, index, header in [("l2_refine1_results.tsv", 5, False),
                                ("bv_residual20_results.tsv", 3, True)]:
        for row in rows(tables, name, header):
            require(row[index] in {"unsat", "unknown"}, f"Unexpected outcome: {row}")
            require(row[index] != "unsat" or row[-1] == "0", f"Failed UNSAT run: {row}")

    # The original audit verifies every refinement key and regenerates both
    # final SMT inputs byte for byte, including their recorded generator hashes.
    # It writes a report, so run it on a disposable copy of the evidence.
    with tempfile.TemporaryDirectory(prefix="four-relations-audit-") as temp:
        copied = Path(temp) / "finite"
        shutil.copytree(root / "finite", copied)
        run = subprocess.run(
            [sys.executable, str(copied / "completion/audit_completed_cover.py")],
            cwd=copied, text=True, capture_output=True)
        require(run.returncode == 0, "Completed-cover audit failed:\n" + run.stdout + run.stderr)
        cover = json.loads((copied / "completion/completed_cover.json").read_text())
    require(cover["result"] == "COMPLETE_UNSAT_COVER" and not cover["unresolved"],
            "Unresolved ten-point case")
    recorded = json.loads((root / "finite/completion/completed_cover.json").read_text())
    require(cover == recorded, "Saved coverage report differs from reproduced audit")
    l2_root = sum(status == "unsat" for key, status in ten.items() if len(key[0]) == 2)
    other_root = sum(status == "unsat" for key, status in ten.items() if len(key[0]) > 2)
    l2_leaves = (l2_root + cover["refinement_unsat"] + cover["residual_previously_unsat"]
                 + len(cover["completed_branches"]))
    require(l2_leaves + other_root == cover["final_leaf_obligations"], "Leaf count mismatch")
    return {
        "result": "PASS",
        "nine_point_root_cases": len(nine),
        "nine_point_cases_by_cycle_length": dict(sorted(Counter(len(k[0]) for k in nine).items())),
        "ten_point_root_cases": len(ten),
        "ten_point_longer_cycle_leaves": other_root,
        "ten_point_two_cycle_leaves": l2_leaves,
        "ten_point_two_cycle_breakdown": [l2_root, cover["refinement_unsat"],
                                          cover["residual_previously_unsat"],
                                          len(cover["completed_branches"])],
        "ten_point_terminal_obligations": cover["final_leaf_obligations"],
        "unresolved": cover["unresolved"],
        "final_inputs_regenerated_exactly": True,
        "component_mask_runs_used_as_proof_leaves": False,
        "scope": "Exhaustive case coverage, saved outcomes and exit codes, exact final-input regeneration, and hashes. No solver reruns or independent checking of Z3 proof certificates."
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = json.dumps(verify(args.root.resolve()), indent=2) + "\n"
    if args.output:
        args.output.write_text(report)
    print(report, end="")
