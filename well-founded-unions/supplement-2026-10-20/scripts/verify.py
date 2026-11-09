#!/usr/bin/env python3
"""Fresh compilation, statement/assumption audits, and independent rocqchk.

Only a successful compiler AND standalone checker produce kernel_verified=true.
The build uses source copies and no pre-existing .vo files. No solver is trusted.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ["FourRelations.v", "Refinements.v", "FourRelationsCounterexample.v", "Audit.v"]


def uncomment(text):
    """Strip nested Rocq comments while preserving line boundaries."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == "(*":
            depth += 1
            i += 2
        elif depth and text[i:i+2] == "*)":
            depth -= 1
            i += 2
        else:
            if not depth or text[i] == "\n":
                out.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed comment")
    return "".join(out)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    build = ROOT / "build/rocq"
    logs = ROOT / "logs/final"
    if build.exists():
        shutil.rmtree(build)
    if logs.exists():
        shutil.rmtree(logs)
    build.mkdir(parents=True)
    logs.mkdir(parents=True)
    report = {"kernel_verified": False, "stages": [], "sources": {}, "assumptions": {}}
    started = time.monotonic()

    def save():
        (logs / "RESULT.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(name, command):
        print(name, flush=True)
        with (logs / (name + ".log")).open("w") as f:
            f.write("Command: " + repr(command) + "\n\n")
            f.flush()
            proc = subprocess.run(command, cwd=build, stdout=f, stderr=subprocess.STDOUT)
        report["stages"].append({"name": name, "command": command,
                                 "exit_status": proc.returncode})
        save()
        if proc.returncode:
            raise RuntimeError(f"{name} failed: see {logs / (name + '.log')}")

    try:
        rocq = shutil.which("rocq")
        checker = shutil.which("rocqchk")
        if not rocq or not checker:
            raise RuntimeError("Install Rocq and rocqchk and put them on PATH.")
        run("toolchain", [rocq, "--version"])
        run("checker_version", [checker, "--version"])
        declarations = []
        hygiene = {}
        for filename in SOURCES:
            source = ROOT / "rocq" / filename
            text = uncomment(source.read_text())
            forbidden = re.findall(
                r"\b(?:Admitted|admit|Axiom|Axioms|Parameter|Parameters|"
                r"Conjecture|Abort|exact_no_check|vm_cast_no_check|"
                r"native_cast_no_check)\b|"
                r"Unset\s+(?:Guard|Positivity|Universe)\s+Checking", text)
            if forbidden:
                raise RuntimeError(f"Proof bypass or new axiom in {filename}: {forbidden}")
            names = re.findall(
                r"^(?:Lemma|Theorem|Corollary|Definition|Fixpoint|Inductive)\s+(\w+)",
                text, re.M)
            prefix = f"FourRelations.{source.stem}."
            if filename == "FourRelationsCounterexample.v":
                prefix += "FourRelations."
            declarations.extend(prefix + name for name in names)
            hygiene[filename] = {"declarations": len(names), "forbidden_tokens": forbidden}
            shutil.copy2(source, build / filename)
            report["sources"][filename] = digest(source)
        (logs / "source_hygiene.json").write_text(json.dumps(hygiene, indent=2) + "\n")
        # Preserve the exact old theorem statements across all proof repairs.
        baseline = ROOT / "originals/failed_FourRelations.v"
        if baseline.exists():
            def statements(p):
                return {n: re.sub(r"\s+", " ", s).strip() for n, s in re.findall(
                    r"(?:Lemma|Theorem|Corollary)\s+(\w+)(.*?)\bProof\.",
                    uncomment(p.read_text()), re.S)}
            old, new = statements(baseline), statements(ROOT / "rocq/FourRelations.v")
            if old != new:
                raise RuntimeError("An original theorem statement changed.")
            (logs / "statement_preservation.json").write_text(json.dumps(
                {"identical": True, "original_statements": len(old)}, indent=2) + "\n")
        for filename in SOURCES:
            run("compile_" + Path(filename).stem,
                [rocq, "compile", "-q", "-time", "-Q", ".", "FourRelations",
                 "-output-directory", ".", filename])
        audit = ["From FourRelations Require Import FourRelations Refinements "
                 "FourRelationsCounterexample Audit.", "Set Printing Width 100."]
        for i, name in enumerate(declarations):
            audit += [f"Check {name}.", f'Print Assumptions {name}.',
                      f'Redirect "assumption_{i:03d}" Print Assumptions {name}.']
        (build / "AllAssumptions.v").write_text("\n".join(audit) + "\n")
        shutil.copy2(build / "AllAssumptions.v", logs / "AllAssumptions.v")
        run("compile_AllAssumptions", [rocq, "compile", "-q", "-Q", ".", "FourRelations",
                                      "-output-directory", ".", "AllAssumptions.v"])
        out = logs / "assumptions"
        out.mkdir()
        for i, name in enumerate(declarations):
            p = build / f"assumption_{i:03d}.out"
            text = p.read_text().strip()
            shutil.copy2(p, out / (name + ".txt"))
            if text == "Closed under the global context":
                deps = []
            elif re.fullmatch(
                    r"Axioms:\s*(?:Stdlib\.Logic\.)?Classical_Prop\.classic\s*"
                    r":\s*forall P : Prop, P \\/ ~ P", text):
                deps = ["Stdlib.Logic.Classical_Prop.classic"]
            else:
                raise RuntimeError(f"Unrecognized assumptions for {name}: {text}")
            report["assumptions"][name] = deps
        run("rocqchk", [checker, "-Q", ".", "FourRelations", "-o",
                       *["FourRelations." + Path(n).stem for n in SOURCES],
                       "FourRelations.AllAssumptions"])
        checklog = (logs / "rocqchk.log").read_text()
        if "Modules were successfully checked" not in checklog:
            raise RuntimeError("Checker did not report successful module checking.")
        for filename, expected in report["sources"].items():
            if digest(ROOT / "rocq" / filename) != expected:
                raise RuntimeError("Source changed during verification.")
        report["proof_objects"] = {p.name: digest(p) for p in sorted(build.glob("*.vo"))}
        report["kernel_verified"] = True
        report["global_axioms"] = sorted({a for v in report["assumptions"].values() for a in v})
        report["checked_declarations"] = len(declarations)
        print(f"VERIFIED: {len(declarations)} declarations; independent rocqchk passed.")
        return 0
    except Exception as e:
        report["failure"] = str(e)
        print("NOT VERIFIED:", e, file=sys.stderr)
        return 1
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        save()


if __name__ == "__main__":
    sys.exit(main())
