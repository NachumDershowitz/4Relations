#!/usr/bin/env python3
"""Failure-handling tests for the repaired supplementary checks, not proofs."""
from __future__ import annotations
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
rows = []


def record(name: str, process: subprocess.CompletedProcess[str], expected_failure: bool) -> None:
    passed = (process.returncode != 0) if expected_failure else (process.returncode == 0)
    rows.append({'test': name, 'exit_status': process.returncode, 'passed': passed,
                 'stdout': process.stdout, 'stderr': process.stderr})
    if not passed:
        raise RuntimeError(f'{name}: unexpected exit {process.returncode}')


with tempfile.TemporaryDirectory(prefix='four-relations-regressions-') as tmp:
    temp = Path(tmp)
    (temp / 'z3_runner.py').write_text(
        'def run_z3(smt, **kwargs):\n'
        '    return \'(:version "test-double")\' if "get-info" in smt else "sat\\n"\n')
    for script in ('check_folding_obligations.py', 'check_existential_folding.py'):
        (temp / script).write_bytes((HERE / script).read_bytes())
        p = subprocess.run([sys.executable, '-O', str(temp / script)],
                           cwd=temp, capture_output=True, text=True, timeout=20)
        record('reject_wrong_solver_answer_under_optimization_' + script, p, True)
    (temp / 'exhaustive_three_points.py').write_bytes((HERE / 'exhaustive_three_points.py').read_bytes())
    p = subprocess.run([sys.executable, '-O', '-c',
        'from exhaustive_three_points import require; require(False, "injected failure")'],
        cwd=temp, capture_output=True, text=True, timeout=20)
    record('invariant_checks_survive_python_optimization', p, True)
    p = subprocess.run([sys.executable, '-O', '-c',
        'from exhaustive_three_points import require; require(True, "should pass")'],
        cwd=temp, capture_output=True, text=True, timeout=20)
    record('true_invariant_is_accepted', p, False)

report = {'scope': 'test-harness failure handling only; not theorem verification',
          'all_passed': all(r['passed'] for r in rows), 'tests': rows}
(HERE.parent / 'review_regressions.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'all_passed': report['all_passed'],
                  'tests': [{k: r[k] for k in ('test', 'exit_status', 'passed')} for r in rows]}, indent=2))
