#!/usr/bin/env python3
"""Fresh general-certificate, Rocq, five-relation and reset verification."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path, required=True)
    parser.add_argument('--with-smt', action='store_true')
    args = parser.parse_args()
    logs = args.log_dir.resolve()
    logs.mkdir(parents=True, exist_ok=False)
    report = {'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'passed': False, 'stages': [], 'general_kernel_verified': False}
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONUNBUFFERED='1')
    env.pop('PYTHONOPTIMIZE', None)
    report['environment_overrides'] = {k: env[k] for k in
        ['PYTHONDONTWRITEBYTECODE', 'PYTHONUNBUFFERED', 'LIBZ3'] if k in env}

    def save():
        (logs / 'RESULT.json').write_text(json.dumps(report, indent=2) + '\n')

    def run(name, cmd, cwd):
        print(name, flush=True)
        start = time.monotonic()
        with (logs / (name + '.log')).open('w') as stream:
            stream.write('Command: ' + repr(cmd) + '\nCwd: ' + str(cwd) + '\n\n')
            stream.flush()
            result = subprocess.run(cmd, cwd=cwd, env=env, stdout=stream, stderr=subprocess.STDOUT)
        report['stages'].append({'name': name, 'command': cmd, 'cwd': str(cwd),
            'exit_status': result.returncode, 'elapsed_seconds': round(time.monotonic()-start, 3)})
        save()
        if result.returncode:
            raise RuntimeError(f'{name} failed with exit {result.returncode}')

    try:
        if sys.flags.optimize:
            raise RuntimeError('Run without -O; the reset check uses assertions.')
        with tempfile.TemporaryDirectory(prefix='wfu-general-') as temp:
            work = Path(temp)
            general = work / 'general'
            shutil.copytree(ROOT / 'general', general)
            shutil.copytree(ROOT / 'reset', work / 'reset')
            formal = general / 'formal'
            try:
                run('certificate', ['sh', 'check.sh'], general)
                run('rocq', ['sh', 'check_rocq.sh'], formal)
                marker = json.loads((formal / 'rocq-results/KERNEL_CHECK_PASSED').read_text())
                if marker['status'] != 'ROCQ_KERNEL_CHECK_PASSED':
                    raise RuntimeError('Missing established-kernel success record')
                build = Path(marker['run_directory'])
                source = formal / 'WellFoundedUnionsProofTerms.v'
                text = re.sub(r'\(\*.*?\*\)', '', source.read_text(), flags=re.S)
                forbidden = re.findall(r'\b(?:Admitted|admit|Axiom|Axioms|Parameter|Parameters|'
                    r'Conjecture|Abort|exact_no_check|vm_cast_no_check|native_cast_no_check)\b|'
                    r'Unset\s+(?:Guard|Positivity|Universe)\s+Checking', text)
                if forbidden:
                    raise RuntimeError('Unexpected proof bypass or axiom declaration: ' + repr(forbidden))
                certificate = json.loads((formal / 'proof.json').read_text())
                names = list(certificate['theorems'])
                audit = ['Require Import WellFoundedUnionsProofTerms.', 'Set Printing Width 100.']
                for i, name in enumerate(names):
                    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name):
                        raise RuntimeError('Invalid theorem identifier')
                    audit += [f'Check {name}.', f'Print Assumptions {name}.',
                        f'Redirect "assumption_{i:03d}" Print Assumptions {name}.']
                (build / 'AllGeneralAssumptions.v').write_text('\n'.join(audit) + '\n')
                run('all_named_assumptions', ['rocq', 'compile', '-q', 'AllGeneralAssumptions.v'], build)
                assumptions = {}
                target = logs / 'assumptions'
                target.mkdir()
                for i, name in enumerate(names):
                    output = (build / f'assumption_{i:03d}.out').read_text().strip()
                    (target / (name + '.txt')).write_text(output + '\n')
                    if output == 'Closed under the global context':
                        assumptions[name] = []
                    elif re.fullmatch(r'Axioms:\s*(?:(?:Stdlib\.Logic\.)?Classical_Prop\.)?classic\s*'
                                      r':\s*forall P : Prop, P \\/ ~ P', output):
                        assumptions[name] = ['Stdlib.Logic.Classical_Prop.classic']
                    else:
                        raise RuntimeError('Unexpected assumptions for ' + name + ': ' + output)
                shutil.copy2(build / 'AllGeneralAssumptions.v', logs / 'AllGeneralAssumptions.v')
                (logs / 'assumptions.json').write_text(json.dumps(assumptions, indent=2) + '\n')
                report.update(general_kernel_verified=True, named_theorems=len(names),
                    inference_steps=len(certificate['proof']), forbidden_tokens=forbidden,
                    closed_theorems=sum(not a for a in assumptions.values()),
                    classical_theorems=sum(bool(a) for a in assumptions.values()),
                    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
                compiler = shutil.which(os.environ.get('CXX', 'c++'))
                if not compiler:
                    raise RuntimeError('A C++17 compiler is required for the five-relation experiment.')
                run('cpp_version', [compiler, '--version'], work)
                run('compile_five_relations', [compiler, '-O2', '-std=c++17',
                    'general/supplement/check_generalization.cpp', '-o', 'check_generalization'], work)
                run('five_relations', [str(work / 'check_generalization'), '3', '5'], work)
                record = json.loads((logs / 'five_relations.log').read_text().split('\n\n', 1)[1])
                if record['tuples'] != 9765625 or record['cyclic_unions'] != 0:
                    raise RuntimeError('Unexpected five-relation result: ' + repr(record))
                (logs / 'five_relations.json').write_text(json.dumps(record, indent=2) + '\n')
                scripts = ['check_representative_elimination.py', 'check_height_elimination.py',
                    'checks/exhaustive_original_conditions.py', 'checks/exhaustive_three_points.py',
                    'checks/test_review_regressions.py']
                if args.with_smt:
                    scripts += ['checks/check_folding_obligations.py', 'checks/check_height_obligations.py',
                        'checks/check_existential_folding.py', 'checks/check_infinite_counterexample.py']
                for script in scripts:
                    run(Path(script).stem, [sys.executable, 'supplement/' + script], general)
                run('reset_bounded_check', [sys.executable, 'reset/checks/check_reset.py'], work)
                expected = json.loads((ROOT / 'historical/reset-clean-revision/checks/reset_checks.json').read_text())
                actual = json.loads((work / 'reset/checks/reset_checks.json').read_text())
                if actual != expected:
                    raise RuntimeError('Reset bounded test differs from its recorded result.')
                report['reset_record_reproduced_exactly'] = True
            finally:
                for path in (formal / 'logs').glob('*.log'):
                    dest = logs / 'certificate-logs' / path.name
                    dest.parent.mkdir(exist_ok=True)
                    shutil.copy2(path, dest)
                if (formal / 'CHECKED.json').exists():
                    shutil.copy2(formal / 'CHECKED.json', logs / 'certificate-CHECKED.json')
                for path in (formal / 'rocq-results').rglob('*'):
                    if path.is_file() and (path.suffix == '.log' or path.name == 'KERNEL_CHECK_PASSED'):
                        dest = logs / 'rocq-results' / path.relative_to(formal / 'rocq-results')
                        dest.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(path, dest)
                for folder in [general / 'supplement', work / 'reset']:
                    for path in folder.rglob('*'):
                        if path.is_file() and path.suffix in ['.json', '.smt2', '.out']:
                            dest = logs / 'experiments' / path.relative_to(work)
                            dest.parent.mkdir(parents=True, exist_ok=True)
                            shutil.copy2(path, dest)
        report['passed'] = True
        report['exit_status'] = 0
        return 0
    except Exception as error:
        report.update(failure=str(error), exit_status=1)
        print(str(error), file=sys.stderr)
        return 1
    finally:
        report['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        save()


if __name__ == '__main__':
    sys.exit(main())
