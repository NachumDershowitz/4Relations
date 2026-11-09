#!/usr/bin/env python3
"""Verify WFU artifacts without modifying archived sources or records.

The default full scope also requires every requested component. Missing evidence
is a nonzero result, even when all recovered checks pass. No historical SMT
searches are rerun by this command; --with-smt runs supplementary local checks.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scope', choices=['full', 'recovered'], default='full')
    parser.add_argument('--with-smt', action='store_true',
                        help='also run all supplementary SMT diagnostics')
    parser.add_argument('--log-dir', type=Path,
                        help='new directory for complete logs; default is a temporary directory')
    args = parser.parse_args()
    if args.log_dir:
        logs = args.log_dir.resolve()
        logs.mkdir(parents=True, exist_ok=False)
    else:
        logs = Path(tempfile.mkdtemp(prefix='wfu-validation-'))
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONUNBUFFERED='1')
    # Archived audits use assert; optimized Python would disable these checks.
    env.pop('PYTHONOPTIMIZE', None)
    report = {
        'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'scope': args.scope, 'python': sys.version, 'platform': platform.platform(),
        'requested_package_complete': False, 'recovered_checks_passed': False,
        'historical_smt_searches_rerun': False, 'stages': [],
        'environment_overrides': {
            key: env[key] for key in ['PYTHONDONTWRITEBYTECODE', 'PYTHONUNBUFFERED', 'LIBZ3'] if key in env
        },
    }

    def save():
        (logs / 'RESULT.json').write_text(json.dumps(report, indent=2) + '\n')

    def run(name, command, cwd):
        started = time.monotonic()
        print(name, flush=True)
        with (logs / (name + '.log')).open('w') as stream:
            stream.write('Command: ' + repr(command) + '\nWorking directory: ' + str(cwd) + '\n\n')
            stream.flush()
            result = subprocess.run(command, cwd=cwd, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT)
        report['stages'].append({'name': name, 'command': command, 'cwd': str(cwd),
                                 'exit_status': result.returncode,
                                 'elapsed_seconds': round(time.monotonic() - started, 3)})
        save()
        if result.returncode:
            raise RuntimeError(f'{name} failed with exit {result.returncode}; see {logs}')

    try:
        if sys.flags.optimize:
            raise RuntimeError('Run Python without -O: archived audits require assertions.')
        run('python_version', [sys.executable, '--version'], ROOT)
        for tool in ['rocq', 'rocqchk']:
            binary = shutil.which(tool)
            if not binary:
                raise RuntimeError(f'Required tool missing from PATH: {tool}')
            run(tool + '_version', [binary, '--version'], ROOT)
        if (ROOT / 'SHA256SUMS').exists():
            run('integrity', [sys.executable, str(ROOT / 'verify_integrity.py')], ROOT)
        else:
            report['integrity'] = 'Manifest not yet generated during initial preparation.'
        run('finite_coverage', [sys.executable, 'verification/verify_results.py'], ROOT)
        run('counterexample', ['sh', 'formal_proofs/check.sh'], ROOT)
        with tempfile.TemporaryDirectory(prefix='wfu-proof-build-') as tmp:
            copied = Path(tmp) / 'supplement'
            shutil.copytree(ROOT / 'supplement-2026-10-20', copied)
            for directory in ['folding_checks', 'height_checks']:
                (copied / 'checks' / directory).mkdir(parents=True, exist_ok=True)
            try:
                run('october_rocq', [sys.executable, 'scripts/verify.py'], copied)
                details = json.loads((copied / 'logs/final/RESULT.json').read_text())
                if details.get('kernel_verified') is not True:
                    raise RuntimeError('October proof verifier did not establish kernel acceptance.')
                report['october_rocq'] = {
                    key: details[key] for key in ['kernel_verified', 'checked_declarations', 'global_axioms']
                }
                for name in ['exhaustive_three_points', 'exhaustive_original_conditions']:
                    run(name, [sys.executable, 'checks/' + name + '.py'], copied)
                if args.with_smt:
                    for name in ['check_folding_obligations', 'check_height_obligations']:
                        run(name, [sys.executable, 'checks/' + name + '.py'], copied)
            finally:
                if (copied / 'logs/final').exists():
                    shutil.copytree(copied / 'logs/final', logs / 'october-proof-details')
                dest = logs / 'fresh-experiments'
                for path in (copied / 'checks').rglob('*'):
                    if path.is_file() and path.suffix in ['.json', '.out', '.smt2']:
                        target = dest / path.relative_to(copied / 'checks')
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(path, target)
        command = [sys.executable, 'verification/verify_general.py', '--log-dir', str(logs / 'general-details')]
        if args.with_smt:
            command.append('--with-smt')
        run('general_development', command, ROOT)
        details = json.loads((logs / 'general-details/RESULT.json').read_text())
        if not details.get('passed') or not details.get('general_kernel_verified'):
            raise RuntimeError('General development verification did not establish success.')
        report['general_development'] = {key: details[key] for key in
            ['passed', 'general_kernel_verified', 'named_theorems', 'inference_steps',
             'closed_theorems', 'classical_theorems', 'source_sha256']}
        report['recovered_checks_passed'] = True
        missing = json.loads((ROOT / 'MISSING_COMPONENTS.json').read_text())
        report['missing_components'] = missing
        report['requested_package_complete'] = not missing
        if args.scope == 'full' and missing:
            report['outcome'] = 'INCOMPLETE_REQUESTED_PACKAGE'
            report['exit_status'] = 2
            print('Recovered checks passed; the requested package is incomplete. See MISSING_COMPONENTS.json.')
            return 2
        report['outcome'] = 'FULL_SCOPE_PASS' if args.scope == 'full' else 'RECOVERED_SCOPE_PASS'
        report['exit_status'] = 0
        print('PASS for', args.scope, 'scope. Logs:', logs)
        return 0
    except Exception as error:
        report['outcome'] = 'FAILED'
        report['failure'] = str(error)
        report['exit_status'] = 1
        print(str(error), file=sys.stderr)
        return 1
    finally:
        report['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        save()


if __name__ == '__main__':
    sys.exit(main())
