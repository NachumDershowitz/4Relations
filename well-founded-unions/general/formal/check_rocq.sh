#!/bin/sh
# Optional established-kernel validation. Uses a fresh directory and fails closed.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
mkdir -p rocq-results
rm -f rocq-results/KERNEL_CHECK_PASSED
if ! command -v rocq >/dev/null 2>&1; then
  printf '%s\n' 'NOT ROCQ-VERIFIED: Rocq 9 compiler is not installed.' > rocq-results/compiler.log
  cat rocq-results/compiler.log >&2
  exit 127
fi
work=$(mktemp -d "$PWD/rocq-results/run.XXXXXXXX")
cp WellFoundedUnionsProofTerms.v "$work/"
(
  cd "$work"
  rocq c -v > version.log 2>&1
  rocq c -q WellFoundedUnionsProofTerms.v > compile.log 2>&1
  rocq check WellFoundedUnionsProofTerms > kernel-check.log 2>&1
  python3 - <<'PY'
from pathlib import Path
import re
s=Path('compile.log').read_text()
expected=Path('WellFoundedUnionsProofTerms.v').read_text().count('Print Assumptions ')
if s.count('Axioms:') != expected:
    raise SystemExit(f'Assumption audit: expected {expected} Print Assumptions outputs.')
if re.search(r'(?m)^Error:', s):raise SystemExit('Compilation reported an error.')
for block in s.split('Axioms:')[1:]:
    declarations=re.findall(r'(?m)^([A-Za-z_][\w.]*)(?:\s*:\s*|\s*$)',block)
    for name in declarations:
        if name not in ('classic','Classical_Prop.classic','Stdlib.Logic.Classical_Prop.classic'):
            raise SystemExit('Unexpected assumption: '+name)
    if not any(x.endswith('classic') for x in declarations):
        raise SystemExit('Could not identify excluded middle in assumption output.')
print('Assumption outputs contain only the permitted excluded-middle declaration.')
PY
)
python3 - "$work" <<'PY'
from pathlib import Path
import hashlib,json,sys
w=Path(sys.argv[1]);r={
 'status':'ROCQ_KERNEL_CHECK_PASSED',
 'run_directory':str(w),
 'source_sha256':hashlib.sha256((w/'WellFoundedUnionsProofTerms.v').read_bytes()).hexdigest(),
 'logs':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in w.glob('*.log')},
}
Path('rocq-results/KERNEL_CHECK_PASSED').write_text(json.dumps(r,indent=2)+'\n')
print('Rocq compilation, standalone kernel checking, and assumption audit passed.')
PY
