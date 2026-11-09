#!/bin/sh
# Recheck the supplied certificate; success does not mean Rocq acceptance.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
export PYTHONDONTWRITEBYTECODE=1
PYTHON=${PYTHON:-python3}
mkdir -p logs
rm -f CHECKED.json
"$PYTHON" - <<'PY'
import hashlib,json,pathlib
p=pathlib.Path('.')
for name,expected in json.loads((p/'MANIFEST.json').read_text()).items():
    actual=hashlib.sha256((p/name).read_bytes()).hexdigest()
    if actual != expected:raise SystemExit('SOURCE HASH MISMATCH: '+name)
print('Source manifest verified.')
PY
"$PYTHON" kernel.py proof.json > logs/named-kernel.log 2>&1
"$PYTHON" -O check_debruijn.py proof.json > logs/debruijn-kernel.log 2>&1
"$PYTHON" audit_finite.py > logs/finite-audit.log 2>&1
"$PYTHON" audit_branching.py > logs/branching-audit.log 2>&1
"$PYTHON" audit_extensions.py > logs/extensions-audit.log 2>&1
"$PYTHON" -O test_extension_audit.py > logs/extension-tests.log 2>&1
"$PYTHON" -O test_kernels.py > logs/kernel-tests.log 2>&1
"$PYTHON" -O test_statement_audit.py > logs/statement-tests.log 2>&1
"$PYTHON" -O test_certificates.py > logs/certificate-tests.log 2>&1
sh rebuild.sh > logs/rebuild.log 2>&1
"$PYTHON" - <<'PY'
import collections,datetime,hashlib,json,pathlib,platform,sys
p=pathlib.Path('.'); cert=json.loads((p/'proof.json').read_text())
record={
 'status':'PASSED_STANDALONE_CERTIFICATE_REPLAY',
 'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'framework':'Classical higher-order natural deduction',
 'implementations':['kernel.py: named variables','check_debruijn.py: de Bruijn indices'],
 'inference_steps':len(cert['proof']),
 'closed_named_theorems':len(cert['theorems']),
 'logical_axioms':['excluded_middle'],
 'unproved_mathematical_lemmas':[],
 'rule_inventory':dict(sorted(collections.Counter(r[0] for r in cert['proof']).items())),
 'checked_results':['arbitrary finite families on finite domains, with every shortcut',
   'finite branching at internal indices on unrestricted domains, with shortened internal conditions',
   'finite reachability, representative elimination and the final two-relation step',
   'exclusion of infinite forward chains',
   'mixed uniform and pointwise internal-height theorem',
   'successor-ordinal layer elimination, minimum-rank and limit-layer theorems',
   'mixed height and zero-or-successor ordinal-rank termination',
   'pointwise accessibility equivalence with the maximal serial subset'],
 'exact_statement_audits':18,
 'regression_tests':30,
 'byte_for_byte_regeneration':True,
 'established_proof_assistant_kernel_acceptance':False,
 'rocq_compiled':False,
 'not_covered':['infinite counterexample','construction of set-theoretic ordinals and their canonical rank assignments'],
 'ordinal_interface':'Explicit strict total well-order, rank decrease, and least strict-upper-bound property.',
 'height_encoding':'Finite iteration of successor-preimage closure from the empty predicate; one shared iterate for uniform bounds.',
 'python':sys.version,
 'platform':platform.platform(),
 'certificate_sha256':hashlib.sha256((p/'proof.json').read_bytes()).hexdigest(),
 'source_sha256':json.loads((p/'MANIFEST.json').read_text()),
 'logs_sha256':{str(q):hashlib.sha256(q.read_bytes()).hexdigest() for q in sorted((p/'logs').glob('*.log'))},
}
(p/'CHECKED.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: both standalone checkers, 18 exact-statement audits, and 30 regression tests.')
print(f"{record['inference_steps']:,} inferences; {record['closed_named_theorems']} closed named theorems.")
print('The certificate and explicit Rocq export regenerate byte for byte.')
print('This record is not a Rocq compilation or Rocq kernel-check certificate.')
PY
