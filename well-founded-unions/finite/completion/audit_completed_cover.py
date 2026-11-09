#!/usr/bin/env python3
"""Validate complete case coverage and saved UNSAT outcomes, not Z3 proofs."""
from pathlib import Path
from itertools import product
from collections import Counter
import hashlib,importlib.util,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent/'computation'

def rows(name,header=False):
 rs=[r.split('\t') for r in (ROOT/name).read_text().splitlines() if r.strip()]
 return rs[1:] if header else rs

def expected(n):
 out=set()
 for L in range(2,n):
  pats=['DC'+''.join(t) for t in product('CD',repeat=L-2)] if L<=n//2 else ['DC'+'X'*(L-2)]
  for p in pats:
   for s0 in range(L,n):
    for s1 in range(L,s0+1):out.add((p,s0,s1))
 return out

root={}
for r in rows('n10_strong_results_results.tsv'):
 key=(r[0],int(r[1]),int(r[2]));assert key not in root
 root[key]=r[3];assert r[3]!='unsat' or r[-1]=='0'
for r in rows('remaining_strong_results_results.tsv'):
 if r[0]!='10':continue
 key=(r[1],int(r[2]),int(r[3]));assert key not in root
 root[key]=r[4];assert r[4]!='unsat' or r[-1]=='0'
assert set(root)==expected(10)
assert set(root.values())<={'unsat','unknown'}
refine={}
for r in rows('l2_refine1_results.tsv'):
 key=tuple([int(r[i]) for i in range(4)]+[r[4]])
 assert key not in refine;refine[key]=r[5]
 assert r[5]!='unsat' or r[-1]=='0'
needed=set()
for (p,s0,s1),status in root.items():
 if status=='unsat':continue
 assert p=='DC'
 for v in range(s0,10):
  for a in range(v):
   for h in ['F','Bplus']:needed.add((s0,s1,v,a,h))
assert set(refine)==needed
residual={}
for r in rows('bv_residual20_results.tsv',True):
 key=(5,5,int(r[0]),int(r[1]),r[2])
 assert key not in residual;residual[key]=r[3]
 assert r[3]!='unsat' or r[-1]=='0'
assert set(residual)=={k for k,v in refine.items() if v!='unsat'}
assert set(residual.values())<={'unsat','unknown'}
pending={k for k,v in residual.items() if v!='unsat'}
assert pending=={(5,5,7,3,'F'),(5,5,8,4,'F')}

path=ROOT/'quad_work_search_quad_bv_strong.py'
spec=importlib.util.spec_from_file_location('archived_bv',path)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
completed=[]
for s0,s1,v,a,h in sorted(pending):
 d=HERE/'runs'/f'v{v}_a{a}_baseline'
 meta=json.loads((d/'metadata.json').read_text());result=json.loads((d/'result.json').read_text())
 assert meta['branch']=={'n':10,'s0':s0,'s1':s1,'pattern':'DC','witness':v,'aescape':a,'h1':h}
 o=meta['options']
 assert o['tactic']=='solver' and o['seed']==0 and o['timeout_ms']==300000
 assert all(o[k] is None for k in ['mask','first','first_color','last','last_color'])
 assert o.get('strengthen','none')=='none'
 rebuilt=m.build(10,s0,s1,v,h,a,300000,0,'solver')
 saved=(d/'input.smt2').read_bytes()
 assert saved==rebuilt.encode()
 digest=hashlib.sha256(saved).hexdigest()
 assert digest==meta['input_sha256']==result['input_sha256']
 assert hashlib.sha256(path.read_bytes()).hexdigest()==meta['generator_sha256']
 assert result['result']=='unsat' and (d/'solver_output.txt').read_text().strip()=='unsat'
 completed.append({'branch':[v,a,h],'result':'unsat','elapsed_seconds':result['elapsed_seconds'],
                   'z3_version':meta['z3_version'],'input_sha256':digest})

report={'result':'COMPLETE_UNSAT_COVER','n':10,'root_cases':len(root),
 'root_unsat':sum(v=='unsat' for v in root.values()),
 'root_cases_refined':sum(v!='unsat' for v in root.values()),
 'refinement_cases':len(refine),'refinement_unsat':sum(v=='unsat' for v in refine.values()),
 'residual_cases':len(residual),'residual_previously_unsat':sum(v=='unsat' for v in residual.values()),
 'completed_branches':completed,'final_leaf_obligations':572,'unresolved':[],
 'scope':'Checks exhaustive case coverage, zero exit codes of archived UNSAT leaves, exact regeneration and hashes of both completed branch inputs, and saved Z3 outputs. It does not independently verify Z3 proof certificates.'}
assert report['final_leaf_obligations']==report['root_unsat']+report['refinement_unsat']+report['residual_previously_unsat']+len(completed)
(HERE/'completed_cover.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
