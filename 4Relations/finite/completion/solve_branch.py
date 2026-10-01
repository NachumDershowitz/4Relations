#!/usr/bin/env python3
"""Run a saved residual branch using the unmodified archived BV generator."""
from pathlib import Path
import argparse, ctypes, importlib.util, hashlib, json, os, platform, time

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('archived_bv',HERE.parent/'computation/quad_work_search_quad_bv_strong.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
p=argparse.ArgumentParser()
p.add_argument('witness',type=int);p.add_argument('aescape',type=int)
p.add_argument('--timeout-ms',type=int,default=300000)
p.add_argument('--seed',type=int,default=0)
p.add_argument('--tactic',choices=['solver','sat','qfbv'],default='solver')
p.add_argument('--mask',type=int)
p.add_argument('--first',type=int)
p.add_argument('--first-color',choices=['B','C','D'])
p.add_argument('--last',type=int)
p.add_argument('--last-color',choices=['B','C','D'])
p.add_argument('--name',required=True)
p.add_argument('--libz3',default=os.environ.get('LIBZ3','/Applications/MATLAB_R2026a.app/bin/maca64/libz3.4.12.2.0.dylib'))
a=p.parse_args()
m.LIBZ3=a.libz3
lib=ctypes.CDLL(a.libz3);lib.Z3_get_full_version.restype=ctypes.c_char_p
version=lib.Z3_get_full_version().decode()
s=m.build(10,5,5,a.witness,'F',a.aescape,a.timeout_ms,a.seed,a.tactic,a.last,a.last_color,a.first,a.first_color,a.mask)
d=HERE/'runs'/a.name;d.mkdir(parents=True,exist_ok=True)
(d/'input.smt2').write_text(s)
meta={'branch':{'n':10,'s0':5,'s1':5,'pattern':'DC','witness':a.witness,'aescape':a.aescape,'h1':'F'},
      'options':vars(a),'z3_version':version,'machine':platform.machine(),
      'input_sha256':hashlib.sha256(s.encode()).hexdigest(),
      'generator_sha256':hashlib.sha256(Path(spec.origin).read_bytes()).hexdigest(),
      'library_sha256':hashlib.sha256(Path(a.libz3).read_bytes()).hexdigest(),
      'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
(d/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({'event':'started','name':a.name,'z3':version,'bytes':len(s),'options':vars(a)}),flush=True)
t=time.monotonic()
out=m.Z3().run(s)
result={'name':a.name,'result':out.strip(),'elapsed_seconds':round(time.monotonic()-t,3),
        'finished_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'input_sha256':meta['input_sha256']}
(d/'solver_output.txt').write_text(out)
(d/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
if out.strip()=='sat':
 (d/'model.txt').write_text(m.Z3().run(s+'\n(get-model)\n'))
