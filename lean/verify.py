#!/usr/bin/env python3
"""Build this release and cold-check its declared theorem endpoints."""
from pathlib import Path
import datetime, hashlib, json, os, re, shutil, subprocess, sys, time
root=Path(__file__).resolve().parent
projects=json.loads((root/'projects.json').read_text())
coverage=json.loads((root/'coverage.json').read_text())
permitted={'propext','Classical.choice','Quot.sound'}
allowed_audit_options={
 '-DautoImplicit=false', '-DmaxSynthPendingDepth=3',
 '-Dbackward.isDefEq.respectTransparency.types=false',
 '-DsynthInstance.maxHeartbeats=400000', '-DmaxHeartbeats=16000000',
 '-DmaxRecDepth=10000',
}
def audit_extra_args(project):
 """Preserve recorded frontend settings without permitting trust or plugin overrides."""
 values=project.get('audit_lean_args',[])
 if not isinstance(values,list) or not all(isinstance(v,str) for v in values):
  raise SystemExit('audit_lean_args must be a list of approved frontend arguments.')
 result=[];seen=set();i=0
 while i<len(values):
  value=values[i]
  if value in seen:raise SystemExit('Duplicate audit frontend argument: '+value)
  seen.add(value)
  if value=='-R':
   if i+1>=len(values) or values[i+1]!='Source':
    raise SystemExit('Only the project-local Source root is supported for audits.')
   result.extend(['-R','Source']);i+=2
  elif value in allowed_audit_options:
   result.append(value);i+=1
  else:raise SystemExit('Unapproved audit frontend argument: '+value)
 return result
lake=shutil.which('lake')
if not lake:raise SystemExit('lake is not on PATH; install elan and the pinned Lean toolchain first.')
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
logs=root/'verification'/stamp;logs.mkdir(parents=True)
env=os.environ.copy();env.pop('LEAN_PATH',None)
env['MATHLIB_NO_CACHE_ON_UPDATE']='1';env.setdefault('LEAN_NUM_THREADS','2')
records=[];audited={}
for index,project in enumerate(projects):
 cwd=root/project['directory'];steps=[('build',[lake,'--keep-toolchain','--no-cache','build',project['target']])]
 for j,audit in enumerate(project['audit']):
  source=audit if isinstance(audit,str) else audit['source']
  setup=None if isinstance(audit,str) else audit.get('setup')
  # Lake generates exact module-provider maps when dependencies share namespaces.
  args=[lake,'--keep-toolchain','env','lean']
  if setup:
   setup_path=Path(setup)
   if setup_path.is_absolute() or '..' in setup_path.parts:
    raise SystemExit('Audit setup must be a project-relative generated file: '+setup)
   args.extend(['--setup',setup])
  args.extend(audit_extra_args(project))
  # These fixed options follow frontend settings and cannot be overridden by project metadata.
  args.extend(['-t0','-Ddebug.skipKernelTC=false',source])
  steps.append((f'audit_{j}',args))
 for name,args in steps:
  if '--setup' in args:
   setup_path=cwd/args[args.index('--setup')+1]
   setup_data=json.loads(setup_path.read_text())
   expected_options=project.get('expected_setup_options',{})
   if expected_options not in ({},{'autoImplicit':False,'maxSynthPendingDepth':3}):
    raise SystemExit('Unsupported declared elaboration options: '+repr(expected_options))
   if setup_data.get('options') != expected_options:
    raise SystemExit('Audit setup contains unexpected Lean options: '+str(setup_path))
  rel=f'{index:02d}_{name}.log';start=time.monotonic()
  with (logs/rel).open('w') as out:result=subprocess.run(args,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT)
  data=(logs/rel).read_bytes();text=data.decode(errors='replace')
  records.append({'project':project['directory'],'stage':name,'command':['lake',*args[1:]],'exit_code':result.returncode,'elapsed_seconds':time.monotonic()-start,'log':rel,'log_sha256':hashlib.sha256(data).hexdigest()})
  (logs/'RESULTS.json').write_text(json.dumps(records,indent=2)+'\n')
  print(project['directory'],name,'exit',result.returncode,flush=True)
  if result.returncode:raise SystemExit(result.returncode)
  if name.startswith('audit'):
   for theorem in re.findall(r"'([^']+)' does not depend on any axioms",text):
    audited[theorem]=[]
   for theorem,axes in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text):
    axioms={re.sub(r'\.\{[^}]*\}','',a.strip()) for a in axes.split(',') if a.strip()}
    if not axioms<=permitted:raise SystemExit('Unexpected axiom closure: '+theorem+' '+repr(axioms))
    audited[theorem]=sorted(axioms)
missing=[]
for e in coverage['statements']:
 if e['lean_status']=='verified':
  missing.extend(n for n in e['declarations'] if n not in audited)
if missing:raise SystemExit('Missing axiom outputs: '+', '.join(missing))
report={'status':'PASS','verified_numbered_statements':coverage['fully_formalized_numbered_statements'],'total_numbered_statements':coverage['numbered_statements'],'audited_declarations':audited,'permitted_axioms':sorted(permitted),'full_paper_formalization':False}
(logs/'AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: all declared release endpoints built and cold-kernel checked.',flush=True)
