#!/usr/bin/env python3
"""Build this portable package and replay every custom source ordinarily/cold."""
from pathlib import Path
import json,hashlib,os,shutil,subprocess,time,datetime,re
D=Path(__file__).resolve().parent;lake=shutil.which('lake')
if not lake:raise SystemExit('Install the pinned Lean toolchain and put lake on PATH.')
E=dict(os.environ);E.pop('LEAN_PATH',None);E['MATHLIB_NO_CACHE_ON_UPDATE']='1';E.setdefault('LEAN_NUM_THREADS','2')
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');V=D/'verification'/stamp;V.mkdir(parents=True);sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();records=[]
def call(args,name,inputs=None):
 t=time.monotonic();p=subprocess.run(args,cwd=D,env=E,text=True,capture_output=True);(V/(name+'.log')).write_text(p.stdout+p.stderr)
 ip=None
 if inputs is not None:
  ip=V/(name+'.inputs.json');ip.write_text(json.dumps(inputs,indent=2)+'\n')
 r=dict(stage=name,command=args,exit_code=p.returncode,seconds=time.monotonic()-t,log=name+'.log',log_sha256=sha(V/(name+'.log')),inputs_manifest=None if ip is None else dict(path=ip.name,sha256=sha(ip)),implicit_stdlib_baseline=globals().get('stdlib_baseline_pin'))
 records.append(r);(V/'RESULTS.json').write_text(json.dumps(records,indent=2)+'\n');print(name,'exit',p.returncode,flush=True)
 if p.returncode:raise SystemExit(p.returncode)
 return p.stdout
call([lake,'--keep-toolchain','--no-cache','build','ThetaLocalSurvivalPortable','ThetaLocalSurvivalPortable.Audit'],'lake_build')
mods=[r['new_module']for r in json.loads((D/'MODULE_MAPPING.json').read_text())]+['ThetaLocalSurvivalPortable.Audit','ThetaLocalSurvivalPortable'];pairs=[]
T=Path(subprocess.check_output([lake,'env','lean','--print-prefix'],cwd=D,env=E,text=True).strip()).resolve()
stdlib_files=[]
for op in sorted((T/'lib/lean').rglob('*.olean')):
 for p in [op,Path(str(op)+'.server'),Path(str(op)+'.private'),op.with_suffix('.ir'),Path(str(op.with_suffix('.ir'))+'.sig')]:
  if p.is_file():stdlib_files.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
baseline=V/'IMPLICIT_STDLIB_BASELINE.json'
baseline.write_text(json.dumps(dict(schema=1,status='PRELAUNCH_HASHED_FULL_PINNED_TOOLCHAIN_NATIVE_SUPERSET',toolchain_prefix=str(T),scope='Every toolchain .olean plus all present server/private/IR/signature siblings; includes all implicit stdlib imports',artifacts=stdlib_files),indent=2)+'\n')
stdlib_baseline_pin=dict(path=baseline.name,sha256=sha(baseline))
for n in mods:
 src=D/'Source'/(n.replace('.','/')+'.lean');setup=D/'.lake/build/ir'/(n.replace('.','/')+'.setup.json');j=json.loads(setup.read_text());inputs={str(src.relative_to(D)):sha(src),str(setup.relative_to(D)):sha(setup),str(baseline.relative_to(D)):sha(baseline)}
 for gs in j['importArts'].values():
  for g in gs:
   for a in g:
    p=Path(a);p=p if p.is_absolute()else D/p
    assert p.resolve().is_relative_to(D)or p.resolve().is_relative_to(T),('private external artifact',p)
    inputs[str(p)]=sha(p)
 runtime=[T/'bin/lean',T/'bin/lake',Path(lake).resolve(),*sorted((T/'lib/lean').glob('*.dylib'))]
 for p in runtime:inputs[str(p)]=sha(p)
 lake_object=D/'.lake/build/lib/lean'/(n.replace('.','/')+'.olean');lake_hash=sha(lake_object)
 hashes=[]
 for mode in ['ordinary','cold']:
  out=V/(n+'.'+mode+'.olean');args=[lake,'--keep-toolchain','env','lean','--setup',str(setup.relative_to(D)),'-Ddebug.skipKernelTC=false','-DautoImplicit=false','-DmaxSynthPendingDepth=3','-Dbackward.isDefEq.respectTransparency=false','-Dbackward.isDefEq.respectTransparency.types=false','-DmaxHeartbeats=16000000','-R','Source']
  if mode=='cold':args+=['-t0']
  args+=['-o',str(out.relative_to(D)),str(src)];text=call(args,n+'.'+mode,inputs)
  assert all(sha(D/p if not Path(p).is_absolute()else p)==h for p,h in inputs.items()),'input changed during replay'
  hashes.append(sha(out))
  records[-1]['object_sha256']=hashes[-1];records[-1]['all_posthashes_match']=True
  if n.endswith('.Audit'):
   assert 'AUDIT_DECLARATIONS 'in text and 'AUDIT_FULL_TYPE_VALUE_CLOSURE 'in text
   for axes in re.findall(r'AUDIT_AXIOMS \S+ \[([^]]*)\]',text):assert {x.strip()for x in axes.split(',')if x.strip()}<={'propext','Classical.choice','Quot.sound'}
 assert hashes[0]==hashes[1],('ordinary/cold output mismatch',n)
 assert hashes[0]==lake_hash,('replay differs from actual Lake-produced object',n,lake_hash,hashes)
 pairs.append(dict(module=n,source_sha256=sha(src),object_sha256=hashes[0],lake_produced_object=str(lake_object.relative_to(D)),lake_produced_object_sha256=lake_hash,replays_equal_lake_object=True,setup_options=j.get('options')))
assert all(sha(a['path'])==a['sha256'] for a in stdlib_files),'implicit stdlib changed during entire replay batch'
(V/'IMPLICIT_STDLIB_POSTCHECK.json').write_text(json.dumps(dict(status='PASS_ALL_BATCH_POSTHASHES_MATCH',baseline=stdlib_baseline_pin,artifact_parts=len(stdlib_files)),indent=2)+'\n')
(V/'RESULTS.json').write_text(json.dumps(records,indent=2)+'\n');(V/'OBJECT_PAIRS.json').write_text(json.dumps(pairs,indent=2)+'\n');print('PASS',len(pairs),'ordinary/cold source pairs; actual dependencies built by Lake from this package.',flush=True)
