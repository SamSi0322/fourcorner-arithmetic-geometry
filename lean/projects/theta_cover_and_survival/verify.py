#!/usr/bin/env python3
"""Source-built Lake baseline, explicit immutable batch inputs, every ordinary/cold object equals Lake."""
from pathlib import Path
import concurrent.futures as cf,datetime,hashlib,json,os,shutil,subprocess,threading,time,sys
D=Path(__file__).resolve().parent;lake=shutil.which('lake')
if not lake:raise SystemExit('Install the pinned Lean toolchain and put lake on PATH.')
E=dict(os.environ);E.pop('LEAN_PATH',None);E['MATHLIB_NO_CACHE_ON_UPDATE']='1';E['LEAN_NUM_THREADS']='1';workers=max(1,int(E.get('VERIFY_WORKERS','4')))
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');V=D/'verification'/stamp;V.mkdir(parents=True,exist_ok=False)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,v):
 tmp=Path(str(p)+'.tmp.'+str(threading.get_ident()));tmp.write_text(json.dumps(v,indent=2)+'\n');tmp.replace(p)
t=time.monotonic();p=subprocess.run([lake,'--keep-toolchain','--no-cache','build','ThetaCoverClassPortable'],cwd=D,env=E,text=True,capture_output=True);(V/'lake_build.log').write_text(p.stdout+p.stderr);write(V/'LAKE_BUILD_RECEIPT.json',dict(command=[lake,'--keep-toolchain','--no-cache','build','ThetaCoverClassPortable'],exit_code=p.returncode,seconds=time.monotonic()-t,log_sha256=sha(V/'lake_build.log')))
if p.returncode:raise SystemExit(p.returncode)
T=Path(subprocess.check_output([lake,'env','lean','--print-prefix'],cwd=D,env=E,text=True).strip()).resolve();lean=T/'bin/lean';version=subprocess.check_output([str(lean),'--version'],text=True).strip();assert 'version 4.33.1,'in version,version
mapping=json.loads((D/'MODULE_MAPPING.json').read_text());mods=[r['new_module']for r in mapping]+['ThetaCoverClassPortable'];assert len(set(mods))==len(mods);by={r['new_module']:r for r in mapping}
# All sources and actual Lake setups are fixed for this whole parallel batch. Replays only write V.
input_paths=set();source_setups={};lake_objects={}
for n in mods:
 src=D/'Source'/Path(n.replace('.','/')+'.lean');setup=D/'.lake/build/ir'/Path(n.replace('.','/')+'.setup.json');op=D/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.olean');assert src.is_file()and setup.is_file()and op.is_file();source_setups[n]=(src,setup)
 if n in by:assert sha(src)==by[n]['source_sha256'],n
 input_paths.update([src,setup,op]);parts={}
 for suffix in ['', '.server', '.private']:
  part=Path(str(op)+suffix)
  if part.is_file():input_paths.add(part);parts[suffix]=dict(path=str(part.relative_to(D)),sha256=sha(part),bytes=part.stat().st_size)
 lake_objects[n]=dict(path=str(op.relative_to(D)),sha256=sha(op),all_olean_parts=parts)
root_setup=json.loads(source_setups['ThetaCoverClassPortable'][1].read_text())
for dependency_module,gs in root_setup['importArts'].items():
 for g in gs:
  for a in g:
   q=Path(a);q=q if q.is_absolute()else D/q;assert q.resolve().is_relative_to(D)or q.resolve().is_relative_to(T),('private external input',q);input_paths.add(q)
   if q.name.endswith('.olean') and dependency_module not in by and dependency_module!='ThetaCoverClassPortable':
    if '/.lake/build/lib/lean/'in str(q):
     package_root=Path(str(q).split('/.lake/build/lib/lean/')[0]);source=package_root/Path(dependency_module.replace('.','/')+'.lean')
     if not source.is_file():source=package_root/'Source'/Path(dependency_module.replace('.','/')+'.lean')
     assert source.is_file(),('missing official dependency source',dependency_module,source);input_paths.add(source)
stdlib=[]
for op in sorted((T/'lib/lean').rglob('*.olean')):
 module_path=op.relative_to(T/'lib/lean').with_suffix('.lean');standard_source=T/'src/lean'/module_path
 if not standard_source.is_file():standard_source=T/'src/lean/lake'/module_path
 if standard_source.is_file():input_paths.add(standard_source)
 for q in [op,Path(str(op)+'.server'),Path(str(op)+'.private'),Path(str(op.with_suffix('.ir'))+'.sig'),op.with_suffix('.ir')]:
  if q.is_file():input_paths.add(q);stdlib.append(q)
for q in [D/'lakefile.toml',D/'lake-manifest.json',D/'lean-toolchain',D/'MODULE_MAPPING.json',D/'SOURCE_CONFIGURATION_PORTS.json',Path(__file__).resolve(),lean,T/'bin/lake',Path(lake).resolve(),*sorted((T/'lib/lean').glob('*.dylib'))]:input_paths.add(q)
inputs=[]
for q in sorted(input_paths):inputs.append(dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size))
stdlib_paths={str(p)for p in stdlib}
manifest=V/'BATCH_INPUT_BASELINE.json';write(manifest,dict(schema=1,policy='Exact prelaunch SHA of every source, actual Lake setup/main object, selected root transitive artifact part, pinned toolchain native superset and runtime. No source/setup/dependency writes during replays. All inputs are cryptographically rehashed at batch end.',toolchain=str(T),version=version,source_modules=len(mods),workers=workers,inputs=inputs));manifest_sha=sha(manifest);write(V/'EXPLICIT_STDLIB_BASELINE.json',dict(scope='Every pinned toolchain main olean and every present server/private/IR/signature sibling, a full superset of implicit imports.',artifacts=[x for x in inputs if x['path']in stdlib_paths]));initial={x['path']:x['sha256']for x in inputs};lock=threading.Lock();active={};results=[];failed=threading.Event()
def state():
 with lock:
  write(V/'PROGRESS.json',dict(status='RUNNING',total_modules=len(mods),completed_modules=len(results),failed_modules=sum(not r['passed']for r in results),active_processes=active,baseline_manifest_sha256=manifest_sha,workers=workers))
def job(n):
 if failed.is_set():return None
 src,setup=source_setups[n];assert sha(src)==initial[str(src)]and sha(setup)==initial[str(setup)];r=dict(module=n,source=str(src.relative_to(D)),source_sha256=initial[str(src)],actual_setup=str(setup.relative_to(D)),setup_sha256=initial[str(setup)],batch_inputs=dict(path=manifest.name,sha256=manifest_sha),actual_lake_object=lake_objects[n],checks=[],passed=False);start=time.monotonic()
 for mode in ['ordinary','cold']:
  out=V/'objects'/Path(n.replace('.','/')+'.'+mode+'.olean');out.parent.mkdir(parents=True,exist_ok=True);log=V/'logs'/Path(n.replace('.','/')+'.'+mode+'.log');log.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(lean),'--setup',str(setup),'-Ddebug.skipKernelTC=false','-DautoImplicit=false','-DmaxSynthPendingDepth=3','-Dbackward.isDefEq.respectTransparency.types=false','-DsynthInstance.maxHeartbeats=400000','-DmaxHeartbeats=16000000','-DmaxRecDepth=10000','-R','Source']+(['-t0']if mode=='cold'else[])+['-o',str(out),str(src)]
  t=time.monotonic()
  with log.open('w')as f:
   proc=subprocess.Popen(cmd,cwd=D,env=E,text=True,stdout=f,stderr=subprocess.STDOUT)
   with lock:active[n]=dict(mode=mode,pid=proc.pid,command=cmd,start_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
   state();code=proc.wait()
  txt=log.read_text();check=dict(mode=mode,command=cmd,exit_code=code,seconds=time.monotonic()-t,log=str(log.relative_to(V)),log_sha256=sha(log),output_object=str(out.relative_to(V)),output_sha256=sha(out)if code==0 else None,source_and_setup_posthash_match=sha(src)==initial[str(src)]and sha(setup)==initial[str(setup)])
  if n.endswith('.ActualThetaCoverFullAudit')or n.endswith('.ActualTwoJacobianSurvivalAudit'):
   expected=246 if n.endswith('.ActualTwoJacobianSurvivalAudit')else 51
   import re
   m=re.search(r'(?<!COVER_)AUDIT_DECLARATIONS (\d+)',txt);v=re.search(r'(?<!COVER_)AUDIT_FULL_TYPE_VALUE_CLOSURE (\d+)',txt);check['owned_scope_count']=int(m.group(1))if m else None;check['full_type_value_closure']=int(v.group(1))if v else None
   assert check['owned_scope_count']==expected,(n,txt[-1000:]);assert 'AUDIT_ZERO_UNSAFE_PARTIAL_PLACEHOLDERS true'in txt
   if expected==246:assert 'COVER_AUDIT_DECLARATIONS 51'in txt and 'COVER_AUDIT_ZERO_UNSAFE_PARTIAL_PLACEHOLDERS true'in txt
  check['output_olean_parts']={};check['all_olean_parts_equal_actual_lake']=code==0
  for suffix in ['', '.server', '.private']:
   generated=Path(str(out)+suffix);expected_part=lake_objects[n]['all_olean_parts'].get(suffix)
   if expected_part is None:
    if generated.exists():check['all_olean_parts_equal_actual_lake']=False
   elif not generated.is_file():check['all_olean_parts_equal_actual_lake']=False
   else:
    digest=sha(generated);size=generated.stat().st_size;check['output_olean_parts'][suffix]=dict(path=str(generated.relative_to(V)),sha256=digest,bytes=size)
    if digest!=expected_part['sha256']or size!=expected_part['bytes']:check['all_olean_parts_equal_actual_lake']=False
  r['checks'].append(check)
  if code or not check['source_and_setup_posthash_match']or not check['all_olean_parts_equal_actual_lake']:break
 r['passed']=len(r['checks'])==2 and all(c['exit_code']==0 and c['source_and_setup_posthash_match']and c['output_sha256']==lake_objects[n]['sha256']and c['all_olean_parts_equal_actual_lake']for c in r['checks']);r['seconds']=time.monotonic()-start;receipt=V/'receipts'/Path(n.replace('.','/')+'.json');receipt.parent.mkdir(parents=True,exist_ok=True);write(receipt,r)
 with lock:active.pop(n,None);results.append(r)
 if not r['passed']:failed.set()
 state();print(('PASS 'if r['passed']else'FAIL ')+n+' '+str(round(r['seconds'],2))+'s',flush=True);return r
state()
try:
 with cf.ThreadPoolExecutor(max_workers=workers)as pool:
  futures={pool.submit(job,n):n for n in mods}
  for f in cf.as_completed(futures):
   try:f.result()
   except Exception as e:
    failed.set();n=futures[f];write(V/(n+'.EXCEPTION.json'),dict(module=n,error=repr(e)))
    with lock:active.pop(n,None);results.append(dict(module=n,passed=False,error=repr(e)))
    state();print('ERROR',n,repr(e),flush=True)
except KeyboardInterrupt:failed.set();raise
post=[dict(path=x['path'],expected=x['sha256'],actual=sha(x['path']))for x in inputs if sha(x['path'])!=x['sha256']];write(V/'BATCH_INPUT_POSTHASH.json',dict(status='PASS'if not post else'FAIL',baseline_manifest_sha256=manifest_sha,input_files=len(inputs),mismatches=post));passed=len(results)==len(mods)and not post and all(r['passed']for r in results);summary=dict(status='PASS_ALL_ORDINARY_COLD_EQUAL_ACTUAL_SOURCE_BUILT_LAKE_OBJECTS'if passed else'FAIL_OR_INCOMPLETE',source_modules=len(mods),completed_modules=len(results),identical_ordinary_cold_lake_pairs=sum(r['passed']for r in results),source_bound_batch_input_files=len(inputs),stdlib_native_parts=len(stdlib),baseline_manifest_sha256=manifest_sha,posthash_mismatches=post,workers=workers,numbered_credit=0);write(V/'SUMMARY.json',summary);write(V/'PROGRESS.json',dict(**summary,active_processes=active));print(json.dumps(summary),flush=True);raise SystemExit(0 if passed else 1)
