"""Rebuild every packaged nonstandard Lean module, using only a compatible standard cache.

No prior custom olean is accepted. No downloads or external services are used.
"""
from pathlib import Path
import argparse,json,hashlib,subprocess,os,time,concurrent.futures,sys,re
ap=argparse.ArgumentParser()
ap.add_argument('--lean',default='lean')
ap.add_argument('--standard-cache',required=True,type=Path)
ap.add_argument('--evidence-out',required=True,type=Path)
ap.add_argument('--jobs',type=int,choices=[1,2],default=2)
a=ap.parse_args();P=Path(__file__).resolve().parent;S=P/'Source';B=P/'.lake/build/lib/lean';E=a.evidence_out.resolve();E.mkdir(parents=True,exist_ok=True);B.mkdir(parents=True,exist_ok=True)
manifest=json.loads((P/'SOURCE_MANIFEST.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allowed_axioms={'propext','Classical.choice','Quot.sound'}
def checked_axioms(output):
 matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output)
 if not matches:raise RuntimeError('Cold check produced no axiom audit.')
 audits={name:sorted(a.strip() for a in axes.split(',') if a.strip()) for name,axes in matches}
 for name,axes in audits.items():
  if not set(axes)<=allowed_axioms:raise RuntimeError('Unexpected axiom dependency: '+name+' '+repr(axes))
 required='FourCorner.OppositeProjective.ExactGenus.prop_ell_opposite_genus'
 if required not in audits:raise RuntimeError('Main theorem is missing from the axiom audit.')
 return audits
version=subprocess.check_output([a.lean,'--version'],text=True).strip()
if '4.33.1' not in version:raise SystemExit('This package requires Lean 4.33.1.')
standard={'Init','Lean','Std','Lake','Mathlib','Batteries','Aesop','Qq','Plausible','ProofWidgets','ImportGraph','LeanSearchClient'}
for p in a.standard_cache.rglob('*.olean'):
 if p.relative_to(a.standard_cache).parts[0].removesuffix('.olean') not in standard:raise SystemExit('Custom artifact found in standard cache: '+str(p))
def strip_comments(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;i+=2;continue
  if depth and s.startswith('-/',i):depth-=1;i+=2;continue
  if depth:
   if s[i]=='\n':out.append('\n')
   i+=1;continue
  if s.startswith('--',i):
   k=s.find('\n',i);i=len(s) if k<0 else k;continue
  out.append(s[i]);i+=1
 return ''.join(out)
graph={}
for m,r in manifest.items():
 p=P/r['path']
 if sha(p)!=r['sha256']:raise SystemExit('Source hash mismatch: '+m)
 imports=[]
 for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)',strip_comments(p.read_text()),re.M):imports.extend(line.split())
 graph[m]={i for i in imports if i in manifest}
 for i in imports:
  if i not in manifest and i.split('.')[0] not in standard:raise SystemExit('Missing nonstandard source: '+i)
# Each run begins with no pre-existing packaged custom objects.
for m in manifest:
 q=B/Path(*m.split('.')).with_suffix('.olean')
 for suffix in ['','.server','.private']:
  z=Path(str(q)+suffix)
  if z.exists() or z.is_symlink():z.unlink()
env=dict(os.environ,LEAN_PATH=str(B)+':'+str(a.standard_cache.resolve()),LEAN_NUM_THREADS='1')
(E/'ENVIRONMENT.json').write_text(json.dumps({'lean_version':version,'LEAN_PATH':env['LEAN_PATH'],'standard_cache':str(a.standard_cache.resolve()),'jobs':a.jobs,'custom_sources':len(manifest),'reused_nonstandard_artifacts':0},indent=2))
def run(m,cold=False):
 r=manifest[m];p=P/r['path'];o=B/Path(*m.split('.')).with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True)
 cmd=[a.lean,*r['compile_options'],'-R',str(S)]
 cmd+=['-t0'] if cold else ['-o',str(o)]
 cmd.append(str(p));t=time.monotonic();z=subprocess.run(cmd,env=env,capture_output=True,text=True)
 rec={'module':m,'mode':'cold' if cold else 'ordinary','source_sha256':r['sha256'],'command':cmd,'exit_code':z.returncode,'stdout':z.stdout,'stderr':z.stderr,'elapsed_seconds':time.monotonic()-t}
 if not cold and o.exists():rec['olean_sha256']=sha(o)
 if cold and z.returncode==0:rec['checked_axioms']=checked_axioms(z.stdout)
 name=m+('.cold' if cold else '.ordinary')+'.json';(E/name).write_text(json.dumps(rec,indent=2))
 if z.returncode or 'declaration uses `sorry`' in z.stdout or 'sorryAx' in z.stdout:raise RuntimeError('Failed '+m+'; inspect '+name)
 return rec
done=set();pending=set(manifest);active={};records=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
 while pending or active:
  for m in sorted(pending):
   if len(active)>=a.jobs:break
   if graph[m]<=done:
    active[pool.submit(run,m)]=m;pending.remove(m)
  if not active:raise SystemExit('Cyclic or unresolved custom source imports: '+str(sorted(pending)))
  fs,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
  for f in fs:
   m=active.pop(f)
   try:r=f.result()
   except Exception as ex:
    (E/'FAILED.json').write_text(json.dumps({'module':m,'error':str(ex),'completed':len(done)},indent=2));print(str(ex),flush=True);sys.exit(1)
   done.add(m);records.append(r)
   (E/'PROGRESS.json').write_text(json.dumps({'completed':len(done),'total':len(manifest),'active':list(active.values()),'last':m},indent=2))
   print(str(len(done))+'/'+str(len(manifest))+' '+m+' '+str(round(r['elapsed_seconds'],2))+'s',flush=True)
for m in ['OppositeProjectiveGenusFive','OppositeGenus']:records.append(run(m,True))
summary={'status':'COMPLETE','custom_sources_rebuilt':len(done),'ordinary_exit_codes_all_zero':True,'cold_targets':['OppositeProjectiveGenusFive','OppositeGenus'],'cold_exit_codes_all_zero':True,'allowed_axioms':sorted(allowed_axioms),'axiom_outputs_verified':True,'source_manifest_sha256':sha(P/'SOURCE_MANIFEST.json'),'reused_nonstandard_artifacts':0,'total_compile_seconds':sum(x['elapsed_seconds'] for x in records)}
(E/'FULL_REBUILD_ACCEPTANCE.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary),flush=True)
