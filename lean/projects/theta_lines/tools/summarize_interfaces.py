"""Summarize the structural expression DAG emitted by ExportInterfaces.lean.
Run after a successful build: lake env lean tools/ExportInterfaces.lean > interfaces.log
Then: python3 tools/summarize_interfaces.py interfaces.log
"""
from pathlib import Path
import json,hashlib,sys
j=next(json.loads(l.split('COMPACT_INTERFACES ',1)[1])for l in Path(sys.argv[1]).open()if 'COMPACT_INTERFACES 'in l)
hashes=[]
for node in j['nodes']:
 x=list(node)
 for i in {'app':[1,2],'lam':[1,2],'forall':[1,2],'let':[1,2,3],'proj':[3]}.get(x[0],[]):
  assert x[i]<len(hashes)
  x[i]=hashes[x[i]]
 hashes.append(hashlib.sha256(json.dumps(x,separators=(',',':'),ensure_ascii=False).encode()).hexdigest())
pins={r['declaration']:dict(declaration=r['declaration'],level_parameters=r['level_parameters'],type_sha256=hashes[r['type']],definition_value_sha256=hashes[r['value']]if r['value']is not None else None)for r in j['entries']}
print(json.dumps(dict(declarations=len(pins),nodes=len(hashes),endpoint=pins['FourCorner.ThetaLinesFullAssembly.theta_lines_full']),indent=2))
