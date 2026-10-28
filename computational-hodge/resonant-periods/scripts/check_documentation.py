#!/usr/bin/env python3
"""Check retained computational-path and Hodge docstrings against both entrypoints."""
from pathlib import Path
import hashlib,json,re,subprocess,tempfile
if not __debug__:
    raise RuntimeError('This checker must run without Python optimization')

root=Path(__file__).resolve().parents[1]
source=(root/'Challenge.lean').read_text()
assert (root/'Solution.lean').read_text()==source
rows=[]
for match in re.finditer(r'(?m)^/--(?:(?!/\-).)*?-/\n',source,re.S):
    stack=[]
    for line in source[:match.start()].splitlines():
        if line.startswith(('namespace ','section ')):
            kind,name=line.split()[:2];stack.append((kind,name))
        elif line.startswith('end '):
            assert stack and stack[-1][1]==line.split()[1];stack.pop()
    names=[name for kind,name in stack if kind=='namespace']
    if not names or not '.'.join(names).startswith(('ComputationalHodge','ComputationalPaths')):continue
    declaration=re.match(r'(?:noncomputable )?(?:theorem|def|abbrev|instance|structure|inductive) ([A-Za-z_][A-Za-z_0-9]*)',source[match.end():])
    assert declaration,match.group()
    doc=match.group();rows.append(('.'.join(names+[declaration[1]]),doc[3:doc.rfind('-/')].strip()))
assert len(rows)==23 and len({name for name,_ in rows})==23
pairs=',\n'.join('(`'+name+','+json.dumps(prose,ensure_ascii=False)+')' for name,prose in rows)
code='''module
import Lean
open Lean
public def main : IO Unit := do
 initSearchPath (← findSysroot)
 for mod in #[`Challenge,`Solution] do
  let env ← importModules #[{module := mod, importAll := true}] {}
  for (n, expected) in #[PAIRS] do
   let some actual ← findSimpleDocString? env n | throw (IO.userError s!"missing docstring {mod}:{n}")
   unless actual.trimAscii.toString == expected do
    throw (IO.userError s!"docstring changed {mod}:{n}: {actual}")
   IO.println s!"DOC_ASSOCIATION {mod}:{n} PASS"
'''.replace('PAIRS',pairs)
with tempfile.TemporaryDirectory(prefix='arclength-docs-') as tmp:
    p=Path(tmp)/'DocAudit.lean';p.write_text(code)
    proc=subprocess.run(['lake','--no-cache','env','lean','--run',str(p)],cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    assert proc.returncode==0,proc.stdout
    assert proc.stdout.count('DOC_ASSOCIATION ')==2*len(rows),proc.stdout
print(json.dumps({'status':'pass','challenge_sha256':hashlib.sha256(source.encode()).hexdigest(),
                  'declarations':len(rows),'entrypoint_associations':2*len(rows),
                  'scope':'Exact docstring association in separately imported Challenge and Solution environments.'}))
