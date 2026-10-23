from pathlib import Path
import re,textwrap,json,hashlib,subprocess,tempfile,argparse
p=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description="Regenerate the proof-complete Mathlib-only Challenge; this is not protected verification.")
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
files={f.stem:f for f in p.glob('*.lean') if f.stem not in {'AxiomAudit','HodgeChallenge','HodgeSolution','HodgeChallengeTests','HodgeSolutionTests'}}
order=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 for n in re.findall(r'^(?:public )?import (\S+)',files[m].read_text(),re.M):
  if n in files:visit(n)
 order.append(m)
visit('ReleaseFidelity')
config=json.loads((p/'comparator.json').read_text())
subprocess.run(['lake','build','ReleaseFidelity'],cwd=p,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
seeds=config['theorem_names']+config['definition_names']
scan='module\n'+''.join('import all '+m+'\n'for m in order)+"open Lean Elab Command\nrun_cmd do\n let env ← getEnv\n let mut pending := #["+', '.join('`'+n for n in seeds)+"]\n let mut seen : NameSet := {}\n while !pending.isEmpty do\n  let n := pending.back!\n  pending := pending.pop\n  if seen.contains n then continue\n  seen := seen.insert n\n  if let some ci := env.find? n then\n   logInfo m!\"PILOT_DEP {n}\"\n   for e in #[ci.type] ++ (ci.value? true).toArray do\n    for c in e.getUsedConstants do\n     if c.toString.startsWith \"AlgebraicHodgePilot\" then pending := pending.push c\n"
with tempfile.TemporaryDirectory(prefix='hodge-source-scan-')as tmp:
 probe=Path(tmp)/'SourceScan.lean';probe.write_text(scan)
 result=subprocess.run(['lake','env','lean',str(probe)],cwd=p,check=True,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
used=set(re.findall(r'PILOT_DEP (\S+)',result.stdout))
header='''module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# Algebraic column E1 degeneration and bounded abutment
This proof-complete statement surface uses actual bicomplex operators, filtered
quotients and total cohomology. The hypothesis is a componentwise image/kernel
identity. It is conditional algebraic mathematics, without analytic Kähler claims.
Definitions are literal and all selected proofs are supplied. Generated from the
modular development by dependency selection and declaration-header reflow;
verification/challenge-source-map.json records the retained source declarations.
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits
'''
out=[header];mapping=[]
for m in order:
 f=files[m];raw=f.read_text();clean=re.sub(r'/\-.*?\-/','',raw,flags=re.S);clean=re.sub(r'(?m)^\s*--.*$','',clean)
 for block in re.finditer(r'(?ms)^namespace (\S+)\n(.*?)^end \1\s*$',clean):
  ns,body=block[1],block[2]
  matches=list(re.finditer(r'(?m)^(?:@\[[^\n]*\]\n)*(?:(?:noncomputable|protected) )?(def|abbrev|theorem|structure) (\S+)',body))
  kept=[]
  for i,d in enumerate(matches):
   name=ns+'.'+d[2]
   if name not in used:continue
   decl=body[d.start():matches[i+1].start()if i+1<len(matches)else len(body)].strip('\n')
   # Only statement headers are reflowed; proof layout and commands remain intact.
   if ':=' in decl and 'where' not in decl.split(':=',1)[0]:
    pre,post=decl.split(':=',1)
    attrs=[]
    while pre.startswith('@['):
     attr,pre=pre.split('\n',1);attrs.append(attr)
    pre=' '.join(pre.split())
    pre='\n'.join(textwrap.wrap(pre,width=240,subsequent_indent='    ',break_long_words=False,break_on_hyphens=False))
    decl=('\n'.join(attrs)+'\n'if attrs else'')+pre+' :='+post
   decl='\n'.join(l for l in decl.splitlines()if l.strip())
   kept.append(decl)
   mapping.append({'declaration':name,'modular_file':f.name,'modular_file_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'standalone_declaration_sha256':hashlib.sha256(decl.encode()).hexdigest()})
  if kept:
   pre=body[:matches[0].start()];pre='\n'.join(l for l in pre.splitlines()if l.strip())
   out.append('namespace '+ns+'\n'+(pre+'\n'if pre else'')+'\n'.join(kept)+'\nend '+ns+'\n')
s=''.join(out)
for ns in ['AlgebraicHodgePilot.Column']:
 var='variable {k : Type} [Field k] (K : Bicomplex k)'
 s=s.replace('end '+ns+'\nnamespace '+ns+'\n'+var+'\n','')
data={'status':'generated-source-map; compilation and review are certified separately','method':'Exact local constant closure collected with import all; only explicitly used source declarations retained. Comments/blank lines removed; declaration headers reflowed to width240, and adjacent identical Column contexts merged. No mathematical proof commands or contracts changed.','retained_declarations':mapping,'challenge_sha256':hashlib.sha256(s.encode()).hexdigest(),'physical_lines':len(s.splitlines()),'bytes':len(s.encode())}
assert len(s.splitlines())<=1000 and len(s.encode())<=100*1024
if args.check:
 assert (p/'HodgeChallenge.lean').read_text()==s,'Challenge regeneration differs'
 assert (p/'HodgeSolution.lean').read_text()==s,'Solution regeneration differs'
 assert json.loads((p/'verification/challenge-source-map.json').read_text())==data,'Source map regeneration differs'
else:
 (p/'HodgeChallenge.lean').write_text(s)
 (p/'HodgeSolution.lean').write_text(s)
 (p/'verification/challenge-source-map.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'status':'pass','mode':'check'if args.check else'generate','lines':data['physical_lines'],'bytes':data['bytes'],'declarations':len(mapping)}))
