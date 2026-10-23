import pathlib,subprocess,os,json,re,hashlib,time,argparse,tempfile
parser=argparse.ArgumentParser(description='Native protected-copy comparison and kernel replay; not canonical sandbox verification.')
parser.add_argument('--output-dir',type=pathlib.Path)
a=parser.parse_args()
P=pathlib.Path(__file__).resolve().parents[1]
A=(a.output_dir or pathlib.Path(tempfile.mkdtemp(prefix='lavrentieff-native-'))).resolve();A.mkdir(parents=True,exist_ok=True)
T=pathlib.Path(subprocess.check_output(['lean','--print-prefix'],cwd=P,text=True).strip()); env=os.environ.copy();env['PATH']=str(T/'bin')+os.pathsep+env.get('PATH','');cfg=json.loads((P/'comparator.json').read_text())
names=cfg['theorem_names']; legal=cfg['permitted_axioms']
src=(T/'src/lean/lake/Lake/CLI/Check.lean').read_text(); primitive=re.findall(r'(?m)^    ``([\w.]+),?$',src.split('def primitiveTargets')[1].split('def builtinTargets')[0]);assert len(primitive)==26
exports=['Quot','Quot.mk','Quot.lift','Quot.ind']+names+legal+primitive
runs=[]
def run(label,cmd,expected=0):
 if cmd[0]==str(T/'bin/lean'): cmd.insert(1,'--root='+str(A))
 start=time.monotonic()
 with (A/(label+'.log')).open('wb') as f:
  r=subprocess.run(cmd,cwd=P,env=env,stdout=f,stderr=subprocess.STDOUT)
 runs.append(dict(label=label,command=cmd,exit=r.returncode,seconds=round(time.monotonic()-start,3)))
 if expected is not None and r.returncode!=expected: raise RuntimeError((label,r.returncode,(A/(label+'.log')).read_text()[-4000:]))
 return r.returncode
# Establish the package's exact environment without a shell.
r=subprocess.run([str(T/'bin/lake'),'env','printenv','LEAN_PATH'],cwd=P,env=env,capture_output=True,text=True,check=True);env['LEAN_PATH']=str(A)+':'+r.stdout.strip()
proof=(P/'LEChallenge.lean').read_text();(A/'PalomarNativeLavrentieff.lean').write_text(proof)
run('protected-build',[str(T/'bin/lean'),'-DwarningAsError=true','-o',str(A/'PalomarNativeLavrentieff.olean'),str(A/'PalomarNativeLavrentieff.lean')])
def export(label,module):
 with (A/(label+'.ndjson')).open('wb') as out, (A/(label+'-export.log')).open('wb') as err:
  r=subprocess.run([str(T/'bin/leanexport'),module,'--']+exports,cwd=P,env=env,stdout=out,stderr=err)
 assert r.returncode==0,(label,r.returncode,(A/(label+'-export.log')).read_text()[-2000:])
export('challenge','PalomarNativeLavrentieff');export('solution','LESolution')
arr=lambda xs:'#['+','.join(json.dumps(x)+'.toName' for x in xs)+']'
driver='''module
public import Lake.Check.Compare
public import Lake.Check.Axioms
open Lean
@[expose] public section
def main (args : List String) : IO Unit := do
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk args[0]! .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk args[1]! .read)
  let targets : Array Name := TARGETS
  let legal : Array Name := LEGAL
  let primitive : Array Name := PRIMITIVE
  IO.ofExcept <| Lake.Check.compareAt challenge solution (targets ++ legal) #[] primitive
  IO.ofExcept <| Lake.Check.checkAxioms solution targets #[] legal
  IO.println "Native protected comparison and transitive axiom audit passed"
'''.replace('TARGETS',arr(names)).replace('LEGAL',arr(legal)).replace('PRIMITIVE',arr(primitive))
(A/'CompareNative.lean').write_text(driver)
run('compare-driver-C',[str(T/'bin/lean'),'-c',str(A/'CompareNative.c'),str(A/'CompareNative.lean')])
run('compare-driver-link',[str(T/'bin/leanc'),'-o',str(A/'CompareNative'),str(A/'CompareNative.c'),'-lLake','-lLeanExport'])
run('compare',[str(A/'CompareNative'),str(A/'challenge.ndjson'),str(A/'solution.ndjson')])
for label,old,new,constant in [
 ('changed-small-oscillation','  ⋃ (U : Set X) (_ : IsOpen U)\n    (_ : ∀ a ∈ U ∩ s, ∀ b ∈ U ∩ s, dist (f a) (f b) < ε), U','  id (⋃ (U : Set X) (_ : IsOpen U)\n    (_ : ∀ a ∈ U ∩ s, ∀ b ∈ U ∩ s, dist (f a) (f b) < ε), U)','smallOscillation'),
 ('changed-extension-domain','  closure s ∩ ⋂ n : ℕ, smallOscillation s f ((n + 1 : ℝ)⁻¹)','  id (closure s ∩ ⋂ n : ℕ, smallOscillation s f ((n + 1 : ℝ)⁻¹))','extensionDomain')]:
 assert old in proof
 mod='Negative'+label.title().replace('-','')
 variant=proof.replace(old,new,1)
 if label=='changed-small-oscillation': variant=variant.replace('simp only [smallOscillation, mem_iUnion]', 'simp only [smallOscillation, id_eq, mem_iUnion]')
 (A/(mod+'.lean')).write_text(variant)
 run(label+'-build',[str(T/'bin/lean'),'-DwarningAsError=true','-o',str(A/(mod+'.olean')),str(A/(mod+'.lean'))])
 export(label,mod)
 rc=run(label+'-compare',[str(A/'CompareNative'),str(A/'challenge.ndjson'),str(A/(label+'.ndjson'))],expected=None)
 log=(A/(label+'-compare.log')).read_text();assert rc!=0 and 'does not match' in log and constant in log,(label,rc,log)
# Kernel replays consume only the selected proof closure, never compiled candidate plugins.
run('lean-kernel',[str(T/'bin/leanchecker'),'--silent','--from-export',str(A/'solution.ndjson')])
nanoda=dict(export_file_path=str(A/'solution.ndjson'),use_stdin=False,permitted_axioms=legal,unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True)
(A/'nanoda.json').write_text(json.dumps(nanoda,indent=2)+'\n')
run('nanoda',[str(T/'bin/nanoda_bin'),str(A/'nanoda.json')])
run('con-ron',[str(T/'bin/con-ron'),'--verified','--jobs=2',str(A/'solution.ndjson')])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
summary=dict(status='pass',scope='Native protected-copy comparison and independent kernel replays; not canonical sandbox/resource-profile verification',selected_theorems=names,permitted_axioms=legal,primitive_targets=primitive,source_sha256=sha(P/'LEChallenge.lean'),proof_sha256=sha(P/'Lavrentieff.lean'),comparator_sha256=sha(P/'comparator.json'),source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),runs=runs,files={f.name:dict(sha256=sha(f),size=f.stat().st_size) for f in A.iterdir() if f.is_file()},toolchain=str(T),tool_binary_sha256={n:sha(T/'bin'/n) for n in ['lean','lake','leanexport','leanchecker','nanoda_bin','con-ron']},canonical_workflows_run=0,registry_intakes=0)
(A/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
