"""Sequential native exact-pin checks, reusing dependencies read-only; not canonical CI."""
import argparse,hashlib,json,os,pathlib,re,shutil,subprocess,time
PKG=pathlib.Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--work-dir',type=pathlib.Path,required=True)
parser.add_argument('--dependency-root',type=pathlib.Path,default=PKG/'.lake/packages')
args=parser.parse_args()
pkg=PKG
out=args.work_dir.resolve()
out.mkdir(parents=True,exist_ok=False)
alias=out/'BaireProtected'
alias.mkdir()
prefix=pathlib.Path(subprocess.check_output(['lean','--print-prefix'],cwd=PKG,text=True).strip())
version=subprocess.check_output([str(prefix/'bin/lean'),'--version'],text=True)
assert '4.35.0-rc2' in version and '11acb17ec6b07a8f9e9173e6845197929540936b' in version
lock=json.loads((PKG/'lake-manifest.json').read_text())
for dep in lock['packages']:
 actual=subprocess.check_output(['git','-C',str(args.dependency_root/dep['name']),'rev-parse','HEAD'],text=True).strip()
 assert actual==dep['rev'],(dep['name'],actual,dep['rev'])
deps=sorted(args.dependency_root.iterdir())
env=os.environ.copy()
env.update(PATH=str(prefix/'bin')+':/usr/bin:/bin',LEAN_NUM_THREADS='1')
dep_paths=[str(prefix/'lib/lean')]+[str(p/'.lake/build/lib/lean') for p in deps]
protected=env|dict(LEAN_PATH=':'.join([str(out)]+dep_paths))
candidate=env|dict(LEAN_PATH=':'.join([str(pkg)]+dep_paths))
cfg=json.loads((pkg/'comparator.json').read_text())
cli=(prefix/'src/lean/lake/Lake/CLI/Check.lean').read_text()
primitive=re.findall(r'^    ``([\w.]+),?$',cli.split('def primitiveTargets',1)[1].split('def builtinTargets',1)[0],re.M)
assert len(primitive)==26
targets=['Quot','Quot.mk','Quot.lift','Quot.ind']+cfg['theorem_names']+cfg['permitted_axioms']+primitive
records=[]
def run(name,argv,runenv,export=None):
 t=time.monotonic()
 with (out/(name+'.log')).open('w') as log:
  if export:
   with export.open('w') as f:p=subprocess.run(list(map(str,argv)),cwd=out,env=runenv,stdout=f,stderr=log)
  else:p=subprocess.run(list(map(str,argv)),cwd=out,env=runenv,stdout=log,stderr=subprocess.STDOUT)
 records.append(dict(name=name,exit_code=p.returncode,seconds=round(time.monotonic()-t,3),argv=list(map(str,argv))))
 (out/'receipt.json').write_text(json.dumps(dict(scope='Native exact-pin checks, no sandbox or canonical CI claim',theorem_names=cfg['theorem_names'],definition_names=cfg['definition_names'],primitive_targets=primitive,checks=records,source_sha256=hashlib.sha256((pkg/'OpenBaire.lean').read_bytes()).hexdigest()),indent=2)+'\n')
 print(name,p.returncode,records[-1]['seconds'],flush=True)
 if p.returncode:raise SystemExit(p.returncode)
shutil.copyfile(pkg/'OBChallenge.lean',alias/'Challenge.lean')
run('protected-compile',[prefix/'bin/lean','-j1','-M2048','-DwarningAsError=true','-o','BaireProtected/Challenge.olean','BaireProtected/Challenge.lean'],protected)
run('challenge-export',[prefix/'bin/leanexport','BaireProtected.Challenge','--',*targets],protected,out/'challenge.ndjson')
run('solution-export',[prefix/'bin/leanexport','OBSolution','--',*targets],candidate,out/'solution.ndjson')
judge='import Lake.Check.Compare\nimport Lake.Check.Axioms\n\nopen Lean Lake.Check\n\ndef primitive : Array Name := #[``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow,\n  ``Nat.gcd, ``Nat.div, ``Nat.mod, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor,\n  ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat,\n  ``List, ``eagerReduce, ``Nat, ``String, ``String.mk, ``Char, ``optParam,\n  ``autoParam, ``semiOutParam, ``outParam]\n\ndef main (args : List String) : IO UInt32 := do\n  let [challengePath, solutionPath] := args | throw <| IO.userError "two export paths required"\n  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)\n  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)\n  let names := #["imageStrategy_winning", "strong_image", "completelyMetrizable_image",\n    "polish_image", "polish_image_of_t3"].map (fun n => ("OpenPolish." ++ n).toName)\n  let axioms := #[``propext, ``Quot.sound, ``Classical.choice]\n  for labelEnv in [("challenge", challenge), ("solution", solution)] do\n    if let some info := labelEnv.2.constMap["OpenPolish.imageStrategy".toName]? then\n      IO.println s!"{labelEnv.1} imageStrategy direct value constants:"\n      if let some value := info.value? (allowOpaque := true) then\n        for n in value.getUsedConstants do\n          if n.toString.contains "OpenPolish" || n.toString.contains "private" then\n            IO.println n\n  match compareAt challenge solution (names ++ axioms) #[] primitive with\n  | .error error => IO.eprintln error; return 1\n  | .ok () => IO.println "Pinned compareAt: PASS (five theorem targets; no definition holes; all primitive targets)"\n  match checkAxioms solution names #[] axioms with\n  | .error error => IO.eprintln error; return 1\n  | .ok () => IO.println "Pinned checkAxioms: PASS"\n  let helper := "OpenPolish.trap".toName\n  let some (.defnInfo value) := solution.constMap[helper]?\n    | throw <| IO.userError "fixed trap definition missing"\n  -- A well-typed let wrapper preserves meaning but changes the actual definition body.\n  -- The unchanged Comparator must reject it: this helper is not a definition hole.\n  let changed := { value with value := .letE `regressionWitness value.type value.value (.bvar 0) false }\n  let altered := { solution with constMap := solution.constMap.insert helper (.defnInfo changed) }\n  match compareAt challenge altered (names ++ axioms) #[] primitive with\n  | .ok () => IO.eprintln "Altered fixed helper was accepted"; return 1\n  | .error error =>\n    unless error.contains "OpenPolish.trap" do\n      throw <| IO.userError s!"Unexpected negative-control rejection: {error}"\n    IO.println s!"Altered fixed helper rejected: {error}"\n  return 0\n'
a=judge.index('  let names :=')
b=judge.index('  let axioms :=',a)
judge=judge[:a]+'  let names := #['+', '.join(json.dumps(n) for n in cfg['theorem_names'])+'].map String.toName\n'+judge[b:]
a=judge.index('  for labelEnv in')
b=judge.index('  match compareAt',a)
judge=judge[:a]+judge[b:]
judge=judge.replace('five theorem targets','six theorem targets').replace('OpenPolish.trap','OpenBaire.OpenScheme.limit').replace('fixed trap','fixed limit')
(out/'CompareBaire.lean').write_text(judge)
run('pinned-comparator',[prefix/'bin/lean','-j1','-M2048','--run',out/'CompareBaire.lean',out/'challenge.ndjson',out/'solution.ndjson'],env)
run('lean-kernel',[prefix/'bin/leanchecker','--silent','--from-export',out/'solution.ndjson'],env)
ncfg=dict(export_file_path=str(out/'solution.ndjson'),permitted_axioms=cfg['permitted_axioms'],unpermitted_axiom_hard_error=True,num_threads=1,nat_extension=True,string_extension=True)
(out/'nanoda-config.json').write_text(json.dumps(ncfg))
run('nanoda-kernel',[prefix/'bin/nanoda_bin',out/'nanoda-config.json'],env)
run('con-ron-kernel',[prefix/'bin/con-ron','--jobs=1','--verified',out/'solution.ndjson'],env)
