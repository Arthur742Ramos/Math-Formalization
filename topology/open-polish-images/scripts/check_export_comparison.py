"""Native regression using unchanged pinned comparison/axiom APIs; no canonical claim."""
import argparse, hashlib, json, os, pathlib, re, shutil, subprocess, time

JUDGE = r'''import Lake.Check.Compare
import Lake.Check.Axioms

open Lean Lake.Check

def primitive : Array Name := #[``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow,
  ``Nat.gcd, ``Nat.div, ``Nat.mod, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor,
  ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat,
  ``List, ``eagerReduce, ``Nat, ``String, ``String.mk, ``Char, ``optParam,
  ``autoParam, ``semiOutParam, ``outParam]

def main (args : List String) : IO UInt32 := do
  let [challengePath, solutionPath] := args | throw <| IO.userError "two export paths required"
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)
  let names := #["imageStrategy_winning", "strong_image", "completelyMetrizable_image",
    "polish_image", "polish_image_of_t3"].map (fun n => ("OpenPolish." ++ n).toName)
  let axioms := #[``propext, ``Quot.sound, ``Classical.choice]
  for labelEnv in [("challenge", challenge), ("solution", solution)] do
    if let some info := labelEnv.2.constMap["OpenPolish.imageStrategy".toName]? then
      IO.println s!"{labelEnv.1} imageStrategy direct value constants:"
      if let some value := info.value? (allowOpaque := true) then
        for n in value.getUsedConstants do
          if n.toString.contains "OpenPolish" || n.toString.contains "private" then
            IO.println n
  match compareAt challenge solution (names ++ axioms) #[] primitive with
  | .error error => IO.eprintln error; return 1
  | .ok () => IO.println "Pinned compareAt: PASS (five theorem targets; no definition holes; all primitive targets)"
  match checkAxioms solution names #[] axioms with
  | .error error => IO.eprintln error; return 1
  | .ok () => IO.println "Pinned checkAxioms: PASS"
  let helper := "OpenPolish.trap".toName
  let some (.defnInfo value) := solution.constMap[helper]?
    | throw <| IO.userError "fixed trap definition missing"
  -- A well-typed let wrapper preserves meaning but changes the actual definition body.
  -- The unchanged Comparator must reject it: this helper is not a definition hole.
  let changed := { value with value := .letE `regressionWitness value.type value.value (.bvar 0) false }
  let altered := { solution with constMap := solution.constMap.insert helper (.defnInfo changed) }
  match compareAt challenge altered (names ++ axioms) #[] primitive with
  | .ok () => IO.eprintln "Altered fixed helper was accepted"; return 1
  | .error error =>
    unless error.contains "OpenPolish.trap" do
      throw <| IO.userError s!"Unexpected negative-control rejection: {error}"
    IO.println s!"Altered fixed helper rejected: {error}"
  return 0
'''

PKG = pathlib.Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--work-dir', type=pathlib.Path, required=True, help='Fresh directory for exports and receipts')
args = parser.parse_args()
PREFIX = pathlib.Path(subprocess.check_output(['lean', '--print-prefix'], cwd=PKG, text=True).strip())
version = subprocess.check_output([str(PREFIX/'bin/lean'), '--version'], text=True)
assert '4.35.0-rc2' in version and '11acb17ec6b07a8f9e9173e6845197929540936b' in version, version
CHECK_SOURCE = PREFIX / 'src/lean/lake/Lake/CLI/Check.lean'
env = os.environ.copy()
env.update(PATH=str(PREFIX / 'bin') + ':/usr/bin:/bin', LEAN_NUM_THREADS='2')
deps = sorted((PKG / '.lake/packages').iterdir())
dependency_paths = [str(PREFIX / 'lib/lean')] + [str(p / '.lake/build/lib/lean') for p in deps]
source = CHECK_SOURCE.read_text()
primitive = re.findall(r'^    ``([\w.]+),?$', source.split('def primitiveTargets', 1)[1].split('def builtinTargets', 1)[0], re.M)
assert len(primitive) == 26
assert re.findall(r'``([\w.]+)', JUDGE.split('def main', 1)[0]) == primitive
cfg = json.loads((PKG / 'comparator.json').read_text())
assert cfg['definition_names'] == []
assert cfg['permitted_axioms'] == ['propext', 'Quot.sound', 'Classical.choice']
assert cfg['theorem_names'] == ['OpenPolish.' + n for n in [
    'imageStrategy_winning', 'strong_image', 'completelyMetrizable_image',
    'polish_image', 'polish_image_of_t3']]
targets = ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind'] + cfg['theorem_names'] + cfg['permitted_axioms'] + primitive
out = args.work_dir.resolve()
out.mkdir(parents=True, exist_ok=False)
alias = out / 'PalomarStableIdentity'
alias.mkdir()
shutil.copyfile(PKG / 'OPChallenge.lean', alias / 'Challenge.lean')
receipts = []

def run(name, argv, cwd, runenv, output=None):
    started = time.monotonic()
    with (out / (name + '.log')).open('w') as log:
        if output:
            with output.open('w') as f:
                p = subprocess.run(argv, cwd=cwd, env=runenv, stdout=f, stderr=log)
        else:
            p = subprocess.run(argv, cwd=cwd, env=runenv, stdout=log, stderr=subprocess.STDOUT)
    receipt = dict(name=name, argv=list(map(str, argv)), exit_code=p.returncode,
                   elapsed_seconds=round(time.monotonic() - started, 3))
    receipts.append(receipt)
    (out / 'receipt.json').write_text(json.dumps(dict(
        scope='Native pinned APIs and separately compiled protected-alias source; no Linux sandbox or canonical workflow claim',
        challenge_sha256=hashlib.sha256((alias / 'Challenge.lean').read_bytes()).hexdigest(),
        primitive_targets=primitive, export_targets=targets, checks=receipts), indent=2) + '\n')
    print(name, p.returncode, receipt['elapsed_seconds'], flush=True)
    if p.returncode: raise SystemExit(p.returncode)

judge = out / 'CompareExports.lean'
judge.write_text(JUDGE)
run('package-build', [str(PREFIX/'bin/lake'), '--no-cache', 'build'], PKG, env)
protected_env = env | dict(LEAN_PATH=':'.join([str(out)] + dependency_paths),
    LEAN_SRC_PATH=':'.join(map(str, deps)))
run('protected-compile', [str(PREFIX/'bin/lean'), '-j2', '-M3072', '-DwarningAsError=true',
    '-o', 'PalomarStableIdentity/Challenge.olean', 'PalomarStableIdentity/Challenge.lean'], out, protected_env)
challenge_export = out / 'challenge.ndjson'
solution_export = out / 'solution.ndjson'
run('challenge-export', [str(PREFIX/'bin/leanexport'), 'PalomarStableIdentity.Challenge', '--', *targets], out, protected_env, challenge_export)
run('solution-export', [str(PREFIX/'bin/lake'), 'env', 'leanexport', 'OPSolution', '--', *targets], PKG, env, solution_export)
run('pinned-comparator', [str(PREFIX/'bin/lean'), '-j2', '-M3072', '--run',
    str(judge), str(challenge_export), str(solution_export)], out, env)
run('export-native-kernel', [str(PREFIX/'bin/leanchecker'), '--silent', '--from-export', str(solution_export)], out, env)
