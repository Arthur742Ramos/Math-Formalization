#!/usr/bin/env python3
"""Local interface/source-closure evidence; NEVER a protected Comparator verdict."""
from pathlib import Path
import subprocess, tempfile, json, hashlib, re, secrets, os

ROOT = Path(__file__).resolve().parents[1]


def inspect():
    config = json.loads((ROOT / 'comparator.json').read_text())
    names = config['theorem_names'] + config['definition_names']
    name_array = '#[' + ', '.join('`' + name for name in names) + ']'
    code = '''module
import Lean
import Lake.Check.Compare
open Lean
public def main : IO Unit := do
 initSearchPath (← findSysroot)
 let paths ← IO.getEnv "HODGE_ALIAS_PATH"
 if let some path := paths then searchPathRef.modify (· ++ [System.FilePath.mk path])
 let moduleName := (← IO.getEnv "HODGE_CHALLENGE_MODULE").getD "Challenge"
 let c ← importModules #[{module := moduleName.toName, importAll := true}] {}
 let s ← importModules #[{module := `Solution, importAll := true}] {}
 let base := (← IO.getEnv "HODGE_EXPORT_DIR").getD ""
 let challengeExport := (← IO.getEnv "HODGE_CHALLENGE_EXPORT").getD (base ++ "/challenge.ndjson")
 let ce ← LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk challengeExport .read))
 let mut se ← LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk (base ++ "/solution.ndjson") .read))
 let control := (← IO.getEnv "HODGE_NEGATIVE_CONTROL").getD ""
 if control == "statement" then
  let n := `ComputationalHodge.PresentationHomology.pairing_loopClass
  let some (.thmInfo v) := se.constMap[n]? | throw (IO.userError "missing control theorem")
  se := { se with constMap := se.constMap.insert n (.thmInfo { v with type := mkConst ``False }) }
 if control == "closure" || control == "definition-value" then
  let n := if control == "closure" then `ComputationalHodge.evaluation else `ComputationalHodge.PresentationHomology.boundary₂
  let some (.defnInfo v) := se.constMap[n]? | throw (IO.userError "missing control definition")
  se := { se with constMap := se.constMap.insert n (.defnInfo { v with value := mkConst ``False }) }
 IO.ofExcept (Lake.Check.compareAt ce se THEOREMS DEFINITIONS PRIMITIVES)
 IO.println "EXACT_COMPARATOR pass"
 for n in NAMES do
  let some ci := ce.constMap[n]? | throw (IO.userError s!"missing Challenge {n}")
  let some si := se.constMap[n]? | throw (IO.userError s!"missing Solution {n}")
  let ck := match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | _ => "other"
  let sk := match si with | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | _ => "other"
  let defeq := match Kernel.isDefEq s {} ci.type si.type with | .ok b => b | .error _ => false
  if ci.toConstantVal != si.toConstantVal then throw (IO.userError s!"exact constant header mismatch {n}")
  if ck == "definition" && ci.value? true != si.value? true then throw (IO.userError s!"literal definition value mismatch {n}")
  IO.println s!"INTERFACE {n}|{ck}|{sk}|{ci.type == si.type}|{defeq}|{ci.value? true == si.value? true}"
 if moduleName != "Challenge" then return
 let sp ← getSrcSearchPath
 for n in c.header.moduleNames do
  let path ← findLean sp n
  IO.println s!"SOURCE {n}|{path}"
'''.replace('NAMES', name_array)
    for key, ns in [('THEOREMS', config['theorem_names']), ('DEFINITIONS', config['definition_names'])]:
        code = code.replace(key, '#[' + ', '.join('`' + n for n in ns) + ']')
    sysroot = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
    cli = sysroot / 'src/lean/lake/Lake/CLI/Check.lean'
    primitive_source = cli.read_text().split('def primitiveTargets', 1)[1].split('def builtinTargets', 1)[0]
    primitive_source = re.sub(r'--[^\n]*', '', primitive_source)
    primitives = re.findall(r'``([A-Za-z][A-Za-z0-9_.]*)', primitive_source)
    assert primitives and 'Nat.add' in primitives
    code = code.replace('PRIMITIVES', '#[' + ', '.join('`' + n for n in primitives) + ']')
    dynlib = sysroot / 'lib/lean/libLake_shared.so'
    with tempfile.TemporaryDirectory(prefix='hodge-interfaces-') as tmp:
        probe = Path(tmp) / 'Inspect.lean'
        probe.write_text(code)
        exports = {}
        for module, label in [('Challenge', 'challenge'), ('Solution', 'solution')]:
            path = Path(tmp) / (label + '.ndjson')
            with path.open('w') as stream:
                subprocess.run(['lake', 'env', 'leanexport', module, '--', *names, *primitives, 'Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind'],
                               cwd=ROOT, stdout=stream, stderr=subprocess.PIPE, text=True, check=True)
            exports[label] = {'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'bytes': path.stat().st_size}
        base_env = {k: v for k, v in os.environ.items() if not k.startswith('HODGE_')}
        base_env['HODGE_EXPORT_DIR'] = tmp
        result = subprocess.run(['lake', 'env', 'lean', '--load-dynlib=' + str(dynlib), '--run', str(probe)], cwd=ROOT,
                                env=base_env, check=False, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(result.stdout)
        controls = []
        for mode, expected in [('statement', 'theorem statement do not match'),
                               ('closure', 'Const does not match between challenge and target'),
                               ('definition-value', 'literal definition value mismatch')]:
            env = dict(base_env, HODGE_NEGATIVE_CONTROL=mode)
            negative = subprocess.run(['lake', 'env', 'lean', '--load-dynlib=' + str(dynlib), '--run', str(probe)], cwd=ROOT,
                                      env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            assert negative.returncode != 0 and expected in negative.stdout, (mode, negative.stdout)
            controls.append({'mode': mode, 'rejected': True, 'diagnostic': negative.stdout.strip()})
        alias_name = 'HodgeLocal' + secrets.token_hex(8) + '.Challenge'
        alias_file = Path(tmp).joinpath(*alias_name.split('.')).with_suffix('.lean')
        alias_file.parent.mkdir()
        alias_file.write_bytes((ROOT / 'Challenge.lean').read_bytes())
        compile_alias = subprocess.run(['lake', 'env', 'lean', '--root=' + tmp, '-o', str(alias_file.with_suffix('.olean')), str(alias_file)], cwd=ROOT,
                                       text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert compile_alias.returncode == 0, compile_alias.stdout
        alias_export = Path(tmp) / 'alias.ndjson'
        env = dict(base_env, HODGE_ALIAS_PATH=tmp, HODGE_CHALLENGE_MODULE=alias_name, HODGE_CHALLENGE_EXPORT=str(alias_export))
        # leanexport uses LEAN_PATH, while the probe adds the alias through searchPathRef.
        lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, text=True).strip()
        export_env = dict(base_env, LEAN_PATH=tmp + os.pathsep + lean_path)
        with alias_export.open('w') as stream:
            subprocess.run([str(sysroot / 'bin/leanexport'), alias_name, '--', *names, *primitives, 'Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind'], cwd=ROOT,
                           env=export_env, stdout=stream, stderr=subprocess.PIPE, text=True, check=True)
        exports['random_alias'] = {'sha256': hashlib.sha256(alias_export.read_bytes()).hexdigest(), 'bytes': alias_export.stat().st_size}
        alias = subprocess.run(['lake', 'env', 'lean', '--load-dynlib=' + str(dynlib), '--run', str(probe)], cwd=ROOT,
                               env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert alias.returncode == 0 and 'EXACT_COMPARATOR pass' in alias.stdout, alias.stdout
    interfaces, sources = [], []
    packages = json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
    owners = []
    for package in packages:
        directory = (ROOT / '.lake/packages' / package['name']).resolve()
        head = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
        assert head == package['rev'], ('Wrong dependency HEAD', package['name'])
        tree = subprocess.check_output(['git', '-C', str(directory), 'ls-tree', '-rz', head])
        blobs = {}
        for row in tree.split(b'\0'):
            if row:
                fields, path = row.split(b'\t', 1)
                if fields.split()[1] == b'blob':
                    blobs[path.decode()] = fields.split()[2].decode()
        owners.append((directory, package, blobs))
    mathlib = next(v for v in owners if v[1]['name'] == 'mathlib')
    official_raw = (mathlib[0] / 'lake-manifest.json').read_bytes()
    assert official_raw == subprocess.check_output(['git', '-C', str(mathlib[0]), 'show', mathlib[1]['rev'] + ':lake-manifest.json'])
    official = json.loads(official_raw)['packages']
    flattened = {row['name']: row for row in packages}
    for expected in official:
        actual = flattened[expected['name']]
        assert actual['rev'] == expected['rev'] and actual['url'].removesuffix('.git') == expected['url'].removesuffix('.git')
    for line in result.stdout.splitlines():
        if line.startswith('INTERFACE '):
            name, ck, sk, same_type, defeq, same_value = line[10:].split('|')
            expected = 'theorem' if name in config['theorem_names'] else 'definition'
            assert ck == sk == expected, ('Wrong declaration kind', name, ck, sk)
            assert same_type == 'true', ('Exact theorem/definition type mismatch', name)
            assert defeq == 'true', ('Local interface types are not definitionally equal', name)
            interfaces.append({'name': name, 'kind': ck, 'types_syntactically_equal': same_type == 'true',
                               'types_kernel_defeq_in_solution_environment': True,
                               'values_syntactically_equal': same_value == 'true'})
        elif line.startswith('SOURCE '):
            module, path = line[7:].split('|', 1)
            path = Path(path).resolve()
            raw = path.read_bytes()
            row = {'module': module, 'sha256': hashlib.sha256(raw).hexdigest()}
            owner = next((v for v in owners if path.is_relative_to(v[0])), None)
            if owner:
                directory, package, blobs = owner
                relative = path.relative_to(directory).as_posix()
                blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
                assert blobs.get(relative) == blob, ('Source differs from pinned Git', package['name'], relative)
                row.update(origin=package['name'], path=relative, commit=package['rev'],
                           repository=package['url'], git_blob_sha1=blob, git_source_authenticated=True)
            elif path == ROOT / 'Challenge.lean':
                row.update(origin='candidate', path='Challenge.lean')
            else:
                assert '/src/lean/' in path.as_posix(), ('Noncanonical local Challenge import', str(path))
                row.update(origin='bundled-Lean-toolchain-source', path=path.as_posix().split('/src/lean/', 1)[1],
                           git_source_authenticated=False)
            sources.append(row)
    assert {r['name'] for r in interfaces} == set(names)
    assert sources and {r['path'] for r in sources if r['origin'] == 'candidate'} == {'Challenge.lean'}
    return {'status': 'pass', 'scope': 'Local separate environments: actual pinned leanexport and Lake.Check.compareAt exact exported declaration/closure comparison plus literal selected definition values, declaration kinds and kernel defeq. Compiled Challenge source closure with pinned Git-byte checks. Writable local compilation, not protected canonical execution or independent kernel replay.',
            'original_failure_regression': [line for line in result.stdout.splitlines() if line.startswith(('ORIGINAL_REGRESSION ', 'TYPE_CONSTANTS_'))], 'local_exports': exports, 'exact_pinned_compareAt': True, 'negative_controls': controls, 'negative_control_scope': 'In-memory malformed declaration mutations test comparison rejection only; not kernel-checked counterexamples or canonical controls.', 'random_alias_comparison': {'module': alias_name, 'pass': True, 'source_sha256': hashlib.sha256((ROOT / 'Challenge.lean').read_bytes()).hexdigest()} , 'literal_selected_definition_values_equal': True, 'compare_source_sha256': hashlib.sha256((sysroot / 'src/lean/lake/Lake/Check/Compare.lean').read_bytes()).hexdigest(), 'libLake_shared_sha256': hashlib.sha256(dynlib.read_bytes()).hexdigest(), 'primitive_targets': primitives,
            'interfaces': interfaces, 'source_modules': sources,
            'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
            'core_source_limit': 'Bundled Lean source bytes hashed; protected toolchain/authenticated artifact verification remains canonical-run work.'}


if __name__ == '__main__':
    print(json.dumps(inspect(), indent=2))
