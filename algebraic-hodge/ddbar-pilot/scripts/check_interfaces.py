#!/usr/bin/env python3
"""Local interface/source-closure evidence; NEVER a protected Comparator verdict."""
from pathlib import Path
import subprocess, tempfile, json, hashlib

ROOT = Path(__file__).resolve().parents[1]


def inspect():
    config = json.loads((ROOT / 'comparator.json').read_text())
    names = config['theorem_names'] + config['definition_names']
    name_array = '#[' + ', '.join('`' + name for name in names) + ']'
    code = '''module
import Lean
open Lean
public def main : IO Unit := do
 initSearchPath (← findSysroot)
 let c ← importModules #[{module := `HodgeChallenge, importAll := true}] {}
 let s ← importModules #[{module := `HodgeSolution, importAll := true}] {}
 for n in NAMES do
  let some ci := c.find? n | throw (IO.userError s!"missing Challenge {n}")
  let some si := s.find? n | throw (IO.userError s!"missing Solution {n}")
  let ck := match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | _ => "other"
  let sk := match si with | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | _ => "other"
  let defeq := match Kernel.isDefEq s {} ci.type si.type with | .ok b => b | .error _ => false
  IO.println s!"INTERFACE {n}|{ck}|{sk}|{ci.type == si.type}|{defeq}|{ci.value? true == si.value? true}"
 let sp ← getSrcSearchPath
 for n in c.header.moduleNames do
  let path ← findLean sp n
  IO.println s!"SOURCE {n}|{path}"
'''.replace('NAMES', name_array)
    with tempfile.TemporaryDirectory(prefix='hodge-interfaces-') as tmp:
        probe = Path(tmp) / 'Inspect.lean'
        probe.write_text(code)
        result = subprocess.run(['lake', 'env', 'lean', '--run', str(probe)], cwd=ROOT,
                                check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
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
            elif path == ROOT / 'HodgeChallenge.lean':
                row.update(origin='candidate', path='HodgeChallenge.lean')
            else:
                assert '/src/lean/' in path.as_posix(), ('Noncanonical local Challenge import', str(path))
                row.update(origin='bundled-Lean-toolchain-source', path=path.as_posix().split('/src/lean/', 1)[1],
                           git_source_authenticated=False)
            sources.append(row)
    assert {r['name'] for r in interfaces} == set(names)
    assert sources and {r['path'] for r in sources if r['origin'] == 'candidate'} == {'HodgeChallenge.lean'}
    return {'status': 'pass', 'scope': 'Local separate environments, declaration kinds and local kernel type-definitional equality in Solution environment (not canonical frozen environment); compiled Challenge module source closure with pinned Git-byte checks. Not protected proof/definition comparison or independent kernel replay.',
            'interfaces': interfaces, 'source_modules': sources,
            'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
            'core_source_limit': 'Bundled Lean source bytes hashed; protected toolchain/authenticated artifact verification remains canonical-run work.'}


if __name__ == '__main__':
    print(json.dumps(inspect(), indent=2))
