"""Check the local Gottschalk-Hedlund draft's package consistency, not proof verification."""
import json
import pathlib
import re
import subprocess
import sys
import tomllib

from check_imported_definitions import check as check_imported_definitions

if not __debug__:
    raise RuntimeError('assertions must be enabled')

ROOT = pathlib.Path(__file__).resolve().parents[1]
PROJECT = ROOT / 'topology/gottschalk-hedlund'
SELECTED = [
    'GottschalkHedlund.bounded_sums_iff_transfer',
    'GottschalkHedlund.transfer_difference_constant',
    'GottschalkHedlund.bounded_sums_skew_conjugacy',
]
MODULES = ['GottschalkHedlund', 'GHChallenge', 'GHSolution', 'SemanticChallenge', 'SemanticSolution']
CHALLENGE_HEADER = ('/-\nScalar Gottschalk–Hedlund theorem. Apache-2.0; see ATTRIBUTION.md.\n'
                    'Material Lean proof developed by OpenAI Codex.\n-/\nmodule\n'
                    'public import Mathlib.Dynamics.BirkhoffSum.Basic\n'
                    'public import Mathlib.Topology.Algebra.Order.Field\n'
                    'public import Mathlib.Topology.Homeomorph.Lemmas\n'
                    'public import Mathlib.Topology.MetricSpace.Bounded\n'
                    'public import Mathlib.Tactic\n'
                    'public import Mathlib.Topology.Compactness.Compact\n'
                    'public import Mathlib.Topology.Separation.Hausdorff\n'
                    'public import Mathlib.Order.Zorn\n\n@[expose] public section\n')


def imports(body):
    modules = []
    for line in body.splitlines():
        if re.match(r'^\s*(?:(?:public|private|meta)\s+)*import(?:\s|$)', line):
            match = re.fullmatch(r'public import ([A-Za-z_][A-Za-z0-9_.]*)', line)
            assert match, ('unrecognized import directive', line)
            modules.append(match.group(1))
    return modules


def check_challenge_header(body):
    # Imports are only permitted in the exact independently reviewed module header.
    assert body.startswith(CHALLENGE_HEADER), 'Challenge module header changed'


def check(project=PROJECT):
    project = pathlib.Path(project)
    def read(name):
        p = project / name
        assert p.is_file() and not p.is_symlink(), ('missing or symlink', name)
        return p.read_text(encoding='utf-8')

    config = json.loads(read('comparator.json'))
    meta = json.loads(read('formalization.yaml'))
    lake = tomllib.loads(read('lakefile.toml'))
    assert config['challenge_module'] == 'GHChallenge' and config['solution_module'] == 'GHSolution'
    assert config['theorem_names'] == SELECTED and config['definition_names'] == []
    assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
    assert lake['defaultTargets'] == MODULES
    assert lake['moreLeanArgs'] == ['-j1', '-M4096', '-DwarningAsError=true']
    assert lake['require'] == [{'name': 'mathlib', 'git': 'https://github.com/leanprover-community/mathlib4.git',
                                'rev': '065356127b1dc0016f66b7283ce0ce2c4055aa55'}]
    assert read('lean-toolchain').strip() == 'leanprover/lean4:v4.35.0-rc2'
    locked = json.loads(read('lake-manifest.json'))
    mathlib = [x for x in locked['packages'] if x['name'] == 'mathlib']
    assert len(mathlib) == 1 and mathlib[0]['rev'] == '065356127b1dc0016f66b7283ce0ce2c4055aa55'
    assert mathlib[0]['url'].removesuffix('.git') == 'https://github.com/leanprover-community/mathlib4'
    assert meta['project']['authors'] == meta['project']['responsible_maintainers'] == [
        'Arthur Freitas Ramos', 'David Barros Hulak', 'Ruy Jose Guerra Barretto de Queiroz']
    assert meta['project']['license'] == 'Apache-2.0'
    assert 'OpenAI Codex' in meta['status']['attribution_status']
    assert (project / '.gitattributes').read_bytes() == b'# Preserve the exact source bytes in this formalization package.\n* -text\n'

    bodies = {name: read(name + '.lean') for name in MODULES}
    assert bodies['GHChallenge'] == bodies['GottschalkHedlund']
    check_challenge_header(bodies['GHChallenge'])
    assert bodies['GHSolution'] == 'module\npublic import GottschalkHedlund\n'
    assert bodies['SemanticChallenge'].startswith('module\npublic import GHChallenge\n\nopen Function Set GottschalkHedlund\n')
    assert bodies['SemanticSolution'].startswith('module\npublic import GHSolution\n\nopen Function Set GottschalkHedlund\n')
    expected_imports = ['Mathlib.Dynamics.BirkhoffSum.Basic', 'Mathlib.Topology.Algebra.Order.Field',
                        'Mathlib.Topology.Homeomorph.Lemmas', 'Mathlib.Topology.MetricSpace.Bounded',
                        'Mathlib.Tactic', 'Mathlib.Topology.Compactness.Compact',
                        'Mathlib.Topology.Separation.Hausdorff', 'Mathlib.Order.Zorn']
    assert imports(bodies['GHChallenge']) == expected_imports
    assert imports(bodies['GHSolution']) == ['GottschalkHedlund']
    assert imports(bodies['SemanticChallenge']) == ['GHChallenge']
    assert imports(bodies['SemanticSolution']) == ['GHSolution']
    assert bodies['SemanticChallenge'].replace('public import GHChallenge', 'public import GHSolution', 1) == bodies['SemanticSolution']
    for body in bodies.values():
        assert re.search(r'^module\s*$', body, re.MULTILINE)
        assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide)\b', body)
        assert not re.search(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|constant|unsafe|opaque)\s+[A-Za-z_]', body, re.MULTILINE)
    for name in SELECTED:
        assert re.search(r'^theorem\s+' + re.escape(name.rsplit('.', 1)[1]) + r'\b', bodies['GHChallenge'], re.MULTILINE)
    assert 'H p = fiberTranslation h p' in bodies['GHChallenge']
    assert 'provisional source inventory' in read('MATERIAL-DEFINITIONS.md')
    inv = check_imported_definitions(project)
    assert inv['status'] == 'pass'
    assembly = subprocess.run([sys.executable, str(project / 'scripts/check_source_assembly.py')],
                              cwd=project, capture_output=True, text=True)
    assert assembly.returncode == 0, (assembly.stdout, assembly.stderr)
    return {'status': 'pass', 'scope': 'Local package consistency and static source checks only; inventory completeness, Lean compilation and canonical verification are separate.',
            'material_declarations': len(inv['material_declarations'])}


if __name__ == '__main__':
    print(json.dumps(check(pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else PROJECT), indent=2))
