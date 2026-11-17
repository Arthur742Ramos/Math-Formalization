"""Emit independently kernel-checked Lean certificates from integral proposals.

The input is untrusted. Every patch, geometric trace, slope and integral budget
is checked in Lean, then analytic soundness and balanced gluing are applied.
"""
import argparse
from fractions import Fraction
import gzip
import json
import re
from pathlib import Path


def rat(value):
    q = Fraction(value)
    return f'({q.numerator}/{q.denominator} : ℚ)'


def integer(value):
    return str(value) if value >= 0 else f'({value})'


def box(value):
    return '⟨'+', '.join(integer(x) for x in value)+'⟩'


def boxes(values):
    return '['+', '.join(box(x) for x in values)+']'


def trace(value):
    inputs = '⟨'+', '.join(box(x) for x in value['inputs'])+'⟩'
    results = '⟨'+', '.join('⟨'+box(x)+', []⟩' for x in value['values'])+'⟩'
    return '⟨'+inputs+', '+results+'⟩'


def emit(package, packet_path, pilot, block_size=512):
    assert block_size in (128, 256, 512)
    with gzip.open(packet_path, 'rt') as stream:
        packet = json.load(stream)
    assert packet['scale'] == 2**128 and Fraction(packet['approximation_error']) == Fraction(2, 10**12)
    assert len(packet['tau']) == len(packet['iv']) == 20
    output = package/'ErdosOverlap/Certificate/FrontierLeaves'
    output.mkdir(parents=True, exist_ok=True)
    namespace = 'ErdosOverlap.FrontierLeaves'
    module = 'ErdosOverlap.Certificate.FrontierLeaves.'
    emitted = set()
    def write(name, imports, body):
        content = ('/-\nGenerated exact integral certificates. Generation is untrusted;\n'
                   'all arithmetic and source binding are checked in Lean.\n-/\nmodule\n\n')
        meta_imports = []
        if any('erdos_geometry_decide' in declaration for declaration in body):
            meta_imports.append('ErdosOverlap.Numerics.KernelGeometryDecision')
        if any('erdos_leaves_decide' in declaration for declaration in body):
            meta_imports.append('ErdosOverlap.Numerics.KernelLeafDecision')
        content += ''.join(f'public import {x}\n' for x in sorted(set(imports+meta_imports)))
        content += ''.join(f'public meta import {x}\n' for x in sorted(meta_imports))
        content += (f'\nnamespace {namespace}\nopen Numerics\n@[expose] public section\n'
                    'set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
                    'set_option Elab.async false\n\n')
        # Kernel reduction still sees these exact values; runtime code is unused.
        body = [re.sub(r'(?m)^def ', 'noncomputable def ', declaration) for declaration in body]
        content += '\n\n'.join(body)+f'\n\nend\nend {namespace}\n'
        assert len(content.splitlines()) <= 10000, name
        (output/f'{name}.lean').write_text(content)
        emitted.add(name)

    # Discard adaptive subdivision proposals which no accepted leaf consumes.
    used = sorted({leaf['geometry'] for leaves in packet['leaves'].values() for leaf in leaves})
    if pilot:
        used = used[:1]
    used_set = set(used)
    geometries = {g['id']: g for g in packet['geometries'] if g['id'] in used_set}
    patch_ids = sorted({g[k] for g in geometries.values() for k in ['patchA', 'patchB']})
    patch_set = set(patch_ids)
    patches = {p['id']: p for p in packet['patches'] if p['id'] in patch_set}
    patch_modules, geometry_modules = {}, {}
    lambda_definitions = [f'def lam{i:02d} : ℚ := {rat(2*Fraction(packet["tau"][i]))}' for i in range(4,20)]
    write('Lambdas', ['ErdosOverlap.Numerics.FrontierLeafCertificateData'], lambda_definitions)
    for start in range(0, len(patch_ids), 64):
        name = f'Patch{start//64:04d}'
        body = []
        for i in patch_ids[start:start+64]:
            p = patches[i]
            patch_modules[i] = name
            value = '⟨'+', '.join(boxes(v) for v in p['boxes'])+'⟩'
            body.append(f'def p{i:05d} : CheckedPatchCache {p["piece"]} {p["grid"]} :=\n'
                        f'  ⟨{value}, by decide +kernel⟩')
        write(name, ['ErdosOverlap.Numerics.FrontierPolynomialCache'], body)

    for start in range(0, len(used), 64):
        name = f'Geometry{start//64:04d}'
        body, imports = [], ['ErdosOverlap.Numerics.FrontierPolynomialDirectTrace']
        for i in used[start:start+64]:
            g = geometries[i]
            geometry_modules[i] = name
            imports += [module+patch_modules[g[k]] for k in ['patchA', 'patchB']]
            cache = '⟨'+box(g['boxes'][0])+', '+box(g['boxes'][1])+', ⟨'+', '.join(box(b) for b in g['boxes'][2:])+'⟩⟩'
            value = f'⟨{rat(g["left"])}, {rat(g["right"])}, {g["pieceA"]}, {g["pieceB"]}, {g["grid"]}, {cache}⟩'
            body += [f'def d{i:05d} : Geometry := {value}',
                     f'def a{i:05d} : CachedPolynomialTrace := {trace(g["traceA"])}',
                     f'def b{i:05d} : CachedPolynomialTrace := {trace(g["traceB"])}',
                     f'def g{i:05d} : CheckedGeometry :=\n'
                     f'  ⟨d{i:05d}, Geometry.check_of_directTraceCheck _\n'
                     f'    p{g["patchA"]:05d} p{g["patchB"]:05d}\n'
                     f'    a{i:05d} b{i:05d} (by erdos_geometry_decide)⟩']
        write(name, imports, body)
    if pilot:
        print(f'Pilot target: {module}Geometry0000', flush=True)
        return

    for kind, leaves in packet['leaves'].items():
        profile = kind.startswith('Profile')
        mode = int(kind[7:]) if profile else None
        stem = kind[0].lower()+kind[1:]
        leaf_type = f'CheckedProfileLeaf ⟨{mode}, by decide⟩' if profile else f'Checked{kind}Leaf'
        raw_type = 'ProfileLeaf' if profile else kind+'Leaf'
        checker = f'checkedProfileLeaves ⟨{mode}, by decide⟩' if profile else 'checked'+kind+'Leaves'
        integrand = f'(profileIntegrand ⟨{mode}, by decide⟩)' if profile else stem+'Integrand'
        certificate = 'UpperCertificate' if kind == 'Denominator' else 'LowerCertificate'
        error = '4*approximationError' if kind == 'Denominator' else '2*approximationError'
        block_function = 'profileBlock_certificate' if profile else stem+'Block_certificate'
        blocks = []
        for start in range(0, len(leaves), block_size):
            chunk, index = leaves[start:start+block_size], start//block_size
            block_name = f'{kind}Block{index:04d}'
            imports = ['ErdosOverlap.Numerics.FrontierCheckedLeafLists', module+'Lambdas']
            entries = []
            for leaf in chunk:
                i = leaf['geometry']
                imports.append(module+geometry_modules[i])
                fields = f'g{i:05d}, '
                if profile:
                    cell = 'none' if leaf['cell'] is None else f'(some {leaf["cell"]})'
                    if leaf['cell'] is None:
                        assert Fraction(leaf['lam']) == 2*Fraction(packet['tau'][mode])
                        lam = f'lam{mode:02d}'
                    else:
                        lam = rat(leaf['lam'])
                    fields += f'{cell}, {lam}, '
                fields += integer(leaf['bound'])
                entries.append(f'  ⟨{fields}⟩')
            list_name = f'{stem}Leaves{index:04d}'
            raw_name = f'{stem}Raw{index:04d}'
            # Keep raw data, checked leaves and their block certificate together.
            # This changes module layout only; every ordered leaf is retained.
            body = [f'def {raw_name} : List {raw_type} := [\n'+',\n'.join(entries)+'\n]',
                    f'def {list_name} : List ({leaf_type}) :=\n  {checker} {raw_name} (by erdos_leaves_decide)']
            lo, hi = geometries[chunk[0]['geometry']]['left'], geometries[chunk[-1]['geometry']]['right']
            amount = sum(leaf['bound'] for leaf in chunk)
            claim, theorem = f'{stem}Claim{index:04d}', f'{stem}Block{index:04d}'
            write(block_name, imports+['ErdosOverlap.Numerics.FrontierLeafAssemblyActual'],
                  body+[f'def {claim} : IntegralClaim := ⟨{rat(lo)}, {rat(hi)}, {integer(amount)}⟩',
                   f'theorem {theorem} : IntegralClaim.{certificate} {integrand} ({error}) {claim} :=\n'
                   f'  {block_function} {list_name} (by decide +kernel) (by decide +kernel)'])
            blocks.append((block_name, claim, theorem, lo, hi, amount))
        level = 0
        while len(blocks) > 1:
            joined = []
            for i in range(0, len(blocks), 2):
                if i+1 == len(blocks):
                    joined.append(blocks[i])
                    continue
                a, b = blocks[i:i+2]
                assert a[4] == b[3]
                name = f'{kind}Join{level:02d}_{i//2:04d}'
                claim, theorem = name[0].lower()+name[1:]+'Claim', name[0].lower()+name[1:]+'Bound'
                amount = a[5]+b[5]
                write(name, [module+a[0], module+b[0]],
                      [f'def {claim} : IntegralClaim := ⟨{rat(a[3])}, {rat(b[4])}, {integer(amount)}⟩',
                       f'theorem {theorem} : IntegralClaim.{certificate} {integrand} ({error}) {claim} :=\n'
                       f'  {a[2]}.glue {b[2]} (by decide +kernel)'])
                joined.append((name, claim, theorem, a[3], b[4], amount))
            blocks, level = joined, level+1
        final = blocks[0]
        write(kind+'Total', [module+final[0]],
              [f'def {stem}Claim : IntegralClaim := {final[1]}',
               f'theorem {stem}Certificate : IntegralClaim.{certificate} {integrand} ({error}) {stem}Claim :=\n'
               f'  {final[2]}'])
    for old in output.glob('*.lean'):
        if old.stem not in emitted:
            assert re.fullmatch(r'(?:Patch\d+|Geometry\d+|Lambdas|(?:Denominator|Central|Profile\d+)(?:Data\d+|Block\d+|Join\d+_\d+|Total))', old.stem), old
            old.unlink()
    print(json.dumps({'patches': len(patches), 'geometries': len(geometries), 'output': str(output)}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--pilot', action='store_true')
    parser.add_argument('--block-size', type=int, choices=[128,256,512], default=512)
    args = parser.parse_args()
    emit(args.package, args.packet, args.pilot, args.block_size)
