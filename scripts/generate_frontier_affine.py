"""Compile all net periodic/phase rows into checked exact affine pieces."""
import argparse
from collections import defaultdict
from fractions import Fraction as F
import json
from pathlib import Path
import re


def q(x):
    x = F(x)
    return str(x.numerator) if x.denominator == 1 else f'({x.numerator}/{x.denominator})'


def header(imports):
    return '''/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

''' + ''.join(f'public import {m}\n' for m in imports) + '''
namespace ErdosOverlap.FrontierJumps
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

'''


def ending():
    return '\nend\nend ErdosOverlap.FrontierJumps\n'


def combine(*blocks):
    sums = defaultdict(lambda: [F(0), F(0)])
    for block in blocks:
        for knot, constant, slope in block:
            sums[knot][0] += constant
            sums[knot][1] += slope
    return [(k, a, b) for k, (a, b) in sorted(sums.items()) if a or b]


def row_jumps(r, k, cell, perimeter, weight):
    terms = [(r, 1), (k-r, 1), (k, 1)] if perimeter else [(k, 1), (r, -1), (k-r, -1)]
    jumps = []
    for dilation, sign in terms:
        value = F(sign*131072, 4*dilation)*weight
        for j in range(dilation):
            index = (dilation*cell+j)%131072
            for v in (index, 131071-index):
                jumps.extend([(F(2*v, 131072), value, F(0)), (F(2*(v+1), 131072), -value, F(0))])
    return combine(jumps)


def table(name, values):
    literals = [f'⟨{q(k)}, {q(a)}, {q(b)}⟩' for k, a, b in values]
    lines = [', '.join(literals[i:i+4]) for i in range(0, len(literals), 4)]
    return f'def {name} : List AffineJump := [\n  ' + ',\n  '.join(lines) + '\n]\n\n'


def generate(package):
    cert = package/'ErdosOverlap/Certificate'
    components = []
    component_sources = []
    for old in cert.glob('FrontierPeriodicJumps[0-9]*.lean'):
        old.unlink()
    periodic_paths = sorted(cert.glob('FrontierPeriodic[0-9][0-9][0-9].lean'))
    assert periodic_paths and all(path.stem == f'FrontierPeriodic{i:03d}' for i, path in enumerate(periodic_paths))
    for chunk, path in enumerate(periodic_paths):
        rows = [(int(r), int(k), int(i), per == 'true', F(int(a), int(b)))
                for r, k, i, per, a, b in re.findall(
                    r'⟨(\d+), (\d+), (\d+), (true|false), \((-?\d+) / (\d+) : ℚ\)⟩', path.read_text())]
        assert 0 < len(rows) <= 64
        name = f'periodic{chunk:03d}'
        module = f'ErdosOverlap.Certificate.FrontierPeriodicJumps{chunk:03d}'
        text = header(['ErdosOverlap.KernelJumps', f'ErdosOverlap.Certificate.FrontierPeriodic{chunk:03d}'])
        blocks, parts = [], []
        for part_index, start in enumerate(range(0, len(rows), 16)):
            part = f'{name}_part{part_index:02d}'
            parts.append(part)
            values = combine(*(row_jumps(*row) for row in rows[start:start+16]))
            blocks.append(values)
            text += table(part, values)
            text += f'''theorem {part}_eq : {part} = compiledPeriodicRows 131072
    ((FrontierData.{name}.drop {start}).take 16) := by
  apply affineJumpsEqual_sound
  decide +kernel

'''
        values = combine(*blocks)
        text += table(name, values)
        text += f'def {name}_blocks : List (List AffineJump) := [' + ', '.join(parts) + ']\n\n'
        text += f'''theorem {name}_compiled : {name} = compiledJumpBlocks {name}_blocks := by
  apply affineJumpsEqual_sound
  decide +kernel

theorem {name}_value (t : ℝ) : affineJumpSum {name} t =
    affineJumpSum (periodicRowsJumps 131072 FrontierData.{name}) t := by
  rw [{name}_compiled, affineJumpSum_compiledBlocks]
  simp only [{name}_blocks, List.flatten_cons, List.flatten_nil,
    List.append_nil, affineJumpSum_append]
  rw [''' + ', '.join(part+'_eq' for part in parts) + ''']
  simp only [affineJumpSum_compiledPeriodicRows]
  have hparts : FrontierData.'''+name+' = ' + ' ++ '.join(
            f'((FrontierData.{name}.drop {j*16}).take 16)' for j in range(len(parts))) + ''' := by rfl
  conv_rhs => rw [hparts]
  all_goals simp only [periodicRowsJumps_append, affineJumpSum_append, add_assoc]
''' + ending()
        assert len(text.splitlines()) <= 10000
        (cert/f'FrontierPeriodicJumps{chunk:03d}.lean').write_text(text)
        components.append((name, module, values))
        component_sources.append(name+'_value')
    periodic_count = len(components)
    frozen = json.loads((package/'certificates/frontier/kernel.json').read_text())
    delta = {key: F(value) for key, value in frozen['delta'].items()}
    native = (cert/'Native6KernelData.lean').read_text()
    pattern = r'def phase(\d+) : PhaseFunctionalRow :=\s*⟨(\d+), \(([^)]+)\), #\[(.*?)\], \(([^)]+)\), \(([^)]+)\)⟩'
    for index, cells, multiplier, gamma, lower, mean in re.findall(pattern, native, re.S):
        index, cells = int(index), int(cells)
        multiplier = F(multiplier)+delta.get(f'phase:{index}', F(0))
        gamma = [F(item.strip().strip('()')) for item in gamma.split(',')]
        width = F(2, cells)
        jumps = []
        for j, value in enumerate(gamma):
            weight = multiplier*value/(width if j == 0 else 2*width)
            for knot, scale in [(j*width-width, weight/width), (j*width, -2*weight/width),
                                (j*width+width, weight/width)]:
                jumps.append((knot, -knot*scale, scale))
        values = combine(jumps)
        name = f'phase{index:02d}'
        module = f'ErdosOverlap.Certificate.FrontierPhaseJumps{index:02d}'
        text = header(['ErdosOverlap.KernelJumps', 'ErdosOverlap.Certificate.FrontierKernelData'])
        text += table(name, values)
        text += f'''theorem {name}_eq : {name} = compressedJumps FrontierData.{name}.jumps := by
  apply affineJumpsEqual_sound
  decide +kernel
''' + ending()
        (cert/f'FrontierPhaseJumps{index:02d}.lean').write_text(text)
        components.append((name, module, values))
        component_sources.append(name+'_eq')
    nodes, merge_proofs, level = components, [], 0
    while len(nodes) > 1:
        following = []
        for j in range(0, len(nodes), 2):
            if j+1 == len(nodes):
                following.append(nodes[j])
                continue
            a, b = nodes[j:j+2]
            name = f'merge{level:02d}_{j//2:03d}'
            module = f'ErdosOverlap.Certificate.FrontierMerge{level:02d}_{j//2:03d}'
            values = combine(a[2], b[2])
            text = header(sorted({a[1], b[1]})) + table(name, values)
            text += f'''theorem {name}_eq : {name} = mergeCompressedJumps {a[0]} {b[0]} := by
  apply affineJumpsEqual_sound
  decide +kernel
''' + ending()
            assert len(text.splitlines()) <= 10000
            (cert/f'FrontierMerge{level:02d}_{j//2:03d}.lean').write_text(text)
            merge_proofs.append(name+'_eq')
            following.append((name, module, values))
        nodes, level = following, level+1
    final_name, final_module, jumps = nodes[0]
    text = header([final_module])
    text += f'def finalJumps : List AffineJump := {final_name}\n\n'
    text += '''theorem finalJumps_source (t : ℝ) : affineJumpSum finalJumps t =
    affineJumpSum (periodicRowsJumps Native6Data.cells FrontierData.periodicRows) t +
      affineJumpSum (phaseRowsJumps FrontierData.phaseRows) t := by
  simp only [finalJumps, ''' + ', '.join(reversed(merge_proofs)) + ''', affineJumpSum_mergeCompressed]
  simp only [''' + ', '.join(component_sources) + ''', affineJumpSum_compressed]
  have hempty : affineJumpSum [] t = 0 := rfl
  simp only [FrontierData.periodicRows, FrontierData.phaseRows, Native6Data.cells,
    periodicRowsJumps_append, phaseRowsJumps, affineJumpSum_append,
    hempty, add_zero, add_assoc]

theorem finalJumps_isChain : finalJumps.IsChain (fun a b => a.knot ≤ b.knot) := by
  decide +kernel

theorem finalJumps_sorted : finalJumps.Pairwise (fun a b => a.knot ≤ b.knot) := by
  letI : Trans (fun a b : AffineJump => a.knot ≤ b.knot)
      (fun a b : AffineJump => a.knot ≤ b.knot) (fun a b : AffineJump => a.knot ≤ b.knot) :=
    ⟨fun h₁ h₂ => h₁.trans h₂⟩
  exact finalJumps_isChain.pairwise
''' + ending()
    (cert/'FrontierJumpBinding.lean').write_text(text)
    left, constant, slope, full = F(-1), F(0), F(0), []
    for knot, dc, ds in jumps:
        full.append((left, knot, constant, slope))
        left, constant, slope = knot, constant+dc, slope+ds
    full.append((left, F(3), constant, slope))
    pieces = [row for row in full if row[0] >= 0 and row[1] <= 2]
    assert pieces[0][0] == 0 and pieces[-1][1] == 2
    assert all(a[1] == b[0] for a, b in zip(pieces, pieces[1:]))
    chunks = [pieces[i:i+64] for i in range(0, len(pieces), 64)]
    text = header(['ErdosOverlap.AffineCompiler', 'Mathlib.Data.List.GetD'])
    for i, block in enumerate(chunks):
        literals = [f'⟨{q(l)}, {q(r)}, {q(a)}, {q(b)}⟩' for l, r, a, b in block]
        text += f'def piecesChunk{i:03d} : List AffinePiece := [\n  ' + ',\n  '.join(
            ', '.join(literals[i:i+4]) for i in range(0, len(literals), 4)) + '\n]\n\n'
    # The complete prefix scan includes the phase hats outside [0,2].
    outside_left = [p for p in full if p[1] <= 0]
    outside_right = [p for p in full if p[0] >= 2]
    for name, block in [('outsideLeft', outside_left), ('outsideRight', outside_right)]:
        text += f'def {name} : List AffinePiece := [\n' + ',\n'.join(
            f'  ⟨{q(l)}, {q(r)}, {q(a)}, {q(b)}⟩' for l, r, a, b in block) + '\n]\n\n'
    count, blocks, last = len(pieces), len(chunks), len(chunks[-1])
    text += 'def piecesBlocks : List (List AffinePiece) := [' + ', '.join(f'piecesChunk{i:03d}' for i in range(blocks)) + ']\n\n'
    text += f'def pieces : List AffinePiece := piecesBlocks.flatten\ndef pieceCount : ℕ := {count}\n\n'
    text += 'def fullPieces : List AffinePiece := outsideLeft ++ pieces ++ outsideRight\n\n'
    text += '''theorem mem_pieces {p : AffinePiece} (hp : p ∈ pieces) :
    p ∈ fullPieces ∧ 0 ≤ p.left ∧ p.right ≤ 2 := by
  have hc : pieces.all (fun p => decide (0 ≤ p.left ∧ p.right ≤ 2)) = true := by
    decide +kernel
  refine ⟨?_, of_decide_eq_true ((List.all_eq_true.mp hc) p hp)⟩
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hp)))

'''
    text += 'def pieceBlock (i : ℕ) : List AffinePiece :=\n  (#[' + ', '.join(f'piecesChunk{i:03d}' for i in range(blocks)) + ']).getD i []\n\n'
    text += '''def pieceAt (i : ℕ) : AffinePiece :=
  (pieceBlock (i / 64)).getD (i % 64) ⟨0, 0, 0, 0⟩

'''
    text += f'''theorem piecesBlocks_length : piecesBlocks.length = {blocks} := by decide +kernel
theorem pieces_length : pieces.length = {count} := by decide +kernel

theorem pieceBlock_eq_getD (i : ℕ) (hi : i < {blocks}) :
    pieceBlock i = piecesBlocks.getD i [] := by
  interval_cases i <;> rfl

theorem pieceBlock_length (i : ℕ) (hi : i < {blocks}) :
    (pieceBlock i).length = if i < {blocks-1} then 64 else {last} := by
  interval_cases i <;> rfl

theorem pieceBlock_mem (i : ℕ) (hi : i < {blocks}) {{p : AffinePiece}}
    (hp : p ∈ pieceBlock i) : p ∈ pieces := by
  have hil : i < piecesBlocks.length := by simpa only [piecesBlocks_length] using hi
  have hb : pieceBlock i ∈ piecesBlocks := by
    rw [pieceBlock_eq_getD i hi, List.getD_eq_getElem piecesBlocks [] hil]
    exact List.getElem_mem hil
  exact List.mem_flatten.mpr ⟨pieceBlock i, hb, hp⟩

theorem pieceAt_mem (i : ℕ) (hi : i < {count}) : pieceAt i ∈ pieces := by
  have hb : i / 64 < {blocks} := by omega
  have hr : i % 64 < 64 := Nat.mod_lt i (by decide)
  have hdecomp := Nat.mod_add_div i 64
  have hindex : i % 64 < (pieceBlock (i / 64)).length := by
    rw [pieceBlock_length (i / 64) hb]
    split_ifs with hs
    · exact hr
    · have hlast : i / 64 = {blocks-1} := by omega
      omega
  unfold pieceAt
  rw [List.getD_eq_getElem (pieceBlock (i / 64)) ⟨0, 0, 0, 0⟩ hindex]
  exact pieceBlock_mem (i / 64) hb (List.getElem_mem hindex)
''' + ending()
    assert len(text.splitlines()) <= 10000
    (cert/'FrontierPieceData.lean').write_text(text)
    text = header(['ErdosOverlap.Certificate.FrontierPieceData', 'ErdosOverlap.Certificate.FrontierJumpBinding'])
    text += '''theorem fullPieces_eq_fast : fullPieces = compileAffinePiecesFast (-1) 3 0 0 finalJumps := by
  apply affinePiecesEqual_sound
  decide +kernel

theorem fullPieces_eq : fullPieces = compileAffinePieces (-1) 3 0 0 finalJumps := by
  rw [fullPieces_eq_fast, compileAffinePiecesFast_eq]
''' + ending()
    (cert/'FrontierAffineData.lean').write_text(text)
    native_source = (package/'ErdosOverlap/Native6AffineKernel.lean').read_text()
    body = native_source[native_source.index('/-- Exact equality away'):]
    body = body.replace('Native6Jumps', 'FrontierJumps').replace('Native6.kernel', 'Frontier.kernel')
    body = body.replace('Native6Data.y0', 'FrontierData.y0').replace('Native6Data.y2', 'FrontierData.y2')
    body = body.replace('Native6Data.periodicRows', 'FrontierData.periodicRows').replace('Native6Data.phaseRows', 'FrontierData.phaseRows')
    body = body.replace('Native6Trig.terms', 'FrontierTrig.terms')
    prefix = '''/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.FrontierAffineData
public import ErdosOverlap.FrontierKernel

namespace ErdosOverlap.FrontierJumps
open MeasureTheory Set
public section
noncomputable section

'''
    (package/'ErdosOverlap/FrontierAffineKernel.lean').write_text(prefix+body)
    (package/'certificates/frontier/affine-pieces.json').write_text(json.dumps(
        [[str(x) for x in row] for row in pieces], separators=(',', ':'))+'\n')
    print(f'Generated {periodic_count} periodic chunks, 23 phase chunks, {len(jumps)} jumps and {count} pieces.')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    generate(p.parse_args().package)
