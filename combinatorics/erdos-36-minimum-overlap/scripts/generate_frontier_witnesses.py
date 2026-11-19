"""Serialize the ten frozen nonnegative witnesses and exact cost inequalities."""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

N, DEN = 16384, 10**18


def rat(q):
    q = F(q)
    return f'({q.numerator} / {q.denominator} : ℚ)'


def generate(package):
    source = package / 'certificates/frontier/witnesses.json'
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    witnesses = json.loads(source.read_text())
    assert len(witnesses) == 10
    for mode, witness in enumerate(witnesses):
        name = f'{mode:02d}'
        nodes = [F(q) for q in witness['nodes']]
        assert len(nodes) == N+1 and nodes[0] == nodes[-1] == 0
        assert all(q >= 0 and (q*DEN).denominator == 1 for q in nodes)
        nonzero = [i for i, q in enumerate(nodes) if q]
        start = min(nonzero)
        # Retaining interior zero nodes preserves the exact same interpolant
        # and allows linear-size dense-slope checks.
        values = [int(q*DEN) for q in nodes[start:N]]
        tau, upper = F(witness['tau']), F(witness['iv_upper'])
        assert (tau*DEN).denominator == 1
        tau_numerator = int(tau*DEN)
        mass = sum(values)
        exact_cost = F(mass, N*DEN)
        assert exact_cost <= upper
        previous = 0
        slopes = []
        for value in values+[0]:
            slopes.append(2*tau_numerator+N*(value-previous))
            previous = value
        text = f'''/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.PiecewiseLinearDenseCache

/-! Frozen fully_joint32 witness {mode}; SHA-256 `{source_hash}`.
The exact tent-function cost is proved below. The rounded cost is an upper
bound, not an asserted equality with the real integral. -/

namespace ErdosOverlap.FrontierWitnesses
open MeasureTheory Set
@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def values{name} : List ℕ := [
''' + ',\n'.join(f'  {v}' for v in values) + f'''
]

def nodes{name} : List PLNode := densePLNodes {start} values{name}

theorem nodes{name}_valid : PLValid 16384 nodes{name} := by
  decide +kernel

theorem nodes{name}_mass : plMass nodes{name} = {mass} := by
  decide +kernel

def v{name} : ℝ → ℝ := plWitness 16384 1000000000000000000 nodes{name}

def tau{name} : ℚ := {rat(tau)}
def Iv{name} : ℚ := {rat(upper)}
def exactCost{name} : ℚ := {rat(exact_cost)}
def tauNumerator{name} : ℤ := {tau_numerator}

theorem exactCost{name}_le : exactCost{name} ≤ Iv{name} := by
  decide +kernel

theorem v{name}_absolutelyContinuous : AbsolutelyContinuousOnInterval v{name} 0 1 :=
  plWitness_absolutelyContinuous 16384 1000000000000000000 nodes{name}

theorem v{name}_one : v{name} 1 = 0 := plWitness_one nodes{name}_valid
theorem v{name}_zero : v{name} 0 = 0 := plWitness_zero nodes{name}_valid

theorem v{name}_integral_abs : (∫ t in (0 : ℝ)..1, |v{name} t|) = (exactCost{name} : ℝ) := by
  change (∫ t in (0 : ℝ)..1, |plWitness 16384 1000000000000000000 nodes{name} t|) = _
  rw [plWitness_integral_abs (by norm_num) (by norm_num) nodes{name}_valid, nodes{name}_mass]
  norm_num [exactCost{name}]

theorem v{name}_integral_abs_le : (∫ t in (0 : ℝ)..1, |v{name} t|) ≤ (Iv{name} : ℝ) := by
  rw [v{name}_integral_abs]
  exact_mod_cast exactCost{name}_le

def slopeCache{name} : PLSlopeCache where
  firstCell := {start-1}
  numerators := #[
''' + ',\n'.join(f'    ({v} : ℤ)' for v in slopes) + f'''
  ]

theorem slopeCache{name}_checked :
    slopeCache{name}.check 16384 nodes{name} tauNumerator{name} = true := by
  apply PLSlopeCache.check_of_dense slopeCache{name} 16384 nodes{name} tauNumerator{name} values{name}
  · rfl
  · decide +kernel

theorem slopeCache{name}_prefix : ∀ p ∈ nodes{name},
    slopeCache{name}.firstCell+1 ≤ p.index := by
  decide +kernel

theorem dualSlope{name}_before {{l r : ℝ}}
    (hr : r ≤ ({start-1} : ℝ)/16384) :
    ∀ᵐ t ∂volume.restrict (Ioo l r),
      dualSlope (tau{name} : ℝ) v{name} t = 2*(tau{name} : ℝ) := by
  exact plWitness_ae_dualSlope_before (by norm_num : 0 < 16384)
    1000000000000000000 nodes{name} slopeCache{name}.firstCell
    (tau{name} : ℝ) slopeCache{name}_prefix hr

theorem dualSlope{name}_on_leaf {{j : ℕ}} (hj : j < slopeCache{name}.numerators.size)
    {{l r : ℝ}} (hl : (((slopeCache{name}.firstCell+j : ℕ) : ℝ)/16384) ≤ l)
    (hr : r ≤ ((((slopeCache{name}.firstCell+j : ℕ) : ℝ)+1)/16384)) :
    ∀ᵐ t ∂volume.restrict (Ioo l r),
      dualSlope (tau{name} : ℝ) v{name} t = (slopeCache{name}.value 1000000000000000000 j : ℝ) := by
  have htau : (tau{name} : ℝ) = ((tauNumerator{name} : ℤ) : ℝ) / 1000000000000000000 := by
    norm_num [tauNumerator{name}, tau{name}]
  rw [htau]
  exact slopeCache{name}.ae_dualSlope_on_leaf (by norm_num : 0 < 16384)
    1000000000000000000 nodes{name} tauNumerator{name} slopeCache{name}_checked hj hl hr

end
end
end ErdosOverlap.FrontierWitnesses
'''
        output = package / f'ErdosOverlap/Certificate/FrontierWitness{name}.lean'
        assert len(text.splitlines()) <= 10000
        output.write_text(text)
        print(f'{output.name}: {len(values)} tail nodes, exact cost <= saved upper bound')

    original_slopes = (package/'ErdosOverlap/Certificate/Native6WitnessSlopes.lean').read_text()
    # Preserve the already-proved slope-leaf soundness argument verbatim,
    # changing only its family size and namespace.
    slope_check = original_slopes[original_slopes.index('/-- A small decidable leaf check'):]
    slope_check = slope_check.replace('Fin 10', 'Fin 20').replace('ErdosOverlap.Native6Witnesses', 'ErdosOverlap.FrontierWitnesses')
    text = '''/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Native6WitnessModeFacts
''' + ''.join(f'public import ErdosOverlap.Certificate.FrontierWitness{i:02d}\n' for i in range(10)) + '''
namespace ErdosOverlap.FrontierWitnesses
open MeasureTheory Set
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

'''
    for definition, typ, prefix, noncomputable in [
        ('modeWitness', 'ℝ → ℝ', 'v', True), ('modeTau', 'ℚ', 'tau', False),
        ('modeIv', 'ℚ', 'Iv', False), ('modeSlopeCache', 'PLSlopeCache', 'slopeCache', False)]:
        text += ('noncomputable ' if noncomputable else '') + f'def {definition} (mode : Fin 20) : {typ} :=\n  match mode.val with\n'
        for i in range(20):
            case = str(i) if i < 19 else '_'
            namespace = 'Native6Witnesses.' if i < 10 else ''
            text += f'  | {case} => {namespace}{prefix}{i%10:02d}\n'
        text += '\n'
    for definition, field in [('modeFirstCell', 'firstCell'), ('modeTailCells', 'numerators.size')]:
        text += f'def {definition} (mode : Fin 20) : ℕ := (modeSlopeCache mode).{field}\n\n'
    text += '''def cachedLambda (mode : Fin 20) (j : ℕ) : ℚ :=
  (modeSlopeCache mode).value 1000000000000000000 j

theorem modeWitness_absolutelyContinuous (mode : Fin 20) :
    AbsolutelyContinuousOnInterval (modeWitness mode) 0 1 := by
  fin_cases mode
''' + ''.join(f'  · exact {"Native6Witnesses." if i < 10 else ""}v{i%10:02d}_absolutelyContinuous\n' for i in range(20))
    text += '''
theorem modeWitness_one (mode : Fin 20) : modeWitness mode 1 = 0 := by
  fin_cases mode
''' + ''.join(f'  · exact {"Native6Witnesses." if i < 10 else ""}v{i%10:02d}_one\n' for i in range(20))
    text += '''
theorem modeWitness_integral_abs_le (mode : Fin 20) :
    (∫ t in (0 : ℝ)..1, |modeWitness mode t|) ≤ (modeIv mode : ℝ) := by
  fin_cases mode
''' + ''.join(f'  · exact Native6Witnesses.v{i:02d}_integral_abs.le\n' for i in range(10))
    text += ''.join(f'  · exact v{i:02d}_integral_abs_le\n' for i in range(10))
    text += '''
theorem mode_dualSlope_before (mode : Fin 20) {l r : ℝ}
    (hr : r ≤ (modeFirstCell mode : ℝ)/16384) :
    ∀ᵐ t ∂volume.restrict (Ioo l r),
      dualSlope (modeTau mode : ℝ) (modeWitness mode) t = 2*(modeTau mode : ℝ) := by
  fin_cases mode
''' + ''.join(f'  · exact {"Native6Witnesses." if i < 10 else ""}dualSlope{i%10:02d}_before hr\n' for i in range(20))
    text += '''
theorem mode_dualSlope_on_leaf (mode : Fin 20) {j : ℕ}
    (hj : j < modeTailCells mode) {l r : ℝ}
    (hl : (((modeFirstCell mode+j : ℕ) : ℝ)/16384) ≤ l)
    (hr : r ≤ ((((modeFirstCell mode+j : ℕ) : ℝ)+1)/16384)) :
    ∀ᵐ t ∂volume.restrict (Ioo l r),
      dualSlope (modeTau mode : ℝ) (modeWitness mode) t = (cachedLambda mode j : ℝ) := by
  fin_cases mode
''' + ''.join(f'  · exact {"Native6Witnesses." if i < 10 else ""}dualSlope{i%10:02d}_on_leaf hj hl hr\n' for i in range(20))
    text += '\n' + slope_check + '\nend\n'
    # slope_check closes the namespace; its public section needs one end
    # before that closure rather than after it.
    text = text.removesuffix('\nend\n').replace(
        'end ErdosOverlap.FrontierWitnesses', 'end\nend ErdosOverlap.FrontierWitnesses')
    (package/'ErdosOverlap/FrontierWitnessModeFacts.lean').write_text(text)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    generate(p.parse_args().package)
