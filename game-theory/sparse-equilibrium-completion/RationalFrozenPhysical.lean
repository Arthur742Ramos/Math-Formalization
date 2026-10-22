/- AI-assisted formalization under the repository Apache-2.0 license.
After rational K,D recovery, physical constraints become linear in q. -/
module
public import RationalIntervalRepertoireSolver
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalFrozenCoefficient {k m : ℕ} (D : Fin m → Fin k → ℚ)
    (j : Fin (m+(m*k+(k*k+0*m)))) (i : Fin m) : ℚ :=
  Sum.elim (fun a => if i=a then 1 else 0)
    (Sum.elim (fun a => if i=a.1 then D a.1 a.2 else 0)
      (Sum.elim (fun _ => 0) (fun a => Fin.elim0 a.1)))
    ((rationalIntervalVariableEquiv k m 0).symm j)

def rationalFrozenConstant {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (j : Fin (m+(m*k+(k*k+0*m)))) : ℚ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
    (Sum.elim (fun a => K a.1 a.2) (fun a => Fin.elim0 a.1)))
    ((rationalIntervalVariableEquiv k m 0).symm j)

theorem rational_frozen_physical_eval {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (q : Fin m → ℚ)
    (j : Fin (m+(m*k+(k*k+0*m)))) :
    (∑ i, rationalFrozenCoefficient D j i*q i)+rationalFrozenConstant K j=
      intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0 j := by
  unfold rationalFrozenCoefficient rationalFrozenConstant intervalPack intervalVariableEncode
  generalize (rationalIntervalVariableEquiv k m 0).symm j=v
  rcases v with a | v
  · simp only [Sum.elim_inl,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',
      Finset.mem_univ,ite_true,add_zero]
  · rcases v with a | v
    · simp only [Sum.elim_inr,Sum.elim_inl,ite_mul,zero_mul,Finset.sum_ite_eq',
        Finset.mem_univ,ite_true,add_zero]
      exact mul_comm _ _
    · rcases v with a | a
      · simp only [Sum.elim_inr,Sum.elim_inl,zero_mul,Finset.sum_const_zero,zero_add]
      · exact Fin.elim0 a.1

def rationalFrozenPhysicalSystem {k m : ℕ} {I : Type*}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) : RationalLinearSystem I m where
  coefficient := fun a i => ∑ j, R.coefficient a j*rationalFrozenCoefficient D j i
  rightSide := fun a => R.rightSide a-∑ j, R.coefficient a j*rationalFrozenConstant K j

theorem rational_frozen_physical_system_iff {k m : ℕ} {I : Type*}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (q : Fin m → ℚ) :
    (rationalFrozenPhysicalSystem K D R).Satisfies q ↔
      R.Satisfies (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0) := by
  have he (a : I) : (∑ i, (∑ j, R.coefficient a j*rationalFrozenCoefficient D j i)*q i)+
      (∑ j, R.coefficient a j*rationalFrozenConstant K j)=
      ∑ j, R.coefficient a j*intervalPack q (fun i b => q i*D i b) K (H := 0) Fin.elim0 j := by
    simp_rw [←rational_frozen_physical_eval K D q,mul_add,Finset.sum_add_distrib,
      Finset.sum_mul,Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm]
  change (∀ a, (∑ i, (∑ j, R.coefficient a j*rationalFrozenCoefficient D j i)*q i) ≤
    R.rightSide a-(∑ j, R.coefficient a j*rationalFrozenConstant K j)) ↔ _
  constructor
  · intro h a
    rw [←he a]
    linarith [h a]
  · intro h a
    have hh := h a
    rw [←he a] at hh
    linarith

end SparseCompletion
