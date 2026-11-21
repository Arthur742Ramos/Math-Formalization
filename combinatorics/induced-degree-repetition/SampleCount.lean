module

public import SamplingMoment
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Prod

public section
namespace InducedDegreeRepetition.Restriction

open Finset
open scoped Classical
variable {X Y I J : Type*} [Fintype X] [Fintype Y] [Fintype I] [Fintype J]

@[expose] noncomputable def common (ok : X → Y → Prop) (V : Finset Y) (xs : I → X) : Finset Y :=
  V.filter fun y => ∀ i, ok (xs i) y

omit [Fintype Y] in
theorem moment_sum (ok : X → Y → Prop) (V : Finset Y) (k m : ℕ) :
    (∑ xs : Fin k → X, ((common ok V xs).card:ℝ)^m) = moment ok m k V := by
  classical
  induction k generalizing V with
  | zero => simp [common,moment]
  | succ k ih =>
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1) => X)) (fun xs => ((common ok V xs).card:ℝ)^m),
      Fintype.sum_prod_type]
    apply sum_congr rfl
    intro x _
    rw [← ih]
    apply sum_congr rfl
    intro xs _
    have h : common ok V (Fin.cons x xs) = common ok (V.filter (ok x)) xs := by
      ext y
      simp only [common,mem_filter,Fin.forall_fin_succ,Fin.cons_zero,Fin.cons_succ]
      tauto
    simp [Fin.consEquiv,h]

variable (I J) in
/-- Count ordered row and column lists which agree at every tested matrix entry. -/
@[expose] noncomputable def samples (ok : X → Y → Prop) : ℝ :=
  ∑ xs : I → X, ∑ ys : J → Y, if ∀ i j, ok (xs i) (ys j) then 1 else 0

theorem samples_moment (ok : X → Y → Prop) :
    samples I J ok = moment ok (Fintype.card J) (Fintype.card I) univ := by
  classical
  have eh (xs : I → X) :
      (∑ ys : J → Y, if ∀ i j, ok (xs i) (ys j) then (1:ℝ) else 0) =
        ((common ok univ xs).card : ℝ)^Fintype.card J := by
    have h (ys : J → Y) : (∀ i j, ok (xs i) (ys j)) ↔ ys ∈ Fintype.piFinset (fun _ => common ok univ xs) := by
      simp only [Fintype.mem_piFinset,common,mem_filter,mem_univ,true_and]
      exact forall_comm
    simp only [h,sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul,mul_one,Fintype.card_piFinset,
      prod_const,card_univ,Nat.cast_pow]
  unfold samples
  simp_rw [eh]
  rw [← moment_sum]
  let e := Fintype.equivFin I
  let E : (I → X) ≃ (Fin (Fintype.card I) → X) := Equiv.arrowCongr e (Equiv.refl X)
  apply Fintype.sum_equiv E
  intro xs
  have h : common ok univ xs = common ok univ (E xs) := by
    ext y
    simp only [common,mem_filter,mem_univ,true_and]
    constructor
    · intro all j
      exact all (e.symm j)
    · intro all i
      simpa [E] using all (e i)
  rw [h]

end InducedDegreeRepetition.Restriction
