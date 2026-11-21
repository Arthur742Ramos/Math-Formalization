module

public import ReferenceErrors
public import MeanMarginals
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical
variable {V I : Type*} [Fintype I] [DecidableEq I]

/-- The tester and the reference tuples are independent before parity selection.
The variance term is linear in the number of tuples. The pool bias is estimated
in mean square over the tester population. -/
theorem group_deviation (G : SimpleGraph V) (p ε : ℝ) (B T : Finset V) (tB : T ⊆ B)
    (tn : T.Nonempty) (op : SpectralBound G B p ε) (L : ℕ) (len : I → ℕ) (cap : ∀ i, len i ≤ L)
    (pool : (i : I) → Fin (len i) → Finset V) (b : ℕ) (hb : 0 < b)
    (sz : ∀ i k, (pool i k).card=b) (sub : ∀ i k, pool i k ⊆ B)
    (dis : ∀ a c : (i : I) × Fin (len i), a ≠ c → Disjoint (pool a.1 a.2) (pool c.1 c.2))
    [∀ i, Nonempty ↥(tupleSpace (List.ofFn (pool i)))] :
    mean (fun y : T => mean (fun ref : ∀ i, tupleSpace (List.ofFn (pool i)) =>
      ((∑ i, (tupleDegree (adj G) y (ref i):ℝ))-p*(∑ i, len i))^2)) ≤
      2*Fintype.card I*L^2+2*(ε*B.card)^2*(∑ i, len i)/((b:ℝ)*T.card) := by
  classical
  let : Nonempty T := tn.to_subtype
  let μ := fun y => groupExpectation G len pool y-p*(∑ i, len i)
  let m : ℕ := ∑ i, len i
  have spectral := group_bias G B T p ε tB op len pool b hb sz sub dis
  change (∑ x ∈ T, ((b:ℝ)*μ x)^2) ≤ (ε*B.card)^2*((m*b:ℕ):ℝ) at spectral
  simp only [mul_pow,← mul_sum,Nat.cast_mul] at spectral
  have tb : (0:ℝ)<T.card := by exact_mod_cast card_pos.mpr tn
  have bb : (0:ℝ)<b := by exact_mod_cast hb
  have bias : mean (fun y : T => μ y^2) ≤ (ε*B.card)^2*m/((b:ℝ)*T.card) := by
    rw [mean_over_pool T (fun y => μ y^2),div_le_div_iff₀ tb (mul_pos bb tb)]
    have s : (b:ℝ)*(∑ x ∈ T, μ x^2) ≤ (ε*B.card)^2*m := by
      apply le_of_mul_le_mul_right (a:=(b:ℝ)) _ bb
      nlinarith only [spectral]
    nlinarith only [mul_le_mul_of_nonneg_right s tb.le]
  have h := mean_le _ _ fun y : T => reference_error G y p L len pool cap
  apply h.trans
  rw [mean_add,mean_const,mean_smul]
  change 2*(Fintype.card I:ℝ)*L^2+2*mean (fun y : T => μ y^2) ≤ _
  apply add_le_add_right
  convert mul_le_mul_of_nonneg_left bias (by norm_num : (0:ℝ)≤2) using 1; push_cast [m]; ring

end InducedDegreeRepetition.Sampling
