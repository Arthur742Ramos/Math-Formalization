module

public import TupleMeans
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical
variable {V I : Type*} [Fintype I]

@[expose] noncomputable def groupExpectation (G : SimpleGraph V) (len : I → ℕ)
    (pool : (i : I) → Fin (len i) → Finset V) (x : V) :=
  ∑ i, mean (fun P : tupleSpace (List.ofFn (pool i)) => (tupleDegree (adj G) x P:ℝ))

theorem indicator_spectral (G : SimpleGraph V) (B T U : Finset V) (p ε : ℝ) (tB : T ⊆ B)
    (uB : U ⊆ B) (op : SpectralBound G B p ε) :
    ∑ x ∈ T, (∑ y ∈ U, centered G p x y)^2 ≤ (ε*B.card)^2*U.card := by
  classical
  let v (y : V) : ℝ := if y ∈ U then 1 else 0
  have eq : B.filter (· ∈ U) = U := by ext x; simp; exact fun h => uB h
  have form (x : V) : (∑ y ∈ B, centered G p x y*v y) = ∑ y ∈ U, centered G p x y := by
    simp only [v,mul_ite,mul_one,mul_zero,←sum_filter,eq]
  have norm : (∑ y ∈ B, v y^2) = U.card := by simp [v,ite_pow,inter_eq_right.mpr uB]
  have h := op v
  change (∑ x ∈ B, (∑ y ∈ B, centered G p x y*v y)^2) ≤ _ at h
  simp only [form,norm] at h
  exact (sum_le_sum_of_subset_of_nonneg tB fun _ _ _ => sq_nonneg _).trans h

/-- Equal-sized disjoint pools turn the sum of the positional biases into the
centered degree of a single union. This controls all but a small fraction of
test labels without choosing the partition by a concentration inequality. -/
theorem group_bias (G : SimpleGraph V) (B T : Finset V) (p ε : ℝ) (tB : T ⊆ B)
    (op : SpectralBound G B p ε) (len : I → ℕ) (pool : (i : I) → Fin (len i) → Finset V)
    (b : ℕ) (hb : 0 < b) (sz : ∀ i k, (pool i k).card=b) (sub : ∀ i k, pool i k ⊆ B)
    (dis : ∀ a c : (i : I) × Fin (len i), a ≠ c → Disjoint (pool a.1 a.2) (pool c.1 c.2)) :
    ∑ x ∈ T, ((b:ℝ)*(groupExpectation G len pool x-p*(∑ i, len i)))^2 ≤
      (ε*B.card)^2*((∑ i, len i)*b:ℕ) := by
  classical
  let P (a : (i : I) × Fin (len i)) := pool a.1 a.2
  let U := univ.biUnion P
  have dj : ((univ : Finset ((i : I) × Fin (len i))) : Set _).PairwiseDisjoint P :=
    fun a _ c _ ne => dis a c ne
  have uB : U ⊆ B := by
    intro x hx
    obtain ⟨a,_,m⟩ := mem_biUnion.mp hx
    exact sub _ _ m
  have ucard : U.card = (∑ i, len i)*b := by
    rw [card_biUnion dj]
    simp [P,sz,Fintype.card_sigma]
  have en (i) : (tupleSpace (List.ofFn (pool i))).Nonempty := by
    apply tuples_nonempty
    intro X hx
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hx
    exact card_pos.mp ((sz i k).symm ▸ hb)
  have eq (x : V) : (b:ℝ)*(groupExpectation G len pool x-p*(∑ i, len i)) = ∑ y ∈ U, centered G p x y := by
    rw [sum_biUnion dj,Fintype.sum_sigma]
    unfold groupExpectation
    simp only [mean_tuple_degree G x _ (en _),List.map_ofFn,List.sum_ofFn,Function.comp_apply,Nat.cast_sum,mul_sum,mul_sub,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    have h := sum_congr (s₁:=(univ:Finset (Fin (len i)))) rfl (fun k _ => pool_mean G p x (pool i k) b (sz i k) hb)
    simpa only [P,mul_sub,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_left_comm,mul_comm,mul_assoc] using h
  simp_rw [eq]
  rw [← ucard]
  exact indicator_spectral G B T U p ε tB uB op

end InducedDegreeRepetition.Sampling
