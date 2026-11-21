module

public import RegularBlocks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition

open Finset OpenProblems
open scoped Classical

/-- A deficient colour on X × Y produces a homogeneous s-block in X with a large
common neighbourhood of the opposite colour in Y. The inequality is the full
finite sampling budget, before choosing parameters as functions of the graph order. -/
theorem dense_cut_step {V : Type*} (G : SimpleGraph V) (X Y : Finset V) (s t : ℕ) (b : Bool)
    (τ ρ : ℝ) (hτ : 0 < τ) (htwo : 2*τ ≤ 1) (hρ : 0 ≤ ρ) (hs : 0 < s) (ypos : Y.Nonempty)
    (few : (∑ x ∈ X, ((Y.filter fun y => adj G x y = b).card : ℝ)) < τ*X.card*Y.card)
    (budget : (4:ℝ)^(s-1) + (X.card : ℝ)^s * ρ^t < (X.card : ℝ)/2 * (1-2*τ)^t) :
    ∃ (A : SavedBlock V) (Y' : Finset V), A.vertices ⊆ X ∧ A.vertices.card = s ∧
      Homogeneous G (A.inner = true) A.vertices ∧ Y' ⊆ Y ∧ ρ*Y.card ≤ Y'.card ∧
      ∀ x ∈ A.vertices, ∀ y ∈ Y', adj G x y = A.outer := by
  classical
  let bad := fun x => Y.filter fun y => adj G x y = b
  let H := X.filter fun x => ((bad x).card : ℝ) ≤ 2*τ*Y.card
  let E := X \ H
  have y : (0:ℝ) < Y.card := by exact_mod_cast card_pos.mpr ypos
  have high : (X.card : ℝ)/2 ≤ H.card := by
    have total : (E.card : ℝ)*(2*τ*Y.card) ≤ ∑ x ∈ X, ((bad x).card : ℝ) := by
      calc
        _ = ∑ _ ∈ E, 2*τ*Y.card := by simp
        _ ≤ ∑ x ∈ E, ((bad x).card : ℝ) := sum_le_sum fun x hx => by
          obtain ⟨hX,hH⟩ := mem_sdiff.mp (show x ∈ E from hx)
          exact (lt_of_not_ge fun h => hH (mem_filter.mpr ⟨hX,h⟩)).le
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => Nat.cast_nonneg _)
    have hE : (2:ℝ)*E.card ≤ X.card := by
      apply le_of_mul_le_mul_right (a := τ*(Y.card:ℝ)) _ (by positivity)
      nlinarith [total.trans_lt few]
    have part : (E.card : ℝ) + H.card = X.card := by
      dsimp [E]; exact_mod_cast card_sdiff_add_card_eq_card (filter_subset (s := X) _)
    linarith
  let R := fun x y => adj G x y ≠ b
  let (x y : V) : Decidable (R x y) := Classical.propDecidable _
  have d : 0 ≤ 1-2*τ := by linarith
  have degree (x) (hx : x ∈ H) : (1-2*τ)*Y.card ≤ ((Y.filter (R x)).card : ℝ) := by
    have tot : ((bad x).card : ℝ) + (Y.filter (R x)).card = Y.card := by
      exact_mod_cast card_filter_add_card_filter_not (s := Y) (fun y => adj G x y = b)
    have bound := (mem_filter.mp (show x ∈ H from hx)).2
    linarith
  have bound : ((4^(s-1):ℕ):ℝ) + (H.card : ℝ)^s * ρ^t < H.card * (1-2*τ)^t := by
    push_cast
    apply lt_of_le_of_lt _ (budget.trans_le (mul_le_mul_of_nonneg_right high (pow_nonneg d t)))
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hρ t)
    exact_mod_cast Nat.pow_le_pow_left (card_le_card (filter_subset ..)) s
  obtain ⟨T,hT,hcount,common⟩ := dependent_choice H Y R s t (4^(s-1)) hs ypos _ ρ d hρ degree bound
  obtain ⟨S,hST,hsize,hom⟩ := ramsey_colored_witness G _ T hcount
  have sz : S.card = s := by omega
  let Z := Y.filter fun y => ∀ x ∈ S, R x y
  have cross (x) (hx : x ∈ S) (y) (hy : y ∈ Z) : adj G x y = !b := by
    have z := (mem_filter.mp hy).2 x hx
    dsimp [R] at z
    exact Bool.eq_not_of_ne z
  have useBlock (i : Bool) (h : Homogeneous G (i = true) S) :
      ∃ (A : SavedBlock V) (Y' : Finset V), A.vertices ⊆ X ∧ A.vertices.card = s ∧
        Homogeneous G (A.inner = true) A.vertices ∧ Y' ⊆ Y ∧ ρ*Y.card ≤ Y'.card ∧
        ∀ x ∈ A.vertices, ∀ y ∈ Y', adj G x y = A.outer :=
    ⟨⟨S,i,!b⟩,Z,hST.trans (hT.trans (filter_subset ..)),sz,h,filter_subset ..,common S hST sz,cross⟩
  rcases hom with pos | neg
  · exact useBlock true (by simpa using pos)
  · exact useBlock false (by simpa using neg)

end InducedDegreeRepetition
