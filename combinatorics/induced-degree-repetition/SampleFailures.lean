module

public import EditSampling
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Edit

open Finset
open scoped Classical
variable {X V : Type*}

theorem some_failure {n : ℕ} (T : Finset X) (p : Fin n → X → Prop) (a : ℝ) (nn : 0 ≤ a)
    (each : ∀ i, ((T.filter (p i)).card:ℝ) ≤ a) :
    ((T.filter fun x => ∃ i, p i x).card:ℝ) ≤ n*a := by
  classical
  have h := Residues.union_bad_lists (univ : Finset (Fin n)).toList T p a nn (fun i _ => each i)
  convert h using 1
  · apply congrArg Nat.cast
    apply congrArg Finset.card
    ext x
    simp
  · simp

/-- Uniform local failure estimates for a tuple with fixed labels, and for the
fresh labels with fixed references, can be combined under the actual product draw. -/
theorem simultaneous_sample_bound {n : ℕ} (pools : Fin n → Finset X) (T : Finset V)
    (f g : Fin n → X → V → Prop) (ok : (Fin n → X) → V → Prop) (a b : ℝ) (ap : 0 ≤ a) (bp : 0 ≤ b)
    (references : ∀ i y, y ∈ T → (((pools i).filter fun x => f i x y).card:ℝ) ≤ a*(pools i).card)
    (labels : ∀ i x, x ∈ pools i → ((T.filter (g i x)).card:ℝ) ≤ b*T.card)
    (suffices_ok : ∀ x ∈ Fintype.piFinset pools, ∀ y ∈ T,
      (∀ i, ¬f i (x i) y) → (∀ i, ¬g i (x i) y) → ok x y) :
    ((((Fintype.piFinset pools) ×ˢ T).filter fun z => ¬ok z.1 z.2).card:ℝ) ≤
      n*(a+b)*((Fintype.piFinset pools) ×ˢ T).card := by
  classical
  let R := Fintype.piFinset pools
  let p (x : Fin n → X) (y : V) := ∃ i, f i (x i) y
  let q (x : Fin n → X) (y : V) := ∃ i, g i (x i) y
  have init (y : V) (hy : y ∈ T) : ((R.filter fun x => p x y).card:ℝ) ≤ (n*a)*R.card := by
    rw [mul_assoc]
    apply some_failure R (fun i x => f i (x i) y) _ (mul_nonneg ap (Nat.cast_nonneg _))
    intro i
    exact coordinate_bad pools i (fun x => f i x y) a (references i y hy)
  have rows (x : Fin n → X) (hx : x ∈ R) : ((T.filter fun y => q x y).card:ℝ) ≤ (n*b)*T.card := by
    rw [mul_assoc]
    exact some_failure T (fun i y => g i (x i) y) _ (mul_nonneg bp (Nat.cast_nonneg _))
      (fun i => labels i (x i) (Fintype.mem_piFinset.mp hx i))
  have ub := product_failures R T p q (n*a) (n*b) (by
    intro y hy
    convert init y hy using 1
    apply congrArg Nat.cast
    apply congrArg Finset.card
    ext x
    simp) (by
    intro x hx
    convert rows x hx using 1
    apply congrArg Nat.cast
    apply congrArg Finset.card
    ext y
    simp)
  have sub : ((R ×ˢ T).filter fun z => ¬ok z.1 z.2) ⊆ ((R ×ˢ T).filter fun z => p z.1 z.2 ∨ q z.1 z.2) := by
    intro z hz
    obtain ⟨ht,no⟩ := mem_filter.mp hz
    refine mem_filter.mpr ⟨ht,?_⟩
    by_contra! none
    exact no (suffices_ok z.1 (mem_product.mp ht).1 z.2 (mem_product.mp ht).2
      (fun i h => none.1 ⟨i,h⟩) (fun i h => none.2 ⟨i,h⟩))
  rw [mul_add]
  apply (Nat.cast_le.mpr (card_le_card sub)).trans
  convert ub using 1
  apply congrArg Nat.cast
  apply congrArg Finset.card
  ext z
  simp

end InducedDegreeRepetition.Edit
