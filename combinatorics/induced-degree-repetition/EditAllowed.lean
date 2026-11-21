module

public import AdjustmentWitnesses
public import Adjustment
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Edit

open Finset
open scoped Classical
variable {X J : Type*} [DecidableEq J]

theorem atom_allowed (S : Finset X) (d : X → J → ℕ) (len : ℕ) (s : J → ℤ) (j : J)
    (w : ℝ) (hw : 0 < w) (bound : ∀ x ∈ S, ∀ j, d x j ≤ len)
    (nonempty : (otherFiber S (fun x k => (d x k:ℤ)) s j).Nonempty)
    (v : ℕ) (atom : w*(otherFiber S (fun x k => (d x k:ℤ)) s j).card ≤
      (((otherFiber S (fun x k => (d x k:ℤ)) s j).filter (fun x => d x j=v)).card:ℝ)) :
    (v:ℤ) ∈ allowedCounts len w S (fun x k => (d x k:ℤ)) s j := by
  classical
  let other := otherFiber S (fun x k => (d x k:ℤ)) s j
  have positive : 0 < (other.filter fun x => d x j=v).card := by
    exact_mod_cast (mul_pos hw (show (0:ℝ) < other.card by exact_mod_cast card_pos.mpr nonempty)).trans_le atom
  obtain ⟨x,hx⟩ := card_pos.mp positive
  have h := mem_filter.mp hx
  have memS : x ∈ S := (mem_filter.mp h.1).1
  have vle := h.2 ▸ bound x memS j
  have eq : other.filter (fun x => d x j=v) = profileFiber S (fun x k => (d x k:ℤ)) (Function.update s j v) := by
    ext x
    simp only [other,otherFiber,profileFiber,mem_filter]
    constructor
    · rintro ⟨⟨h,rest⟩,atj⟩
      refine ⟨h,funext fun k => ?_⟩
      by_cases e : k=j
      · subst k; simp [atj]
      · simpa [e] using rest k e
    · rintro ⟨h,eq⟩
      refine ⟨⟨h,fun k e => ?_⟩,?_⟩
      · simpa [e] using congrFun eq k
      · exact_mod_cast (by simpa using congrFun eq j : (d x j:ℤ) = (v:ℤ))
  apply mem_filter.mpr
  refine ⟨mem_Icc.mpr ⟨by positivity,by exact_mod_cast vle⟩,?_⟩
  rw [← eq]
  exact atom

/-- Translate row witnesses on the subfamily with all other coordinates fixed
into extrema and arithmetic conditions on the allowed integer counts. -/
theorem allowed_tests (S : Finset X) (d : X → J → ℕ) (len L₀ : ℕ) (w θ : ℝ)
    (hw : 0 < w) (hl : 0 < len) (hθ : θ < 1/2)
    (bound : ∀ x ∈ S, ∀ j, d x j ≤ len) (s : J → ℤ) (j : J)
    (hn : (otherFiber S (fun x k => (d x k:ℤ)) s j).Nonempty)
    (range : Witnesses (otherFiber S (fun x k => (d x k:ℤ)) s j) (fun x => d x j) len θ w none)
    (mods : len ≠ L₀ → ∀ q, TestModulus L₀ q →
      Witnesses (otherFiber S (fun x k => (d x k:ℤ)) s j) (fun x => d x j) len θ w (some q)) :
    let T := allowedCounts len w S (fun x k => (d x k:ℤ)) s j
    T.Nonempty ∧ low T ≤ ⌊θ*len/5⌋ ∧ ⌈(1-θ/5)*len⌉ ≤ high T ∧
    (len = L₀ → 1 < T.card ∧ T ⊆ Icc 0 (L₀:ℤ)) ∧
    (len ≠ L₀ → ∀ q, TestModulus L₀ q → ∃ x ∈ T, ∃ y ∈ T, ¬ (q:ℤ) ∣ x-y) := by
  classical
  let T := allowedCounts len w S (fun x k => (d x k:ℤ)) s j
  obtain ⟨k,l,⟨low',high'⟩,ka,la⟩ := range
  have inT := atom_allowed S d len s j w hw bound hn
  have kT := inT k ka
  have lT := inT l la
  have ne : T.Nonempty := ⟨_,kT⟩
  refine ⟨ne,?_,?_,?_,?_⟩
  · exact (by simpa [low,ne] using T.min'_le _ kT : low T ≤ k).trans (Int.le_floor.mpr (by exact_mod_cast low'))
  · exact (Int.ceil_le.mpr (by exact_mod_cast high') : ⌈(1-θ/5)*len⌉ ≤ (l:ℤ)).trans
      (by simpa [high,ne] using T.le_max' _ lT : (l:ℤ) ≤ high T)
  · rintro rfl
    refine ⟨one_lt_card.mpr ⟨_,kT,_,lT,?_⟩,filter_subset ..⟩
    have sep : (k:ℝ) < l := by nlinarith [mul_lt_mul_of_pos_right hθ (show (0:ℝ)<len by exact_mod_cast hl)]
    exact_mod_cast sep.ne
  · intro diff q hq
    obtain ⟨x,y,neq,hx,hy⟩ := mods diff q hq
    exact ⟨_,inT y hy,_,inT x hx,fun dvd => neq (Nat.modEq_iff_dvd.mpr dvd)⟩

end InducedDegreeRepetition.Edit
