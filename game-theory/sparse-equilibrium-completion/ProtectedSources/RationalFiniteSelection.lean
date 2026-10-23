/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalInitializedAlgorithm
public import Mathlib.Data.List.MinMax
@[expose] public section
namespace SparseCompletion

def rationalFiniteSelect {α β : Type*} (candidates : List α)
    (run : α → Option β) (score : β → ℚ) : Option β :=
  (candidates.filterMap run).argmin score

theorem rational_finite_select_origin {α β : Type*} (candidates : List α)
    (run : α → Option β) (score : β → ℚ) (o : β)
    (hout : rationalFiniteSelect candidates run score=some o) :
    ∃ a ∈ candidates, run a=some o := by
  have hm : o ∈ (candidates.filterMap run).argmin score := hout
  exact List.mem_filterMap.mp (List.argmin_mem hm)

theorem rational_finite_select_minimal {α β : Type*} (candidates : List α)
    (run : α → Option β) (score : β → ℚ) (o : β)
    (hout : rationalFiniteSelect candidates run score=some o)
    (a : α) (ha : a ∈ candidates) (b : β) (hb : run a=some b) : score o ≤ score b := by
  have hm : o ∈ (candidates.filterMap run).argmin score := hout
  exact List.le_of_mem_argmin (List.mem_filterMap.mpr ⟨a,ha,hb⟩) hm

theorem rational_finite_select_none_iff {α β : Type*} (candidates : List α)
    (run : α → Option β) (score : β → ℚ) :
    rationalFiniteSelect candidates run score=none ↔ ∀ a ∈ candidates, run a=none := by
  rw [rationalFiniteSelect,List.argmin_eq_none]
  constructor
  · intro he a ha
    cases hr : run a with
    | none => rfl
    | some b =>
      have hm : b ∈ candidates.filterMap run := List.mem_filterMap.mpr ⟨a,ha,hr⟩
      rw [he] at hm
      cases hm
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro b hb
    obtain ⟨a,ha,hb⟩ := List.mem_filterMap.mp hb
    rw [h a ha] at hb
    cases hb

end SparseCompletion
