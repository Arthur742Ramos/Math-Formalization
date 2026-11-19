module

public import BoundedEdgeRegularSubgraphs.Incidence
import Mathlib.Tactic

/-!
# The edge set incident to a vertex
-/

@[expose] public section

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [LinearOrder α]

/-- Edges incident to `i` inside the available edge set. -/
def incidentEdges (A : Finset (Edge α)) (i : α) : Finset (Edge α) :=
  A.filter (fun e ↦ e.val.1 = i ∨ e.val.2 = i)

/-- The endpoint of an incident edge distinct from `i`. -/
def otherEndpoint (i : α) (e : Edge α) : α := if e.val.1 = i then e.val.2 else e.val.1

theorem otherEndpoint_ne {A : Finset (Edge α)} {i : α} {e : Edge α}
    (he : e ∈ incidentEdges A i) : otherEndpoint i e ≠ i := by
  rcases (Finset.mem_filter.mp he).2 with h | h
  · simpa [otherEndpoint, h] using e.property.ne.symm
  · have h' : e.val.1 ≠ i := h ▸ e.property.ne
    simp [otherEndpoint, h']

theorem incident_endpoint_sum {G : Type*} [AddCommMonoid G] {A : Finset (Edge α)}
    {i : α} {e : Edge α} (he : e ∈ incidentEdges A i) (t : α → G) :
    t e.val.1 + t e.val.2 = t i + t (otherEndpoint i e) := by
  rcases (Finset.mem_filter.mp he).2 with h | h
  · simp [otherEndpoint, h]
  · have h' : e.val.1 ≠ i := h ▸ e.property.ne
    simp [otherEndpoint, h, h', add_comm]

private def edgeBetween (i j : α) (h : i ≠ j) : Edge α :=
  ⟨(min i j, max i j), min_lt_max.mpr h⟩

private theorem edgeBetween_incident (i j : α) (h : i ≠ j) :
    (edgeBetween i j h).val.1 = i ∨ (edgeBetween i j h).val.2 = i := by
  rcases le_total i j with h' | h'
  · exact Or.inl (min_eq_left h')
  · exact Or.inr (max_eq_left h')

private theorem otherEndpoint_edgeBetween (i j : α) (h : i ≠ j) :
    otherEndpoint i (edgeBetween i j h) = j := by
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [otherEndpoint, edgeBetween, min_eq_left h'.le, max_eq_right h'.le]
  · simp [otherEndpoint, edgeBetween, min_eq_right h'.le, max_eq_left h'.le, h'.ne]

theorem otherEndpoint_injOn (A : Finset (Edge α)) (i : α) :
    Set.InjOn (otherEndpoint i) (incidentEdges A i : Set (Edge α)) := by
  intro e he f hf hef
  apply Subtype.ext
  have hrecover (a : Edge α) (ha : a ∈ incidentEdges A i) :
      (min i (otherEndpoint i a), max i (otherEndpoint i a)) = a.val := by
    rcases (Finset.mem_filter.mp ha).2 with h | h
    · have hh : i ≤ a.val.2 := h ▸ a.property.le
      rw [otherEndpoint, ite_eq_left h, min_eq_left hh, max_eq_right hh]
      exact Prod.ext h.symm rfl
    · have hh : a.val.1 < i := h ▸ a.property
      rw [otherEndpoint, ite_eq_right hh.ne, min_eq_right hh.le, max_eq_left hh.le]
      exact Prod.ext rfl h.symm
  rw [← hrecover e he, ← hrecover f hf, hef]

variable [Fintype α]

/-- The number of available incident edges into the good coordinates is
at least the number of good coordinates outside the deleted clique. -/
theorem good_incidentEdges_card_ge (S G : Finset α) {i : α} (hi : i ∉ G) :
    (G \ S).card ≤ ((incidentEdges (edgesOutsideOverlap S) i).filter
      (fun e ↦ otherEndpoint i e ∈ G)).card := by
  classical
  let B := G \ S
  let g (j : B) : Edge α := edgeBetween i j.val
    (fun h ↦ hi (by simpa only [h] using (Finset.mem_sdiff.mp j.property).1))
  have hinj : Function.Injective g := by
    intro j k h
    apply Subtype.ext
    simpa only [g, otherEndpoint_edgeBetween] using congrArg (otherEndpoint i) h
  change B.card ≤ _
  rw [← Finset.card_attach (s := B)]
  apply Finset.card_le_card_of_injOn g _ hinj.injOn
  intro j _
  obtain ⟨hjG, hjS⟩ := Finset.mem_sdiff.mp j.property
  have hne : i ≠ j.val := fun h ↦ hi (by simpa only [h] using hjG)
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, edgeBetween_incident i j hne⟩, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases le_total i j.val with h | h
    · change ¬ (min i j.val ∈ S ∧ max i j.val ∈ S)
      rw [max_eq_right h]
      exact fun hx ↦ hjS hx.2
    · change ¬ (min i j.val ∈ S ∧ max i j.val ∈ S)
      rw [min_eq_right h]
      exact fun hx ↦ hjS hx.1
  · exact (otherEndpoint_edgeBetween i j hne).symm ▸ hjG

/-- The exceptional incident edges inject into the other exceptional coordinates. -/
theorem exceptional_incidentEdges_card_le (A : Finset (Edge α)) (G : Finset α) (i : α) :
    ((incidentEdges A i).filter (fun e ↦ otherEndpoint i e ∉ G)).card ≤
      (((Finset.univ : Finset α) \ G).erase i).card := by
  apply Finset.card_le_card_of_injOn (otherEndpoint i)
  · intro e he
    obtain ⟨heA, heG⟩ := Finset.mem_filter.mp he
    exact Finset.mem_erase.mpr ⟨otherEndpoint_ne heA, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, heG⟩⟩
  · exact (otherEndpoint_injOn A i).mono (Finset.filter_subset _ _)

end BoundedEdgeRegularSubgraphs
