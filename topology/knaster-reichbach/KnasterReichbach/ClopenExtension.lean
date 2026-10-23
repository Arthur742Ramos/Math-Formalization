module
public import KnasterReichbach.Cylinders
public import Mathlib.Topology.Separation.Profinite

public section
open Set

namespace KnasterReichbach

/-- Extend a clopen trace on a closed subspace to the ambient Cantor space,
while including and excluding two disjoint closed reserve sets outside it.
The reserve sets may be empty. -/
theorem extend_clopen_trace {A : Set CantorSpace} (hA : IsClosed A)
    {S : Set A} (hS : IsClopen S) {K L : Set CantorSpace}
    (hK : IsClosed K) (hL : IsClosed L)
    (hKA : K ⊆ Aᶜ) (hLA : L ⊆ Aᶜ) (hKL : Disjoint K L) :
    ∃ U : Set CantorSpace, IsClopen U ∧
      Subtype.val ⁻¹' U = S ∧ K ⊆ U ∧ Disjoint U L := by
  let Z : Set CantorSpace := Subtype.val '' S ∪ K
  let T : Set CantorSpace := Subtype.val '' Sᶜ ∪ L
  have hZ : IsClosed Z := (hA.isClosedMap_subtype_val _ hS.isClosed).union hK
  have hT : IsClosed T := (hA.isClosedMap_subtype_val _ hS.compl.isClosed).union hL
  have hZT : Disjoint Z T := by
    rw [Set.disjoint_left]
    intro x hxZ hxT
    rcases hxZ with ⟨a, ha, rfl⟩ | hxK
    · rcases hxT with ⟨b, hb, hab⟩ | hxL
      · have hab' : b = a := Subtype.ext hab
        exact hb (hab' ▸ ha)
      · exact hLA hxL a.property
    · rcases hxT with ⟨a, ha, rfl⟩ | hxL
      · exact hKA hxK a.property
      · exact Set.disjoint_left.mp hKL hxK hxL
  obtain ⟨U, hU, hZU, hUT⟩ := exists_clopen_of_closed_subset_open
    hZ hT.isOpen_compl (Set.disjoint_left.mp hZT)
  refine ⟨U, hU, ?_, fun x hx => hZU (Or.inr hx), ?_⟩
  · ext a
    constructor
    · intro ha
      by_contra hnot
      exact hUT ha (Or.inl ⟨a, hnot, rfl⟩)
    · intro ha
      exact hZU (Or.inl ⟨a, ha, rfl⟩)
  · rw [Set.disjoint_left]
    intro x hxU hxL
    exact hUT hxU (Or.inr hxL)

/-- A trace can be extended with prescribed opposite sides at two points
outside the closed subspace. Thus both ambient sides remain nonempty. -/
theorem extend_clopen_trace_with_points {A : Set CantorSpace} (hA : IsClosed A)
    {S : Set A} (hS : IsClopen S) {p q : CantorSpace}
    (hp : p ∉ A) (hq : q ∉ A) (hpq : p ≠ q) :
    ∃ U : Set CantorSpace, IsClopen U ∧ Subtype.val ⁻¹' U = S ∧ p ∈ U ∧ q ∉ U := by
  obtain ⟨U, hU, htrace, hpU, hqU⟩ := extend_clopen_trace hA hS
    (K := {p}) (L := {q}) isClosed_singleton isClosed_singleton
    (by simpa) (by simpa) (by simpa using hpq)
  exact ⟨U, hU, htrace, hpU (Set.mem_singleton p),
    fun hqmem => Set.disjoint_left.mp hqU hqmem (Set.mem_singleton q)⟩

/-- Every nonempty open set contains two distinct points outside a closed
nowhere-dense set. This is the source of the two reserve points in splitting. -/
theorem exists_two_outside {A V : Set CantorSpace} (hA : IsClosed A)
    (hn : IsNowhereDense A) (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ p q : CantorSpace, p ∈ V ∧ q ∈ V ∧ p ∉ A ∧ q ∉ A ∧ p ≠ q := by
  classical
  have hdense := (isClosed_isNowhereDense_iff_compl.mp ⟨hA, hn⟩).2
  obtain ⟨x, hxA, hxV⟩ := hdense.exists_mem_open hV hne
  obtain ⟨W, ⟨z, n, rfl⟩, hxW, hW⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).exists_subset_of_mem_open
      (show x ∈ V ∩ Aᶜ from ⟨hxV, hxA⟩)
      (hV.inter hA.isOpen_compl)
  let q : CantorSpace := Function.update z n (! z n)
  have hq : q ∈ PiNat.cylinder z n := by
    intro i hi
    exact Function.update_of_ne (Nat.ne_of_lt hi) _ _
  have hz := hW (PiNat.self_mem_cylinder z n)
  have hq' := hW hq
  refine ⟨z, q, hz.1, hq'.1, hz.2, hq'.2, ?_⟩
  intro heq
  have hn' := congrFun heq n
  simp [q] at hn'

/-- Lift a trace into a specified parent clopen, keeping both daughters
nonempty. The supplied trace must lie inside that parent. -/
theorem extend_trace_inside {A V : Set CantorSpace} (hA : IsClosed A)
    (hn : IsNowhereDense A) (hV : IsClopen V) (hne : V.Nonempty)
    {S : Set A} (hS : IsClopen S) (hSV : S ⊆ Subtype.val ⁻¹' V) :
    ∃ U : Set CantorSpace, IsClopen U ∧ U ⊆ V ∧
      Subtype.val ⁻¹' U = S ∧ U.Nonempty ∧ (V \ U).Nonempty := by
  obtain ⟨p, q, hpV, hqV, hpA, hqA, hpq⟩ := exists_two_outside hA hn hV.isOpen hne
  obtain ⟨W, hW, htrace, hpW, hqW⟩ := extend_clopen_trace_with_points hA hS hpA hqA hpq
  refine ⟨W ∩ V, hW.inter hV, Set.inter_subset_right, ?_, ⟨p, hpW, hpV⟩,
    ⟨q, hqV, fun hq => hqW hq.1⟩⟩
  ext a
  constructor
  · intro ha
    exact htrace ▸ ha.1
  · intro ha
    have haW : a ∈ Subtype.val ⁻¹' W := by rwa [htrace]
    exact ⟨haW, hSV ha⟩

/-- Match a source split by an ambient split of the target parent. Reserved
points keep both target daughters nonempty even when a prescribed trace is empty. -/
theorem match_clopen_split {A B U V P : Set CantorSpace} (h : A ≃ₜ B)
    (hB : IsClosed B) (hnB : IsNowhereDense B)
    (hV : IsClopen V) (hneV : V.Nonempty)
    (htrace : ∀ a : A, a.val ∈ U ↔ (h a).val ∈ V)
    (hP : IsClopen P) (hPU : P ⊆ U) :
    ∃ Q : Set CantorSpace, IsClopen Q ∧ Q ⊆ V ∧ Q.Nonempty ∧ (V \ Q).Nonempty ∧
      (∀ a : A, a.val ∈ P ↔ (h a).val ∈ Q) ∧
      (∀ a : A, a.val ∈ U \ P ↔ (h a).val ∈ V \ Q) := by
  let S : Set B := {b | (h.symm b).val ∈ P}
  have hS : IsClopen S := hP.preimage (continuous_subtype_val.comp h.symm.continuous)
  have hSV : S ⊆ Subtype.val ⁻¹' V := by
    intro b hb
    have hv := (htrace (h.symm b)).mp (hPU hb)
    simpa using hv
  obtain ⟨Q, hQ, hQV, hQS, hQne, hdiff⟩ := extend_trace_inside hB hnB hV hneV hS hSV
  have hmatch (a : A) : a.val ∈ P ↔ (h a).val ∈ Q := by
    have hh : (h a) ∈ Subtype.val ⁻¹' Q ↔ h a ∈ S := by rw [hQS]
    simpa [S] using hh.symm
  refine ⟨Q, hQ, hQV, hQne, hdiff, hmatch, ?_⟩
  intro a
  exact and_congr (htrace a) (not_congr (hmatch a))

end KnasterReichbach
