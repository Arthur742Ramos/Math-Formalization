module
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.GDelta.Basic

/-!
Cylinder foundations for the Knaster–Reichbach construction.
The complete ambient extension theorem is proved in Extension.lean.
-/

public section

namespace KnasterReichbach

abbrev CantorSpace := ℕ → Bool

/-- A cylinder meeting another cylinder of no greater depth lies inside it. -/
theorem cylinder_subset_of_mem {x y : CantorSpace} {m n : ℕ}
    (hmn : m ≤ n) (hy : y ∈ PiNat.cylinder x m) :
    PiNat.cylinder y n ⊆ PiNat.cylinder x m := by
  intro z hz i hi
  exact (hz i (hi.trans_le hmn)).trans (hy i hi)

/-- Cylinders at the same depth are equal or disjoint. -/
theorem cylinder_eq_or_disjoint (x y : CantorSpace) (n : ℕ) :
    PiNat.cylinder x n = PiNat.cylinder y n ∨
      Disjoint (PiNat.cylinder x n) (PiNat.cylinder y n) := by
  by_cases h : (PiNat.cylinder x n ∩ PiNat.cylinder y n).Nonempty
  · obtain ⟨z, hzx, hzy⟩ := h
    left
    exact (PiNat.mem_cylinder_iff_eq.mp hzx).symm.trans
      (PiNat.mem_cylinder_iff_eq.mp hzy)
  · right
    exact Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h)

/-- Every cylinder contains an arbitrarily deep subcylinder avoiding a prescribed
closed nowhere-dense set. This supplies the unused clopen pieces needed in a
back-and-forth extension construction. -/
theorem exists_subcylinder_avoiding {A : Set CantorSpace}
    (hA : IsClosed A) (hn : IsNowhereDense A) (x : CantorSpace) (n N : ℕ) :
    ∃ y : CantorSpace, ∃ m : ℕ, N ≤ m ∧ n ≤ m ∧
      PiNat.cylinder y m ⊆ PiNat.cylinder x n ∩ Aᶜ := by
  obtain ⟨hopen, hdense⟩ := isClosed_isNowhereDense_iff_compl.mp ⟨hA, hn⟩
  obtain ⟨y, hyA, hy⟩ := hdense.exists_mem_open
    (PiNat.isOpen_cylinder (fun _ : ℕ => Bool) x n)
    ⟨x, PiNat.self_mem_cylinder x n⟩
  obtain ⟨V, ⟨z, k, rfl⟩, hyV, hV⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).exists_subset_of_mem_open
      (show y ∈ PiNat.cylinder x n ∩ Aᶜ from ⟨hy, hyA⟩)
      ((PiNat.isOpen_cylinder (fun _ : ℕ => Bool) x n).inter hopen)
  refine ⟨z, max k (max n N), ?_, ?_, ?_⟩
  · exact (le_max_right n N).trans (le_max_right k (max n N))
  · exact (le_max_left n N).trans (le_max_right k (max n N))
  · exact (PiNat.cylinder_anti z (le_max_left k (max n N))).trans hV

/-- A first escaping cylinder has no shorter ancestor contained in the complement. -/
def FirstEscape (A : Set CantorSpace) (x : CantorSpace) (n : ℕ) : Prop :=
  PiNat.cylinder x n ⊆ Aᶜ ∧ ∀ m < n, ¬ PiNat.cylinder x m ⊆ Aᶜ

/-- Every point outside a closed set belongs to a first escaping cylinder. -/
theorem exists_firstEscape {A : Set CantorSpace} (hA : IsClosed A)
    {x : CantorSpace} (hx : x ∈ Aᶜ) : ∃ n, FirstEscape A x n := by
  classical
  obtain ⟨V, ⟨z, k, rfl⟩, hxV, hV⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).exists_subset_of_mem_open
      hx hA.isOpen_compl
  have hex : ∃ n, PiNat.cylinder x n ⊆ Aᶜ := by
    refine ⟨k, ?_⟩
    rw [PiNat.mem_cylinder_iff_eq.mp hxV]
    exact hV
  exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩

/-- Two first escaping cylinders that intersect are the same piece, including
when the closed set is empty and the whole space escapes at depth zero. -/
theorem firstEscape_eq_of_inter {A : Set CantorSpace} {x y : CantorSpace} {m n : ℕ}
    (hx : FirstEscape A x m) (hy : FirstEscape A y n)
    (h : (PiNat.cylinder x m ∩ PiNat.cylinder y n).Nonempty) :
    PiNat.cylinder x m = PiNat.cylinder y n := by
  obtain ⟨z, hzx, hzy⟩ := h
  have hmn : m = n := by
    rcases lt_trichotomy m n with hlt | heq | hlt
    · have hyx : y ∈ PiNat.cylinder x m := by
        intro i hi
        exact (hzy i (hi.trans hlt)).symm.trans (hzx i hi)
      exact False.elim (hy.2 m hlt ((cylinder_subset_of_mem le_rfl hyx).trans hx.1))
    · exact heq
    · have hxy : x ∈ PiNat.cylinder y n := by
        intro i hi
        exact (hzx i (hi.trans hlt)).symm.trans (hzy i hi)
      exact False.elim (hx.2 n hlt ((cylinder_subset_of_mem le_rfl hxy).trans hy.1))
  subst n
  exact (PiNat.mem_cylinder_iff_eq.mp hzx).symm.trans
    (PiNat.mem_cylinder_iff_eq.mp hzy)

/-- The canonical first-escape pieces of the complement. -/
def escapePieces (A : Set CantorSpace) : Set (Set CantorSpace) :=
  {V | ∃ x n, FirstEscape A x n ∧ V = PiNat.cylinder x n}

/-- Every piece is a nonempty clopen subset of the complement. -/
theorem escapePiece_properties {A : Set CantorSpace} {V : Set CantorSpace}
    (hV : V ∈ escapePieces A) : V.Nonempty ∧ IsClopen V ∧ V ⊆ Aᶜ := by
  obtain ⟨x, n, hx, rfl⟩ := hV
  refine ⟨⟨x, PiNat.self_mem_cylinder x n⟩, ⟨?_, ?_⟩, hx.1⟩
  · rw [PiNat.cylinder_eq_pi]
    exact isClosed_set_pi fun _ _ => isClosed_singleton
  · exact PiNat.isOpen_cylinder (fun _ : ℕ => Bool) x n

/-- There are only countably many escape pieces: each is encoded by a finite
Boolean word, rather than by its possibly uncountably many centers. -/
theorem escapePieces_countable (A : Set CantorSpace) : (escapePieces A).Countable := by
  have hc : (Set.range fun w : List Bool =>
      {y : CantorSpace | PiNat.res y w.length = w}).Countable := Set.countable_range _
  apply hc.mono
  rintro V ⟨x, n, hx, rfl⟩
  refine ⟨PiNat.res x n, ?_⟩
  simp only [PiNat.res_length]
  exact (PiNat.cylinder_eq_res x n).symm

/-- First-escape pieces cover exactly the complement of a closed set. -/
theorem sUnion_escapePieces {A : Set CantorSpace} (hA : IsClosed A) :
    ⋃₀ escapePieces A = Aᶜ := by
  apply Set.Subset.antisymm
  · rintro x ⟨V, ⟨y, n, hy, rfl⟩, hx⟩
    exact hy.1 hx
  · intro x hx
    obtain ⟨n, hn⟩ := exists_firstEscape hA hx
    exact ⟨PiNat.cylinder x n, ⟨x, n, hn, rfl⟩, PiNat.self_mem_cylinder x n⟩

/-- Distinct first-escape pieces are disjoint. -/
theorem escapePieces_pairwiseDisjoint (A : Set CantorSpace) :
    (escapePieces A).PairwiseDisjoint id := by
  rintro U ⟨x, m, hx, rfl⟩ V ⟨y, n, hy, rfl⟩ hne
  apply Set.disjoint_iff_inter_eq_empty.mpr
  apply Set.not_nonempty_iff_eq_empty.mp
  intro h
  exact hne (firstEscape_eq_of_inter hx hy h)

end KnasterReichbach
