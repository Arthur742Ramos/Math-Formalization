module
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.Maps.Proper.Basic


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


public section

namespace KnasterReichbach

/-- Finite matched clopen partitions will supply these closed approximating
relations. Bi-totality and control in both directions are required explicitly. -/
structure CompatibleRelations where
  relation : ℕ → Set (CantorSpace × CantorSpace)
  closed : ∀ n, IsClosed (relation n)
  nested : Antitone relation
  total : ∀ n x, ∃ y, (x, y) ∈ relation n
  onto : ∀ n y, ∃ x, (x, y) ∈ relation n
  right_prefix : ∀ n x y z, (x, y) ∈ relation n → (x, z) ∈ relation n →
    ∀ i < n, y i = z i
  left_prefix : ∀ n x y z, (y, x) ∈ relation n → (z, x) ∈ relation n →
    ∀ i < n, y i = z i

namespace CompatibleRelations

def symm (R : CompatibleRelations) : CompatibleRelations where
  relation n := Prod.swap ⁻¹' R.relation n
  closed n := (R.closed n).preimage continuous_swap
  nested := fun _ _ h _ hz => R.nested h hz
  total := R.onto
  onto := R.total
  right_prefix := R.left_prefix
  left_prefix := R.right_prefix

theorem exists_limit (R : CompatibleRelations) (x : CantorSpace) :
    ∃ y, ∀ n, (x, y) ∈ R.relation n := by
  let F : ℕ → Set CantorSpace := fun n => {y | (x, y) ∈ R.relation n}
  have hclosed (n : ℕ) : IsClosed (F n) :=
    (R.closed n).preimage (continuous_const.prodMk continuous_id)
  have hnonempty (n : ℕ) : (F n).Nonempty := R.total n x
  have hnested : Antitone F := fun _ _ h _ hz => R.nested h hz
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    F (fun n => hnested (Nat.le_succ n)) hnonempty (hclosed 0).isCompact hclosed
  exact ⟨y, fun n => Set.mem_iInter.mp hy n⟩

noncomputable def limit (R : CompatibleRelations) (x : CantorSpace) : CantorSpace :=
  Classical.choose (R.exists_limit x)

theorem limit_mem (R : CompatibleRelations) (x : CantorSpace) (n : ℕ) :
    (x, R.limit x) ∈ R.relation n :=
  Classical.choose_spec (R.exists_limit x) n

theorem limit_unique (R : CompatibleRelations) {x y : CantorSpace}
    (hy : ∀ n, (x, y) ∈ R.relation n) : y = R.limit x := by
  funext i
  exact R.right_prefix (i + 1) x y (R.limit x) (hy _) (R.limit_mem x _) i
    (Nat.lt_succ_self i)

theorem left_inverse (R : CompatibleRelations) :
    Function.LeftInverse R.symm.limit R.limit := by
  intro x
  exact (R.symm.limit_unique (fun n => R.limit_mem x n)).symm

theorem continuous_limit (R : CompatibleRelations) : Continuous R.limit := by
  apply continuous_of_isClosed_graph
  have heq : R.limit.graph = ⋂ n, R.relation n := by
    ext p
    constructor
    · intro hp
      have hp' : R.limit p.1 = p.2 := hp
      apply Set.mem_iInter.mpr
      intro n
      simpa only [hp'] using R.limit_mem p.1 n
    · intro hp
      exact (R.limit_unique (Set.mem_iInter.mp hp)).symm
  rw [heq]
  exact isClosed_iInter R.closed

/-- The inverse-limit step of the extension construction. This does not assert
that relations extending a prescribed partial homeomorphism already exist. -/
noncomputable def homeomorph (R : CompatibleRelations) : CantorSpace ≃ₜ CantorSpace where
  toFun := R.limit
  invFun := R.symm.limit
  left_inv := R.left_inverse
  right_inv := by
    intro y
    exact (R.limit_unique (fun n => R.symm.limit_mem y n)).symm
  continuous_toFun := R.continuous_limit
  continuous_invFun := R.symm.continuous_limit

theorem homeomorph_agrees (R : CompatibleRelations) {A B : Set CantorSpace}
    (h : A ≃ₜ B) (hR : ∀ n (a : A), (a.val, (h a).val) ∈ R.relation n) (a : A) :
    R.homeomorph a.val = (h a).val :=
  (R.limit_unique (fun n => hR n a)).symm

end CompatibleRelations
end KnasterReichbach


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


public section
open Set

namespace KnasterReichbach

/-- Binary trace matching including empty daughters. Empty pieces are retained
on both sides so the two partition index types stay identical. -/
theorem match_split_allow_empty {A B U V P : Set CantorSpace} (h : A ≃ₜ B)
    (hB : IsClosed B) (hnB : IsNowhereDense B)
    (hV : IsClopen V) (hne : U.Nonempty ↔ V.Nonempty)
    (htrace : ∀ a : A, a.val ∈ U ↔ (h a).val ∈ V)
    (hP : IsClopen P) (hPU : P ⊆ U) :
    ∃ Q : Set CantorSpace, IsClopen Q ∧ Q ⊆ V ∧
      (P.Nonempty ↔ Q.Nonempty) ∧ ((U \ P).Nonempty ↔ (V \ Q).Nonempty) ∧
      (∀ a : A, a.val ∈ P ↔ (h a).val ∈ Q) := by
  classical
  by_cases hp : P.Nonempty
  · by_cases hd : (U \ P).Nonempty
    · obtain ⟨Q, hQ, hQV, hQne, hdiff, hmatch, _⟩ := match_clopen_split h hB hnB hV
        (hne.mp (hp.mono hPU)) htrace hP hPU
      exact ⟨Q, hQ, hQV, iff_of_true hp hQne, iff_of_true hd hdiff, hmatch⟩
    · have hUP : U ⊆ P := by
        intro x hx
        by_contra hxp
        exact hd ⟨x, hx, hxp⟩
      have heq : P = U := hPU.antisymm hUP
      subst P
      exact ⟨V, hV, subset_rfl, hne, by simp, htrace⟩
  · have heq : P = ∅ := Set.not_nonempty_iff_eq_empty.mp hp
    subst P
    exact ⟨∅, isClopen_empty, empty_subset V, by simp, by simpa using hne, by simp⟩

/-- A finite matched clopen partition, permitting empty cells only when the
corresponding cell on the other side is empty too. -/
structure MatchedPartition {A B : Set CantorSpace} (h : A ≃ₜ B) where
  Index : Type
  finite : Finite Index
  left : Index → Set CantorSpace
  right : Index → Set CantorSpace
  left_clopen : ∀ i, IsClopen (left i)
  right_clopen : ∀ i, IsClopen (right i)
  left_cover : ∀ x, ∃ i, x ∈ left i
  right_cover : ∀ x, ∃ i, x ∈ right i
  left_disjoint : Pairwise (fun i j => Disjoint (left i) (left j))
  right_disjoint : Pairwise (fun i j => Disjoint (right i) (right j))
  nonempty_iff : ∀ i, (left i).Nonempty ↔ (right i).Nonempty
  trace : ∀ i (a : A), a.val ∈ left i ↔ (h a).val ∈ right i

namespace MatchedPartition

def splitCell (P D : Set CantorSpace) (b : Bool) : Set CantorSpace :=
  if b then D else P \ D

theorem splitCell_subset {P D : Set CantorSpace} (hD : D ⊆ P) (b : Bool) :
    splitCell P D b ⊆ P := by
  cases b
  · exact sdiff_subset
  · exact hD

theorem splitCell_cover {P D : Set CantorSpace} {x : CantorSpace} (hx : x ∈ P) :
    ∃ b, x ∈ splitCell P D b := by
  by_cases hd : x ∈ D
  · exact ⟨true, hd⟩
  · exact ⟨false, hx, hd⟩

theorem splitCell_pairwise {I : Type} {P D : I → Set CantorSpace}
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) (hD : ∀ i, D i ⊆ P i) :
    Pairwise (fun u v : I × Bool =>
      Disjoint (splitCell (P u.1) (D u.1) u.2) (splitCell (P v.1) (D v.1) v.2)) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ hne
  by_cases hij : i = j
  · subst j
    cases b <;> cases c <;>
      simp_all [splitCell, Set.disjoint_left]
  · exact (hP hij).mono (splitCell_subset (hD i) b) (splitCell_subset (hD j) c)

def trivial {A B : Set CantorSpace} (h : A ≃ₜ B) : MatchedPartition h where
  Index := Unit
  finite := inferInstance
  left _ := univ
  right _ := univ
  left_clopen _ := isClopen_univ
  right_clopen _ := isClopen_univ
  left_cover x := ⟨(), Set.mem_univ x⟩
  right_cover x := ⟨(), Set.mem_univ x⟩
  left_disjoint := by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _))
  right_disjoint := by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _))
  nonempty_iff _ := Iff.rfl
  trace _ _ := Iff.rfl

def symm {A B : Set CantorSpace} {h : A ≃ₜ B} (M : MatchedPartition h) :
    MatchedPartition h.symm where
  Index := M.Index
  finite := M.finite
  left := M.right
  right := M.left
  left_clopen := M.right_clopen
  right_clopen := M.left_clopen
  left_cover := M.right_cover
  right_cover := M.left_cover
  left_disjoint := M.right_disjoint
  right_disjoint := M.left_disjoint
  nonempty_iff i := (M.nonempty_iff i).symm
  trace i b := by simpa using (M.trace i (h.symm b)).symm

structure Refinement {A B : Set CantorSpace} {h : A ≃ₜ B} (M : MatchedPartition h) where
  partition : MatchedPartition h
  parent : partition.Index → M.Index
  left_sub : ∀ i, partition.left i ⊆ M.left (parent i)
  right_sub : ∀ i, partition.right i ⊆ M.right (parent i)

noncomputable def splitLeft {A B : Set CantorSpace} {h : A ≃ₜ B}
    (M : MatchedPartition h) (hB : IsClosed B) (hnB : IsNowhereDense B)
    {D : Set CantorSpace} (hD : IsClopen D) : Refinement M := by
  classical
  letI := M.finite
  have hex (i : M.Index) := match_split_allow_empty h hB hnB (M.right_clopen i)
    (M.nonempty_iff i) (M.trace i) ((M.left_clopen i).inter hD)
    (show M.left i ∩ D ⊆ M.left i from inter_subset_left)
  choose Q hQ hQV hne0 hne1 htrace using hex
  let P : M.Index → Set CantorSpace := fun i => M.left i ∩ D
  have hPL (i : M.Index) : P i ⊆ M.left i := inter_subset_left
  have hPD (i : M.Index) : M.left i \ P i = M.left i \ D := by
    ext x
    simp [P]
  refine {
    partition := {
      Index := M.Index × Bool
      finite := inferInstance
      left := fun i => splitCell (M.left i.1) (P i.1) i.2
      right := fun i => splitCell (M.right i.1) (Q i.1) i.2
      left_clopen := ?_
      right_clopen := ?_
      left_cover := ?_
      right_cover := ?_
      left_disjoint := splitCell_pairwise M.left_disjoint hPL
      right_disjoint := splitCell_pairwise M.right_disjoint hQV
      nonempty_iff := ?_
      trace := ?_ }
    parent := Prod.fst
    left_sub := ?_
    right_sub := ?_ }
  · rintro ⟨i, b⟩
    cases b
    · exact (M.left_clopen i).diff ((M.left_clopen i).inter hD)
    · exact (M.left_clopen i).inter hD
  · rintro ⟨i, b⟩
    cases b
    · exact (M.right_clopen i).diff (hQ i)
    · exact hQ i
  · intro x
    obtain ⟨i, hi⟩ := M.left_cover x
    obtain ⟨b, hb⟩ := splitCell_cover (D := P i) hi
    exact ⟨⟨i, b⟩, hb⟩
  · intro x
    obtain ⟨i, hi⟩ := M.right_cover x
    obtain ⟨b, hb⟩ := splitCell_cover (D := Q i) hi
    exact ⟨⟨i, b⟩, hb⟩
  · rintro ⟨i, b⟩
    cases b
    · exact hne1 i
    · exact hne0 i
  · rintro ⟨i, b⟩ a
    cases b
    · exact and_congr (M.trace i a) (not_congr (htrace i a))
    · exact htrace i a
  · rintro ⟨i, b⟩
    exact splitCell_subset (hPL i) b
  · rintro ⟨i, b⟩
    exact splitCell_subset (hQV i) b

theorem splitLeft_same_membership {A B : Set CantorSpace} {h : A ≃ₜ B}
    (M : MatchedPartition h) (hB : IsClosed B) (hnB : IsNowhereDense B)
    {D : Set CantorSpace} (hD : IsClopen D)
    (i : (M.splitLeft hB hnB hD).partition.Index) {x y : CantorSpace}
    (hx : x ∈ (M.splitLeft hB hnB hD).partition.left i)
    (hy : y ∈ (M.splitLeft hB hnB hD).partition.left i) :
    x ∈ D ↔ y ∈ D := by
  rcases i with ⟨i, b⟩
  change x ∈ splitCell (M.left i) (M.left i ∩ D) b at hx
  change y ∈ splitCell (M.left i) (M.left i ∩ D) b at hy
  cases b
  · exact iff_of_false (fun hd => hx.2 ⟨hx.1, hd⟩) (fun hd => hy.2 ⟨hy.1, hd⟩)
  · exact iff_of_true hx.2 hy.2

def coordinate (n : ℕ) : Set CantorSpace := {x | x n = true}

theorem coordinate_clopen (n : ℕ) : IsClopen (coordinate n) :=
  (isClopen_discrete ({true} : Set Bool)).preimage (continuous_apply n)

def LeftPrefix {A B : Set CantorSpace} {h : A ≃ₜ B} (M : MatchedPartition h) (n : ℕ) : Prop :=
  ∀ i x y, x ∈ M.left i → y ∈ M.left i → ∀ j < n, x j = y j

def RightPrefix {A B : Set CantorSpace} {h : A ≃ₜ B} (M : MatchedPartition h) (n : ℕ) : Prop :=
  ∀ i x y, x ∈ M.right i → y ∈ M.right i → ∀ j < n, x j = y j

theorem prefix_zero {A B : Set CantorSpace} {h : A ≃ₜ B} (M : MatchedPartition h) :
    M.LeftPrefix 0 ∧ M.RightPrefix 0 := by
  constructor <;> intro i x y hx hy j hj <;> exact False.elim (Nat.not_lt_zero j hj)

theorem Refinement.preserve_left {A B : Set CantorSpace} {h : A ≃ₜ B}
    {M : MatchedPartition h} (F : Refinement M) {n : ℕ} (hn : M.LeftPrefix n) :
    F.partition.LeftPrefix n := by
  intro i x y hx hy
  exact hn (F.parent i) x y (F.left_sub i hx) (F.left_sub i hy)

theorem Refinement.preserve_right {A B : Set CantorSpace} {h : A ≃ₜ B}
    {M : MatchedPartition h} (F : Refinement M) {n : ℕ} (hn : M.RightPrefix n) :
    F.partition.RightPrefix n := by
  intro i x y hx hy
  exact hn (F.parent i) x y (F.right_sub i hx) (F.right_sub i hy)

theorem splitLeft_prefix {A B : Set CantorSpace} {h : A ≃ₜ B}
    (M : MatchedPartition h) (hB : IsClosed B) (hnB : IsNowhereDense B)
    {n : ℕ} (hn : M.LeftPrefix n) :
    (M.splitLeft hB hnB (coordinate_clopen n)).partition.LeftPrefix (n + 1) := by
  intro i x y hx hy j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hjn
  · exact (M.splitLeft hB hnB (coordinate_clopen n)).preserve_left hn i x y hx hy j hj
  · subst j
    have heq := M.splitLeft_same_membership hB hnB (coordinate_clopen n) i hx hy
    cases hxn : x n <;> cases hyn : y n <;> simp_all [coordinate]

def relation {A B : Set CantorSpace} {h : A ≃ₜ B} (M : MatchedPartition h) :
    Set (CantorSpace × CantorSpace) := {p | ∃ i, p.1 ∈ M.left i ∧ p.2 ∈ M.right i}

theorem relation_closed {A B : Set CantorSpace} {h : A ≃ₜ B} (M : MatchedPartition h) :
    IsClosed M.relation := by
  let := M.finite
  have heq : M.relation = ⋃ i, M.left i ×ˢ M.right i := by
    ext p
    simp [relation]
  rw [heq]
  exact isClosed_iUnion_of_finite fun i => (M.left_clopen i).isClosed.prod
    (M.right_clopen i).isClosed

theorem relation_total {A B : Set CantorSpace} {h : A ≃ₜ B} (M : MatchedPartition h)
    (x : CantorSpace) : ∃ y, (x, y) ∈ M.relation := by
  obtain ⟨i, hi⟩ := M.left_cover x
  obtain ⟨y, hy⟩ := (M.nonempty_iff i).mp ⟨x, hi⟩
  exact ⟨y, i, hi, hy⟩

theorem relation_onto {A B : Set CantorSpace} {h : A ≃ₜ B} (M : MatchedPartition h)
    (y : CantorSpace) : ∃ x, (x, y) ∈ M.relation := by
  obtain ⟨i, hi⟩ := M.right_cover y
  obtain ⟨x, hx⟩ := (M.nonempty_iff i).mpr ⟨y, hi⟩
  exact ⟨x, i, hx, hi⟩

theorem relation_trace {A B : Set CantorSpace} {h : A ≃ₜ B} (M : MatchedPartition h)
    (a : A) : (a.val, (h a).val) ∈ M.relation := by
  obtain ⟨i, hi⟩ := M.left_cover a.val
  exact ⟨i, hi, (M.trace i a).mp hi⟩

theorem relation_right_prefix {A B : Set CantorSpace} {h : A ≃ₜ B}
    (M : MatchedPartition h) {n : ℕ} (hn : M.RightPrefix n)
    {x y z : CantorSpace} (hy : (x, y) ∈ M.relation) (hz : (x, z) ∈ M.relation) :
    ∀ j < n, y j = z j := by
  obtain ⟨i, hxi, hyi⟩ := hy
  obtain ⟨k, hxk, hzk⟩ := hz
  have hik : i = k := by
    by_contra hne
    exact Set.disjoint_left.mp (M.left_disjoint hne) hxi hxk
  subst k
  exact hn i y z hyi hzk

theorem relation_left_prefix {A B : Set CantorSpace} {h : A ≃ₜ B}
    (M : MatchedPartition h) {n : ℕ} (hn : M.LeftPrefix n)
    {x y z : CantorSpace} (hy : (y, x) ∈ M.relation) (hz : (z, x) ∈ M.relation) :
    ∀ j < n, y j = z j := by
  obtain ⟨i, hyi, hxi⟩ := hy
  obtain ⟨k, hzk, hxk⟩ := hz
  have hik : i = k := by
    by_contra hne
    exact Set.disjoint_left.mp (M.right_disjoint hne) hxi hxk
  subst k
  exact hn i y z hyi hzk

theorem Refinement.relation_subset {A B : Set CantorSpace} {h : A ≃ₜ B}
    {M : MatchedPartition h} (F : Refinement M) : F.partition.relation ⊆ M.relation := by
  rintro p ⟨i, hiL, hiR⟩
  exact ⟨F.parent i, F.left_sub i hiL, F.right_sub i hiR⟩

noncomputable def step {A B : Set CantorSpace} {h : A ≃ₜ B} (M : MatchedPartition h)
    (hA : IsClosed A) (hnA : IsNowhereDense A) (hB : IsClosed B) (hnB : IsNowhereDense B)
    (n : ℕ) : Refinement M :=
  let L := M.splitLeft hB hnB (coordinate_clopen n)
  let R := L.partition.symm.splitLeft hA hnA (coordinate_clopen n)
  { partition := R.partition.symm
    parent := fun i => L.parent (R.parent i)
    left_sub := fun i => (R.right_sub i).trans (L.left_sub (R.parent i))
    right_sub := fun i => (R.left_sub i).trans (L.right_sub (R.parent i)) }

theorem step_prefix {A B : Set CantorSpace} {h : A ≃ₜ B} (M : MatchedPartition h)
    (hA : IsClosed A) (hnA : IsNowhereDense A) (hB : IsClosed B) (hnB : IsNowhereDense B)
    {n : ℕ} (hL : M.LeftPrefix n) (hR : M.RightPrefix n) :
    (M.step hA hnA hB hnB n).partition.LeftPrefix (n + 1) ∧
    (M.step hA hnA hB hnB n).partition.RightPrefix (n + 1) := by
  let L := M.splitLeft hB hnB (coordinate_clopen n)
  let R := L.partition.symm.splitLeft hA hnA (coordinate_clopen n)
  have hLp : L.partition.LeftPrefix (n + 1) := M.splitLeft_prefix hB hnB hL
  have hRp : L.partition.RightPrefix n := L.preserve_right hR
  constructor
  · exact R.preserve_right hLp
  · exact L.partition.symm.splitLeft_prefix hA hnA hRp

end MatchedPartition
end KnasterReichbach


public section
namespace KnasterReichbach

open MatchedPartition

noncomputable def partitions {A B : Set CantorSpace} (h : A ≃ₜ B)
    (hA : IsClosed A) (hnA : IsNowhereDense A) (hB : IsClosed B) (hnB : IsNowhereDense B) :
    ℕ → MatchedPartition h
  | 0 => MatchedPartition.trivial h
  | n + 1 => ((partitions h hA hnA hB hnB n).step hA hnA hB hnB n).partition

theorem partitions_prefix {A B : Set CantorSpace} (h : A ≃ₜ B)
    (hA : IsClosed A) (hnA : IsNowhereDense A) (hB : IsClosed B) (hnB : IsNowhereDense B)
    (n : ℕ) :
    (partitions h hA hnA hB hnB n).LeftPrefix n ∧
    (partitions h hA hnA hB hnB n).RightPrefix n := by
  induction n with
  | zero =>
    exact (partitions h hA hnA hB hnB 0).prefix_zero
  | succ n ih =>
    exact (partitions h hA hnA hB hnB n).step_prefix hA hnA hB hnB ih.1 ih.2

/-- Construct the compatible relations by alternating source and target
coordinate splits. No refinement-existence hypothesis is supplied externally. -/
noncomputable def extensionRelations {A B : Set CantorSpace} (h : A ≃ₜ B)
    (hA : IsClosed A) (hnA : IsNowhereDense A) (hB : IsClosed B) (hnB : IsNowhereDense B) :
    CompatibleRelations where
  relation n := (partitions h hA hnA hB hnB n).relation
  closed n := (partitions h hA hnA hB hnB n).relation_closed
  nested := antitone_nat_of_succ_le (fun n =>
    ((partitions h hA hnA hB hnB n).step hA hnA hB hnB n).relation_subset)
  total n := (partitions h hA hnA hB hnB n).relation_total
  onto n := (partitions h hA hnA hB hnB n).relation_onto
  right_prefix n _ _ _ hy hz := (partitions h hA hnA hB hnB n).relation_right_prefix
    (partitions_prefix h hA hnA hB hnB n).2 hy hz
  left_prefix n _ _ _ hy hz := (partitions h hA hnA hB hnB n).relation_left_prefix
    (partitions_prefix h hA hnA hB hnB n).1 hy hz

/-- **Knaster–Reichbach extension theorem for Cantor space.** Every prescribed
homeomorphism between closed nowhere-dense subsets extends to an ambient
homeomorphism. No nonemptiness assumption is imposed on either subset. -/
theorem exists_homeomorph_extension {A B : Set CantorSpace}
    (hA : IsClosed A) (hnA : IsNowhereDense A) (hB : IsClosed B) (hnB : IsNowhereDense B)
    (h : A ≃ₜ B) :
    ∃ H : CantorSpace ≃ₜ CantorSpace, ∀ a : A, H a.val = (h a).val := by
  let R := extensionRelations h hA hnA hB hnB
  refine ⟨R.homeomorph, ?_⟩
  exact R.homeomorph_agrees h (fun n a =>
    (partitions h hA hnA hB hnB n).relation_trace a)

end KnasterReichbach
