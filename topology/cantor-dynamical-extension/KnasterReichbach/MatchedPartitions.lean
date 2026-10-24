module
public import KnasterReichbach.ClopenExtension
public import KnasterReichbach.CompatibleLimit

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
