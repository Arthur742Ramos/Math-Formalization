module
public import SimplexBoundaryRepair
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Data.Set.UnionLift

/-! SOURCE ONLY / UNCOMPILED. Conventional HEP interface for one actual
standard simplex. Initial map and lateral homotopy are separate inputs;
only their literal corner equality is assumed. Final interior is free. -/
@[expose] public noncomputable section
open Set unitInterval Convexity
namespace AutomaticCoherence.SimplexHomotopyExtension01
open AutomaticCoherence.SimplexBoundaryRepair01

section FinitePasting
variable {A Y J : Type*} [TopologicalSpace A] [TopologicalSpace Y] [Finite J]

def finiteClosedGlue (S : J → Set A) (g : ∀ j, C(S j, Y))
    (agree : ∀ i j (x : A) (hi : x ∈ S i) (hj : x ∈ S j),
      g i ⟨x, hi⟩ = g j ⟨x, hj⟩)
    (cover : ⋃ j, S j = univ) (closed : ∀ j, IsClosed (S j)) : C(A, Y) where
  toFun := Set.liftCover S (fun j => g j) agree cover
  continuous_toFun := by
    apply (locallyFinite_of_finite S).continuous cover closed
    intro j
    rw [continuousOn_iff_continuous_domRestrict]
    simpa +unfoldPartialApp only [Set.domRestrict, Set.liftCover_coe] using (g j).continuous

lemma finiteClosedGlue_coe (S : J → Set A) (g : ∀ j, C(S j, Y))
    (agree : ∀ i j (x : A) (hi : x ∈ S i) (hj : x ∈ S j),
      g i ⟨x, hi⟩ = g j ⟨x, hj⟩)
    (cover : ⋃ j, S j = univ) (closed : ∀ j, IsClosed (S j))
    (j : J) (x : S j) : finiteClosedGlue S g agree cover closed x = g j x := by
  exact Set.liftCover_coe (S := S) (f := fun j => g j)
    (hf := agree) (hS := cover) x
end FinitePasting

variable {n : Nat}
abbrev UnionDomain (n : Nat) := {p : Cylinder n // BottomSides p}

def patch : Bool → Set (UnionDomain n)
  | false => {p | p.val.1 = 0}
  | true => {p | Boundary p.val.2}

lemma boundary_closed : IsClosed {x : Simplex n | Boundary x} := by
  have heq : {x : Simplex n | Boundary x} =
      ⋃ i : Fin (n + 1), {x : Simplex n | x.weights i = 0} := by
    ext x
    simp only [Boundary, mem_setOf_eq, mem_iUnion]
  rw [heq]
  exact isClosed_iUnion_of_finite (fun i =>
    isClosed_eq (StdSimplex.continuous_weights_apply ℝ i) continuous_const)

lemma patch_closed (b : Bool) : IsClosed (patch (n := n) b) := by
  cases b
  · exact isClosed_eq continuous_subtype_val.fst continuous_const
  · exact boundary_closed.preimage continuous_subtype_val.snd

lemma patch_cover : ⋃ b, patch (n := n) b = univ := by
  apply iUnion_eq_univ_iff.mpr
  intro p
  rcases p.property with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

variable {Y : Type*} [TopologicalSpace Y]

def pieceMap (f : C(Simplex n, Y)) (h : C(I × {x : Simplex n // Boundary x}, Y)) :
    (b : Bool) → C(patch (n := n) b, Y)
  | false => {
      toFun := fun p => f p.val.val.2
      continuous_toFun := by
        have hp : Continuous (fun p : patch (n := n) false => p.val.val) :=
          continuous_subtype_val.comp continuous_subtype_val
        exact f.continuous.comp hp.snd }
  | true => {
      toFun := fun p => h (p.val.val.1, ⟨p.val.val.2, p.property⟩)
      continuous_toFun := by
        have hp : Continuous (fun p : patch (n := n) true => p.val.val) :=
          continuous_subtype_val.comp continuous_subtype_val
        exact h.continuous.comp (hp.fst.prodMk (hp.snd.subtype_mk _)) }

lemma pieceMap_agree (f : C(Simplex n, Y))
    (h : C(I × {x : Simplex n // Boundary x}, Y))
    (corner : ∀ x : {x : Simplex n // Boundary x}, h (0, x) = f x.val)
    (i j : Bool) (p : UnionDomain n) (hi : p ∈ patch i) (hj : p ∈ patch j) :
    pieceMap f h i ⟨p, hi⟩ = pieceMap f h j ⟨p, hj⟩ := by
  cases i <;> cases j
  · rfl
  · change p.val.1 = 0 at hi
    change f p.val.2 = h (p.val.1, ⟨p.val.2, hj⟩)
    rw [hi]
    exact (corner ⟨p.val.2, hj⟩).symm
  · change p.val.1 = 0 at hj
    change h (p.val.1, ⟨p.val.2, hi⟩) = f p.val.2
    rw [hj]
    exact corner _
  · rfl

/-- Actual finite closed pasting of separately supplied compatible data. -/
def paste (f : C(Simplex n, Y)) (h : C(I × {x : Simplex n // Boundary x}, Y))
    (corner : ∀ x : {x : Simplex n // Boundary x}, h (0, x) = f x.val) :
    C(UnionDomain n, Y) :=
  finiteClosedGlue patch (pieceMap f h) (pieceMap_agree f h corner) patch_cover patch_closed

lemma paste_bottom (f : C(Simplex n, Y))
    (h : C(I × {x : Simplex n // Boundary x}, Y))
    (corner : ∀ x : {x : Simplex n // Boundary x}, h (0, x) = f x.val)
    (x : Simplex n) : paste f h corner ⟨(0, x), Or.inl rfl⟩ = f x := by
  exact finiteClosedGlue_coe patch (pieceMap f h) (pieceMap_agree f h corner)
    patch_cover patch_closed false ⟨⟨(0, x), Or.inl rfl⟩, rfl⟩

lemma paste_lateral (f : C(Simplex n, Y))
    (h : C(I × {x : Simplex n // Boundary x}, Y))
    (corner : ∀ x : {x : Simplex n // Boundary x}, h (0, x) = f x.val)
    (t : I) (x : {x : Simplex n // Boundary x}) :
    paste f h corner ⟨(t, x.val), Or.inr x.property⟩ = h (t, x) := by
  exact finiteClosedGlue_coe patch (pieceMap f h) (pieceMap_agree f h corner)
    patch_cover patch_closed true ⟨⟨(t, x.val), Or.inr x.property⟩, x.property⟩

/-- HEP for the actual pair (Δⁿ,∂Δⁿ), including n=0. No prescribed top interior. -/
def extendHomotopy (f : C(Simplex n, Y))
    (h : C(I × {x : Simplex n // Boundary x}, Y))
    (corner : ∀ x : {x : Simplex n // Boundary x}, h (0, x) = f x.val) :
    C(Cylinder n, Y) := extendBoundary (paste f h corner)

lemma extendHomotopy_bottom (f : C(Simplex n, Y))
    (h : C(I × {x : Simplex n // Boundary x}, Y))
    (corner : ∀ x : {x : Simplex n // Boundary x}, h (0, x) = f x.val)
    (x : Simplex n) : extendHomotopy f h corner (0, x) = f x := by
  exact (extendBoundary_restrict (paste f h corner) ⟨(0, x), Or.inl rfl⟩).trans
    (paste_bottom f h corner x)

lemma extendHomotopy_lateral (f : C(Simplex n, Y))
    (h : C(I × {x : Simplex n // Boundary x}, Y))
    (corner : ∀ x : {x : Simplex n // Boundary x}, h (0, x) = f x.val)
    (t : I) (x : {x : Simplex n // Boundary x}) :
    extendHomotopy f h corner (t, x.val) = h (t, x) := by
  exact (extendBoundary_restrict (paste f h corner)
    ⟨(t, x.val), Or.inr x.property⟩).trans (paste_lateral f h corner t x)

end AutomaticCoherence.SimplexHomotopyExtension01
