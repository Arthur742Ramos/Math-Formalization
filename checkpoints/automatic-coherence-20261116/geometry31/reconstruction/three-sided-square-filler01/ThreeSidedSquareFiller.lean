module
public import ThreeSidedSquareRetraction
public import SimplexHomotopyExtension
public import Mathlib.Tactic.FinCases

/-! SOURCE ONLY / UNCOMPILED.
Parametric filling of the bottom and both vertical sides of the actual square.
Only the two corner equations are assumed; the top interior is unconstrained. -/
@[expose] public noncomputable section
open Set
open scoped Topology

namespace AutomaticCoherence.ThreeSidedSquareFiller01
open ThreeSidedSquareRetraction01
open SimplexHomotopyExtension01

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The three patches live on the actual three-sided subtype, with a parameter. -/
def patch (X : Type) : Fin 3 → Set (ThreeSides × X)
  | 0 => {p | p.1.val.1 = 0}
  | 1 => {p | p.1.val.2 = 0}
  | 2 => {p | p.1.val.2 = 1}

lemma patch_closed (i : Fin 3) : IsClosed (patch X i) := by
  have h : Continuous (fun p : ThreeSides × X => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  fin_cases i
  · exact isClosed_eq h.fst continuous_const
  · exact isClosed_eq h.snd continuous_const
  · exact isClosed_eq h.snd continuous_const

lemma patch_cover : (⋃ i, patch X i) = univ := by
  apply iUnion_eq_univ_iff.mpr
  intro p
  rcases p.1.property with ht | hs | hs
  · exact ⟨0, ht⟩
  · exact ⟨1, hs⟩
  · exact ⟨2, hs⟩

def bottomCoordinate : C(ThreeSides × X, I × X) where
  toFun p := (p.1.val.2, p.2)
  continuous_toFun := by
    have h : Continuous (fun p : ThreeSides × X => p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    exact h.snd.prodMk continuous_snd

def sideCoordinate : C(ThreeSides × X, I × X) where
  toFun p := (p.1.val.1, p.2)
  continuous_toFun := by
    have h : Continuous (fun p : ThreeSides × X => p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    exact h.fst.prodMk continuous_snd

variable (bottom left right : C(I × X, Y))

def pieceMap : (i : Fin 3) → C(patch X i, Y)
  | 0 => (bottom.comp bottomCoordinate).comp ⟨Subtype.val, continuous_subtype_val⟩
  | 1 => (left.comp sideCoordinate).comp ⟨Subtype.val, continuous_subtype_val⟩
  | 2 => (right.comp sideCoordinate).comp ⟨Subtype.val, continuous_subtype_val⟩

variable (left_corner : ∀ x, left (0, x) = bottom (0, x))
  (right_corner : ∀ x, right (0, x) = bottom (1, x))

include left_corner right_corner in
/-- All nine pairs: three diagonal, four corner, and two disjoint-side cases. -/
lemma pieceMap_agree (i j : Fin 3) (p : ThreeSides × X)
    (hi : p ∈ patch X i) (hj : p ∈ patch X j) :
    pieceMap bottom left right i ⟨p, hi⟩ = pieceMap bottom left right j ⟨p, hj⟩ := by
  fin_cases i <;> fin_cases j
  · rfl
  · change p.1.val.1 = 0 at hi
    change p.1.val.2 = 0 at hj
    change bottom (p.1.val.2, p.2) = left (p.1.val.1, p.2)
    rw [hi, hj]
    exact (left_corner p.2).symm
  · change p.1.val.1 = 0 at hi
    change p.1.val.2 = 1 at hj
    change bottom (p.1.val.2, p.2) = right (p.1.val.1, p.2)
    rw [hi, hj]
    exact (right_corner p.2).symm
  · change p.1.val.2 = 0 at hi
    change p.1.val.1 = 0 at hj
    change left (p.1.val.1, p.2) = bottom (p.1.val.2, p.2)
    rw [hj, hi]
    exact left_corner p.2
  · rfl
  · change p.1.val.2 = 0 at hi
    change p.1.val.2 = 1 at hj
    have h01 : (0 : ℝ) = 1 :=
      congrArg (fun s : I => (s : ℝ)) (hi.symm.trans hj)
    exact False.elim (zero_ne_one h01)
  · change p.1.val.2 = 1 at hi
    change p.1.val.1 = 0 at hj
    change right (p.1.val.1, p.2) = bottom (p.1.val.2, p.2)
    rw [hj, hi]
    exact right_corner p.2
  · change p.1.val.2 = 1 at hi
    change p.1.val.2 = 0 at hj
    have h01 : (0 : ℝ) = 1 :=
      congrArg (fun s : I => (s : ℝ)) (hj.symm.trans hi)
    exact False.elim (zero_ne_one h01)
  · rfl

/-- Actual finite closed pasting. No gluing or extension hypothesis is supplied. -/
def paste : C(ThreeSides × X, Y) :=
  finiteClosedGlue (patch X) (pieceMap bottom left right)
    (pieceMap_agree bottom left right left_corner right_corner)
    patch_cover patch_closed

lemma paste_bottom (s : I) (x : X) :
    paste bottom left right left_corner right_corner (⟨(0, s), Or.inl rfl⟩, x) =
      bottom (s, x) :=
  finiteClosedGlue_coe (patch X) (pieceMap bottom left right)
    (pieceMap_agree bottom left right left_corner right_corner)
    patch_cover patch_closed 0 ⟨(⟨(0, s), Or.inl rfl⟩, x), rfl⟩

lemma paste_left (t : I) (x : X) :
    paste bottom left right left_corner right_corner (⟨(t, 0), Or.inr (Or.inl rfl)⟩, x) =
      left (t, x) :=
  finiteClosedGlue_coe (patch X) (pieceMap bottom left right)
    (pieceMap_agree bottom left right left_corner right_corner)
    patch_cover patch_closed 1 ⟨(⟨(t, 0), Or.inr (Or.inl rfl)⟩, x), rfl⟩

lemma paste_right (t : I) (x : X) :
    paste bottom left right left_corner right_corner (⟨(t, 1), Or.inr (Or.inr rfl)⟩, x) =
      right (t, x) :=
  finiteClosedGlue_coe (patch X) (pieceMap bottom left right)
    (pieceMap_agree bottom left right left_corner right_corner)
    patch_cover patch_closed 2 ⟨(⟨(t, 1), Or.inr (Or.inr rfl)⟩, x), rfl⟩

/-- Product with the identity, an explicit continuous map, not a colimit claim. -/
def retractProduct : C((I × I) × X, ThreeSides × X) where
  toFun p := (edgeRetract p.1, p.2)
  continuous_toFun := (edgeRetract.continuous.comp continuous_fst).prodMk continuous_snd

def fill : C((I × I) × X, Y) :=
  (paste bottom left right left_corner right_corner).comp retractProduct

lemma fill_on_sides (p : ThreeSides) (x : X) :
    fill bottom left right left_corner right_corner (p.val, x) =
      paste bottom left right left_corner right_corner (p, x) := by
  change paste bottom left right left_corner right_corner (edgeRetract p.val, x) = _
  exact congrArg (fun q : ThreeSides =>
    paste bottom left right left_corner right_corner (q, x)) (edgeRetract_fixed p)

lemma fill_bottom (s : I) (x : X) :
    fill bottom left right left_corner right_corner ((0, s), x) = bottom (s, x) :=
  (fill_on_sides bottom left right left_corner right_corner ⟨(0, s), Or.inl rfl⟩ x).trans
    (paste_bottom bottom left right left_corner right_corner s x)

lemma fill_left (t : I) (x : X) :
    fill bottom left right left_corner right_corner ((t, 0), x) = left (t, x) :=
  (fill_on_sides bottom left right left_corner right_corner
    ⟨(t, 0), Or.inr (Or.inl rfl)⟩ x).trans
      (paste_left bottom left right left_corner right_corner t x)

lemma fill_right (t : I) (x : X) :
    fill bottom left right left_corner right_corner ((t, 1), x) = right (t, x) :=
  (fill_on_sides bottom left right left_corner right_corner
    ⟨(t, 1), Or.inr (Or.inr rfl)⟩ x).trans
      (paste_right bottom left right left_corner right_corner t x)

end AutomaticCoherence.ThreeSidedSquareFiller01
