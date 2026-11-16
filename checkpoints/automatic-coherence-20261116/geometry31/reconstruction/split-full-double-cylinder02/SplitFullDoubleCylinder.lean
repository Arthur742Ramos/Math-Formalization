import SplitDoubleCylinderFoundation
import DoubleCylinderCollapse
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! SOURCE ONLY / UNCOMPILED.
Actual split/full double-cylinder homeomorphism. Both split free ends are 0
and attached ends 1; the full interval runs from B at 0 to C at 1.
No HEP, injectivity, nonemptiness or quotient identification is assumed. -/
noncomputable section
open CategoryTheory ContinuousMap
open scoped Topology

namespace AutomaticCoherence.SplitFullDoubleCylinder01
open SplitDoubleCylinderFoundation01 (SplitDoubleCylinder)
open DoubleCylinderCollapse01 (DoubleCylinder)
abbrev I := unitInterval

def midpoint : I := ⟨1 / 2, by norm_num, by norm_num⟩

def leftCoordinate (s : I) : I :=
  ⟨(1 - (s : ℝ)) / 2, by
    have h0 := s.property.1
    have h1 := s.property.2
    constructor <;> linarith⟩

def rightCoordinate (s : I) : I :=
  ⟨(1 + (s : ℝ)) / 2, by
    have h0 := s.property.1
    have h1 := s.property.2
    constructor <;> linarith⟩

lemma continuous_leftCoordinate : Continuous leftCoordinate := by
  unfold leftCoordinate
  fun_prop

lemma continuous_rightCoordinate : Continuous rightCoordinate := by
  unfold rightCoordinate
  fun_prop

@[simp] lemma leftCoordinate_zero : leftCoordinate 0 = midpoint := by
  apply Subtype.ext
  norm_num [leftCoordinate, midpoint]

@[simp] lemma leftCoordinate_one : leftCoordinate 1 = 0 := by
  apply Subtype.ext
  norm_num [leftCoordinate]

@[simp] lemma rightCoordinate_zero : rightCoordinate 0 = midpoint := by
  apply Subtype.ext
  norm_num [rightCoordinate, midpoint]

@[simp] lemma rightCoordinate_one : rightCoordinate 1 = 1 := by
  apply Subtype.ext
  norm_num [rightCoordinate]

lemma leftCoordinate_le_half (s : I) : (leftCoordinate s : ℝ) ≤ 1 / 2 := by
  change (1 - (s : ℝ)) / 2 ≤ 1 / 2
  have h0 := s.property.1
  linarith

variable {A B C : TopCat.{0}} {i : A ⟶ B} {j : A ⟶ C}
  (sd : SplitDoubleCylinder i j) (fd : DoubleCylinder i j)

/-- The left half reverses its cylinder coordinate and scales it to [0,1/2]. -/
def leftToFull : sd.leftCylinder.M ⟶ fd.D :=
  sd.leftCylinder.desc fd.left
    ⟨fun p => fd.interval (leftCoordinate p.1,p.2),
      fd.interval.hom.continuous.comp
        ((continuous_leftCoordinate.comp continuous_fst).prodMk continuous_snd)⟩
    (by
      intro a
      change fd.interval (leftCoordinate 1,a) = fd.left (i a)
      rw [leftCoordinate_one]
      exact fd.interval_zero a)

/-- The right half scales its cylinder coordinate to [1/2,1]. -/
def rightToFull : sd.rightCylinder.M ⟶ fd.D :=
  sd.rightCylinder.desc fd.d
    ⟨fun p => fd.interval (rightCoordinate p.1,p.2),
      fd.interval.hom.continuous.comp
        ((continuous_rightCoordinate.comp continuous_fst).prodMk continuous_snd)⟩
    (by
      intro a
      change fd.interval (rightCoordinate 1,a) = fd.d (j a)
      rw [rightCoordinate_one]
      exact fd.interval_one a)

lemma leftToFull_free (a : A) :
    leftToFull sd fd (sd.leftCylinder.free a) = fd.interval (midpoint,a) :=
  (sd.leftCylinder.desc_free _ _ _ a).trans
    (congrArg (fun t : I => fd.interval (t,a)) leftCoordinate_zero)

lemma rightToFull_free (a : A) :
    rightToFull sd fd (sd.rightCylinder.free a) = fd.interval (midpoint,a) :=
  (sd.rightCylinder.desc_free _ _ _ a).trans
    (congrArg (fun t : I => fd.interval (t,a)) rightCoordinate_zero)

/-- The common-A midpoint equality discharges the actual split pushout gluing. -/
def toFull : sd.S ⟶ fd.D :=
  sd.desc (leftToFull sd fd) (rightToFull sd fd)
    (fun a => (leftToFull_free sd fd a).trans (rightToFull_free sd fd a).symm)

lemma toFull_leftBase (b : B) : toFull sd fd (sd.baseLeft b) = fd.left b :=
  (sd.desc_left _ _ _ (sd.leftCylinder.base b)).trans
    (sd.leftCylinder.desc_base _ _ _ b)

lemma toFull_rightBase (c : C) : toFull sd fd (sd.baseRight c) = fd.d c :=
  (sd.desc_right _ _ _ (sd.rightCylinder.base c)).trans
    (sd.rightCylinder.desc_base _ _ _ c)

lemma toFull_leftInterval (s : I) (a : A) :
    toFull sd fd (sd.left (sd.leftCylinder.interval (s,a))) =
      fd.interval (leftCoordinate s,a) :=
  (sd.desc_left _ _ _ (sd.leftCylinder.interval (s,a))).trans
    (sd.leftCylinder.desc_interval _ _ _ (s,a))

lemma toFull_rightInterval (s : I) (a : A) :
    toFull sd fd (sd.right (sd.rightCylinder.interval (s,a))) =
      fd.interval (rightCoordinate s,a) :=
  (sd.desc_right _ _ _ (sd.rightCylinder.interval (s,a))).trans
    (sd.rightCylinder.desc_interval _ _ _ (s,a))

lemma toFull_common (a : A) : toFull sd fd (sd.common a) = fd.interval (midpoint,a) :=
  (sd.desc_common _ _ _ a).trans (leftToFull_free sd fd a)

/-- Traverse the left split cylinder backwards, from its attached end to the free end. -/
def leftPath : (i ≫ sd.baseLeft).hom.Homotopy sd.common.hom where
  toContinuousMap := ⟨fun p => sd.left (sd.leftCylinder.interval (unitInterval.symm p.1,p.2)),
    by fun_prop⟩
  map_zero_left a := by
    change sd.left (sd.leftCylinder.interval (unitInterval.symm 0,a)) = _
    rw [unitInterval.symm_zero]
    exact congrArg sd.left (sd.leftCylinder.interval_one a)
  map_one_left a := by
    change sd.left (sd.leftCylinder.interval (unitInterval.symm 1,a)) = _
    rw [unitInterval.symm_one]
    rfl

/-- Start the right path at the very same common-A point, not an assumed equal point. -/
def rightPath : sd.common.hom.Homotopy (j ≫ sd.baseRight).hom where
  toContinuousMap := ⟨fun p => sd.right (sd.rightCylinder.interval p), by fun_prop⟩
  map_zero_left a := (congrArg sd.right (sd.rightCylinder.interval_zero a)).trans
    (sd.common_right a).symm
  map_one_left a := congrArg sd.right (sd.rightCylinder.interval_one a)

/-- Upstream Homotopy.trans is the actual closed pasting at t=1/2.
Its endpoints coincide by the two paths' literal common endpoint. -/
def joinedPath : (i ≫ sd.baseLeft).hom.Homotopy (j ≫ sd.baseRight).hom :=
  (leftPath sd).trans (rightPath sd)

def toSplit : fd.D ⟶ sd.S :=
  fd.desc sd.baseLeft (TopCat.ofHom (joinedPath sd).toContinuousMap) sd.baseRight
    (fun a => ((joinedPath sd).map_zero_left a).symm)
    (fun a => (joinedPath sd).map_one_left a)

lemma toSplit_left (b : B) : toSplit sd fd (fd.left b) = sd.baseLeft b :=
  fd.desc_left _ _ _ _ _ b

lemma toSplit_right (c : C) : toSplit sd fd (fd.d c) = sd.baseRight c :=
  fd.desc_right _ _ _ _ _ c

lemma toSplit_interval (t : I) (a : A) :
    toSplit sd fd (fd.interval (t,a)) = joinedPath sd (t,a) :=
  fd.desc_interval _ _ _ _ _ (t,a)

/-- Literal closed-pasting inverse formula, including the left branch at the seam. -/
lemma toSplit_interval_formula (t : I) (a : A) :
    toSplit sd fd (fd.interval (t,a)) =
      if h : (t : ℝ) ≤ 1 / 2 then
        sd.left (sd.leftCylinder.interval
          (unitInterval.symm ⟨2 * (t : ℝ),
            (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.property.1,h⟩⟩,a))
      else
        sd.right (sd.rightCylinder.interval
          (⟨2 * (t : ℝ) - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le,t.property.2⟩⟩,a)) :=
  (toSplit_interval sd fd t a).trans
    (ContinuousMap.Homotopy.trans_apply (leftPath sd) (rightPath sd) (t,a))

/-- The left half, including its free endpoint/midpoint, is recovered exactly. -/
lemma joined_leftCoordinate (s : I) (a : A) :
    joinedPath sd (leftCoordinate s,a) = sd.left (sd.leftCylinder.interval (s,a)) := by
  change ((leftPath sd).trans (rightPath sd)) (leftCoordinate s,a) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs with h
  · change sd.left (sd.leftCylinder.interval (unitInterval.symm _,a)) = _
    apply congrArg (fun u : I => sd.left (sd.leftCylinder.interval (u,a)))
    apply Subtype.ext
    change 1 - 2 * ((1 - (s : ℝ)) / 2) = (s : ℝ)
    ring
  · exact False.elim (h (leftCoordinate_le_half s))

/-- At s=0 the left branch is chosen; the actual common_right equation handles it. -/
lemma joined_rightCoordinate (s : I) (a : A) :
    joinedPath sd (rightCoordinate s,a) = sd.right (sd.rightCylinder.interval (s,a)) := by
  by_cases hs : s = 0
  · subst s
    rw [rightCoordinate_zero, ← leftCoordinate_zero]
    exact (joined_leftCoordinate sd 0 a).trans (sd.common_right a)
  · have ht : ¬ (rightCoordinate s : ℝ) ≤ 1 / 2 := by
      intro ht
      apply hs
      apply Subtype.ext
      change (s : ℝ) = 0
      change (1 + (s : ℝ)) / 2 ≤ 1 / 2 at ht
      have h0 := s.property.1
      linarith
    change ((leftPath sd).trans (rightPath sd)) (rightCoordinate s,a) = _
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with h
    · exact False.elim (ht h)
    · change sd.right (sd.rightCylinder.interval (_,a)) = _
      apply congrArg (fun u : I => sd.right (sd.rightCylinder.interval (u,a)))
      apply Subtype.ext
      change 2 * ((1 + (s : ℝ)) / 2) - 1 = (s : ℝ)
      ring

lemma toFull_toSplit : toFull sd fd ≫ toSplit sd fd = 𝟙 sd.S := by
  have hL : sd.left ≫ toFull sd fd ≫ toSplit sd fd = sd.left := by
    apply sd.leftCylinder.hom_ext
    · intro b
      change toSplit sd fd (toFull sd fd (sd.baseLeft b)) = sd.baseLeft b
      rw [toFull_leftBase, toSplit_left]
    · rintro ⟨s,a⟩
      change toSplit sd fd (toFull sd fd (sd.left (sd.leftCylinder.interval (s,a)))) = _
      rw [toFull_leftInterval, toSplit_interval]
      exact joined_leftCoordinate sd s a
  have hR : sd.right ≫ toFull sd fd ≫ toSplit sd fd = sd.right := by
    apply sd.rightCylinder.hom_ext
    · intro c
      change toSplit sd fd (toFull sd fd (sd.baseRight c)) = sd.baseRight c
      rw [toFull_rightBase, toSplit_right]
    · rintro ⟨s,a⟩
      change toSplit sd fd (toFull sd fd (sd.right (sd.rightCylinder.interval (s,a)))) = _
      rw [toFull_rightInterval, toSplit_interval]
      exact joined_rightCoordinate sd s a
  apply sd.hom_ext
  · intro x
    exact ConcreteCategory.congr_hom hL x
  · intro x
    exact ConcreteCategory.congr_hom hR x

lemma toSplit_toFull : toSplit sd fd ≫ toFull sd fd = 𝟙 fd.D := by
  apply fd.hom_ext
  · intro b
    change toFull sd fd (toSplit sd fd (fd.left b)) = fd.left b
    rw [toSplit_left, toFull_leftBase]
  · rintro ⟨t,a⟩
    change toFull sd fd (toSplit sd fd (fd.interval (t,a))) = fd.interval (t,a)
    rw [toSplit_interval]
    change toFull sd fd (((leftPath sd).trans (rightPath sd)) (t,a)) = fd.interval (t,a)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · let u : I := ⟨2 * (t : ℝ),
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.property.1,ht⟩⟩
      change toFull sd fd (sd.left (sd.leftCylinder.interval (unitInterval.symm u,a))) = _
      rw [toFull_leftInterval]
      apply congrArg (fun v : I => fd.interval (v,a))
      apply Subtype.ext
      change (1 - (1 - 2 * (t : ℝ))) / 2 = (t : ℝ)
      ring
    · let u : I := ⟨2 * (t : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le,t.property.2⟩⟩
      change toFull sd fd (sd.right (sd.rightCylinder.interval (u,a))) = _
      rw [toFull_rightInterval]
      apply congrArg (fun v : I => fd.interval (v,a))
      apply Subtype.ext
      change (1 + (2 * (t : ℝ) - 1)) / 2 = (t : ℝ)
      ring
  · intro c
    change toFull sd fd (toSplit sd fd (fd.d c)) = fd.d c
    rw [toSplit_right, toFull_rightBase]

/-- Actual homeomorphism, not a homotopy equivalence supplied as a premise. -/
def homeomorph : sd.S ≃ₜ fd.D where
  toFun := toFull sd fd
  invFun := toSplit sd fd
  left_inv z := ConcreteCategory.congr_hom (toFull_toSplit sd fd) z
  right_inv z := ConcreteCategory.congr_hom (toSplit_toFull sd fd) z
  continuous_toFun := (toFull sd fd).hom.continuous
  continuous_invFun := (toSplit sd fd).hom.continuous

@[simp] lemma homeomorph_apply (z : sd.S) : homeomorph sd fd z = toFull sd fd z := rfl
@[simp] lemma homeomorph_symm_apply (z : fd.D) :
    (homeomorph sd fd).symm z = toSplit sd fd z := rfl

end AutomaticCoherence.SplitFullDoubleCylinder01
