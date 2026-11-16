module
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FunProp

/-! SOURCE ONLY / UNCOMPILED. A joint reverse-loop/loop cancellation family.
No compatibility or constancy of the supplied loop is assumed. -/
@[expose] public section
noncomputable section
open ContinuousMap
open scoped Topology
namespace AutomaticCoherence.LoopCancellation01

abbrev I := unitInterval

def foldedClock (s : I) : I :=
  ⟨|2 * (s : ℝ) - 1|, abs_nonneg _, abs_le.mpr (by
    have hs0 := s.property.1
    have hs1 := s.property.2
    constructor <;> linarith)⟩

lemma continuous_foldedClock : Continuous foldedClock := by
  unfold foldedClock
  fun_prop

@[simp] lemma foldedClock_zero : foldedClock 0 = 1 := by
  apply Subtype.ext
  norm_num [foldedClock]

@[simp] lemma foldedClock_one : foldedClock 1 = 1 := by
  apply Subtype.ext
  norm_num [foldedClock]

def clock (v s : I) : I := Set.Icc.convexComb (foldedClock s) 1 v

lemma clock_coe (v s : I) :
    (clock v s : ℝ) = (v : ℝ) + (1 - (v : ℝ)) * |2 * (s : ℝ) - 1| := by
  simp only [clock, Set.Icc.coe_convexComb, foldedClock, Set.Icc.coe_one]
  ring

lemma continuous_clock : Continuous (fun p : I × I => clock p.1 p.2) :=
  Set.Icc.continuous_convexComb_prod.comp
    ((continuous_foldedClock.comp continuous_snd).prodMk
      (continuous_const.prodMk continuous_fst))

@[simp] lemma clock_zero (s : I) : clock 0 s = foldedClock s := by simp [clock]
@[simp] lemma clock_one (s : I) : clock 1 s = 1 := by simp [clock]
@[simp] lemma clock_left (v : I) : clock v 0 = 1 := by simp [clock]
@[simp] lemma clock_right (v : I) : clock v 1 = 1 := by simp [clock]

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : C(X,Y)} (H : f.Homotopy f)

lemma reverse_trans_apply (s : I) (x : X) :
    (H.symm.trans H) (s,x) = H (foldedClock s,x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs with hs
  · simp only [ContinuousMap.Homotopy.symm_apply]
    apply congrArg (fun t : I => H (t,x))
    apply Subtype.ext
    change 1 - 2 * (s : ℝ) = |2 * (s : ℝ) - 1|
    rw [abs_of_nonpos (by linarith)]
    ring
  · apply congrArg (fun t : I => H (t,x))
    apply Subtype.ext
    change 2 * (s : ℝ) - 1 = |2 * (s : ℝ) - 1|
    rw [abs_of_nonneg (by linarith)]

/-- This is joint in outer time, loop parameter, and the arbitrary source point. -/
def cancellationFamily : C(I × (I × X),Y) where
  toFun p := H (clock p.1 p.2.1,p.2.2)
  continuous_toFun := H.continuous.comp
    ((continuous_clock.comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd))

lemma cancellationFamily_zero (s : I) (x : X) :
    cancellationFamily H (0,(s,x)) = (H.symm.trans H) (s,x) := by
  change H (clock 0 s,x) = _
  rw [clock_zero]
  exact (reverse_trans_apply H s x).symm

lemma cancellationFamily_one (s : I) (x : X) :
    cancellationFamily H (1,(s,x)) = f x := by
  change H (clock 1 s,x) = _
  rw [clock_one]
  exact H.map_one_left x

lemma cancellationFamily_left (v : I) (x : X) :
    cancellationFamily H (v,(0,x)) = f x := by
  change H (clock v 0,x) = _
  rw [clock_left]
  exact H.map_one_left x

lemma cancellationFamily_right (v : I) (x : X) :
    cancellationFamily H (v,(1,x)) = f x := by
  change H (clock v 1,x) = _
  rw [clock_right]
  exact H.map_one_left x

/-- A homotopy between the two maps I×X→Y, fixed on both parameter ends. -/
def cancellation : (H.symm.trans H).toContinuousMap.Homotopy
    (f.comp ContinuousMap.snd) where
  toContinuousMap := cancellationFamily H
  map_zero_left p := cancellationFamily_zero H p.1 p.2
  map_one_left p := cancellationFamily_one H p.1 p.2

def parameterEnds : Set (I × X) := {p | p.1 = 0 ∨ p.1 = 1}

def cancellationRel : (H.symm.trans H).toContinuousMap.HomotopyRel
    (f.comp ContinuousMap.snd) (parameterEnds (X := X)) where
  toHomotopy := cancellation H
  prop' v p hp := by
    rcases p with ⟨s,x⟩
    change s = 0 ∨ s = 1 at hp
    rcases hp with hs | hs
    · subst s
      exact (cancellationFamily_left H v x).trans
        ((H.symm.trans H).map_zero_left x).symm
    · subst s
      exact (cancellationFamily_right H v x).trans
        ((H.symm.trans H).map_one_left x).symm

end AutomaticCoherence.LoopCancellation01
