module
public import Mathlib.Topology.Homotopy.Basic

/-! SOURCE ONLY / UNCOMPILED.
One fixed scalar schedule for six right-associated binary homotopy stages.
The clock is 0,0,identity,1,1,1 with exactly the same concatenation tree.
It is not identified with the six-equal-slot clamp from the mathematical notes. -/
@[expose] public noncomputable section
open ContinuousMap
open scoped Topology

namespace AutomaticCoherence.SixStageSchedule01
abbrev I := unitInterval

def zeroClock :
    (ContinuousMap.const PUnit (0 : I)).Homotopy (ContinuousMap.const PUnit (0 : I)) :=
  ContinuousMap.Homotopy.refl _

def oneClock :
    (ContinuousMap.const PUnit (1 : I)).Homotopy (ContinuousMap.const PUnit (1 : I)) :=
  ContinuousMap.Homotopy.refl _

def movingClock :
    (ContinuousMap.const PUnit (0 : I)).Homotopy (ContinuousMap.const PUnit (1 : I)) where
  toContinuousMap := ⟨Prod.fst, continuous_fst⟩
  map_zero_left _ := rfl
  map_one_left _ := rfl

def clock :
    (ContinuousMap.const PUnit (0 : I)).Homotopy (ContinuousMap.const PUnit (1 : I)) :=
  zeroClock.trans (zeroClock.trans (movingClock.trans
    (oneClock.trans (oneClock.trans oneClock))))

def schedule : C(I,I) :=
  clock.{0}.toContinuousMap.comp ⟨fun t => (t,PUnit.unit), by fun_prop⟩

@[simp] lemma schedule_zero : schedule 0 = 0 := clock.map_zero_left PUnit.unit
@[simp] lemma schedule_one : schedule 1 = 1 := clock.map_one_left PUnit.unit

section
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f₀ f₁ f₂ : C(X,Y)} {r₀ r₁ r₂ : I}

/-- Exact evaluation under binary concatenation, with no continuity assumption on R. -/
lemma trans_restriction
    (H : f₀.Homotopy f₁) (K : f₁.Homotopy f₂)
    (P : (ContinuousMap.const PUnit r₀).Homotopy (ContinuousMap.const PUnit r₁))
    (Q : (ContinuousMap.const PUnit r₁).Homotopy (ContinuousMap.const PUnit r₂))
    (x : X) (R : I → Y)
    (hH : ∀ t, H (t,x) = R (P (t,PUnit.unit)))
    (hK : ∀ t, K (t,x) = R (Q (t,PUnit.unit))) (t : I) :
    (H.trans K) (t,x) = R ((P.trans Q) (t,PUnit.unit)) := by
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hH _
  · exact hK _
end

section
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : C(X,Y)}
  (H₁ : f₀.Homotopy f₁) (H₂ : f₁.Homotopy f₂)
  (H₃ : f₂.Homotopy f₃) (H₄ : f₃.Homotopy f₄)
  (H₅ : f₄.Homotopy f₅) (H₆ : f₅.Homotopy f₆)

def concatenate : f₀.Homotopy f₆ :=
  H₁.trans (H₂.trans (H₃.trans (H₄.trans (H₅.trans H₆))))

/-- All-time restriction follows from the identical binary tree, not endpoint agreement alone. -/
lemma concatenate_restriction (x : X) (R : I → Y)
    (h₁ : ∀ t, H₁ (t,x) = R 0) (h₂ : ∀ t, H₂ (t,x) = R 0)
    (h₃ : ∀ t, H₃ (t,x) = R t)
    (h₄ : ∀ t, H₄ (t,x) = R 1) (h₅ : ∀ t, H₅ (t,x) = R 1)
    (h₆ : ∀ t, H₆ (t,x) = R 1) (t : I) :
    concatenate H₁ H₂ H₃ H₄ H₅ H₆ (t,x) = R (schedule t) := by
  have h₅₆ := trans_restriction H₅ H₆ oneClock oneClock x R h₅ h₆
  have h₄₅₆ := trans_restriction H₄ (H₅.trans H₆)
    oneClock (oneClock.trans oneClock) x R h₄ h₅₆
  have h₃₄₅₆ := trans_restriction H₃ (H₄.trans (H₅.trans H₆))
    movingClock (oneClock.trans (oneClock.trans oneClock)) x R h₃ h₄₅₆
  have h₂₃₄₅₆ := trans_restriction H₂ (H₃.trans (H₄.trans (H₅.trans H₆)))
    zeroClock (movingClock.trans (oneClock.trans (oneClock.trans oneClock)))
    x R h₂ h₃₄₅₆
  exact trans_restriction H₁ (H₂.trans (H₃.trans (H₄.trans (H₅.trans H₆))))
    zeroClock (zeroClock.trans (movingClock.trans
      (oneClock.trans (oneClock.trans oneClock)))) x R h₁ h₂₃₄₅₆ t
end

end AutomaticCoherence.SixStageSchedule01
