/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPS
public meta import LambdaTuring.CPS

@[expose] public section

namespace LambdaTuring

def churchBodyIndex (f n : Nat) : Term :=
  match n with
  | 0 => .var 0
  | n + 1 => .app (.var f) (churchBodyIndex f n)

theorem subst_churchBody_var1 (n : Nat) :
    substAt 1 (.var 1) (churchBody n) = churchBodyIndex 2 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [churchBody, churchBodyIndex, substAt, liftBy, liftFrom, ih]

theorem subst_churchBodyIndex_var0 (n : Nat) :
    substAt 0 (.var 0) (churchBodyIndex 2 n) = churchBody n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [churchBody, churchBodyIndex, substAt, ih]

theorem church_apply_vars (n : Nat) :
    Reaches (.app (.app (church n) (.var 1)) (.var 0)) (churchBody n) := by
  have hb1 : Beta (.app (church n) (.var 1)) (.abs (churchBodyIndex 2 n)) := by
    simpa [church, substAt, subst_churchBody_var1] using
      (Beta.contract (.abs (churchBody n)) (.var 1))
  have hb2 : Beta (.app (.abs (churchBodyIndex 2 n)) (.var 0)) (churchBody n) := by
    simpa [subst_churchBodyIndex_var0] using (Beta.contract (churchBodyIndex 2 n) (.var 0))
  exact .step (.appLeft hb1) (.step hb2 (.refl _))

theorem reaches_abs {a b : Term} (h : Reaches a b) : Reaches (.abs a) (.abs b) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.abs s) ih

/-- Standard Church successor on the present de Bruijn terms. -/
def churchSuccessor : Term :=
  .abs (.abs (.abs (.app (.var 1) (.app (.app (.var 2) (.var 1)) (.var 0)))))

theorem churchSuccessor_closed : Scoped 0 churchSuccessor := by
  simp [churchSuccessor, Scoped]

theorem churchSuccessor_run (n : Nat) :
    Reaches (.app churchSuccessor (church n)) (church (n + 1)) := by
  have hlift : liftFrom 0 (church n) = church n :=
    liftFrom_scoped (church n) 0 0 (church_closed n) (le_refl _)
  have hshift : liftBy 2 (church n) = church n := by simp [liftBy, hlift]
  have hb : Beta (.app churchSuccessor (church n))
      (.abs (.abs (.app (.var 1) (.app (.app (church n) (.var 1)) (.var 0))))) := by
    simpa [churchSuccessor, substAt, hshift] using
      (Beta.contract (.abs (.abs (.app (.var 1) (.app (.app (.var 2) (.var 1)) (.var 0))))) (church n))
  apply Reaches.step hb
  exact reaches_abs (reaches_abs (reaches_appRight (.var 1) (church_apply_vars n)))

theorem churchSuccessor_represents : Represents churchSuccessor (Nat.Partrec.Code.eval .succ) := by
  constructor
  · exact churchSuccessor_closed
  · intro n
    change numericalValue churchSuccessor n = Part.some (n + 1)
    rw [numericalValue_some_iff]
    exact churchSuccessor_run n

def cpsSuccessor : Term :=
  .abs (.abs (.app (.var 0) (.app churchSuccessor (.var 1))))

theorem cpsSuccessor_run (n : Nat) (K : Term) :
    Reaches (.app (.app cpsSuccessor (church n)) K) (.app K (church (n + 1))) := by
  have hs1 := substAt_scoped churchSuccessor 1 (church n)
    (scoped_mono churchSuccessor_closed (Nat.zero_le 1))
  have hs0 := substAt_scoped churchSuccessor 0 K churchSuccessor_closed
  have hn0 := substAt_scoped (church n) 0 K (church_closed n)
  have hshift : liftBy 1 (church n) = church n := by
    simpa [liftBy] using liftFrom_scoped (church n) 0 0 (church_closed n) (le_refl _)
  have hb1 : Beta (.app cpsSuccessor (church n))
      (.abs (.app (.var 0) (.app churchSuccessor (church n)))) := by
    simpa [cpsSuccessor, substAt, hs1, hshift] using
      (Beta.contract (.abs (.app (.var 0) (.app churchSuccessor (.var 1)))) (church n))
  have hb2 : Beta (.app (.abs (.app (.var 0) (.app churchSuccessor (church n)))) K)
      (.app K (.app churchSuccessor (church n))) := by
    simpa [substAt, liftBy, hs0, hn0] using
      (Beta.contract (.app (.var 0) (.app churchSuccessor (church n))) K)
  exact .step (.appLeft hb1) (.step hb2 (reaches_appRight K (churchSuccessor_run n)))

theorem cpsSuccessor_represents : CPSRepresents cpsSuccessor (Nat.Partrec.Code.eval .succ) := by
  constructor
  · change Scoped 2 (.app (.var 0) (.app churchSuccessor (.var 1)))
    exact ⟨by simp [Scoped], scoped_mono churchSuccessor_closed (Nat.zero_le 2), by simp [Scoped]⟩
  · intro n K
    constructor
    · intro m hm
      have heq : m = n + 1 := by simpa [Nat.Partrec.Code.eval] using hm
      subst m
      exact cpsSuccessor_run n K
    · intro hnone
      simp [Nat.Partrec.Code.eval] at hnone

#print axioms churchSuccessor_run
#print axioms churchSuccessor_represents
#print axioms cpsSuccessor_represents

end LambdaTuring
