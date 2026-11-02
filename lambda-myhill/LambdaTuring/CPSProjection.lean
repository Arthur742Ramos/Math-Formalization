/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ChurchUnpair
public meta import LambdaTuring.ChurchUnpair

@[expose] public section

namespace LambdaTuring

/-- Lift a closed, total Church program into the strict CPS convention. -/
def cpsLiftTotal (M : Term) : Term :=
  .abs (.abs (.app (.var 0) (.app M (.var 1))))

theorem cpsLiftTotal_run {M : Term} (hM : Scoped 0 M) {n m : Nat}
    (h : Reaches (.app M (church n)) (church m)) (K : Term) :
    Reaches (.app (.app (cpsLiftTotal M) (church n)) K) (.app K (church m)) := by
  have hs1 := substAt_scoped M 1 (church n) (scoped_mono hM (Nat.zero_le 1))
  have hs0 := substAt_scoped M 0 K hM
  have hn0 := substAt_scoped (church n) 0 K (church_closed n)
  have hshift : liftBy 1 (church n) = church n := liftBy_closed 1 (church_closed n)
  have hb1 : Beta (.app (cpsLiftTotal M) (church n))
      (.abs (.app (.var 0) (.app M (church n)))) := by
    simpa [cpsLiftTotal, substAt, hs1, hshift] using
      (Beta.contract (.abs (.app (.var 0) (.app M (.var 1)))) (church n))
  have hb2 : Beta (.app (.abs (.app (.var 0) (.app M (church n)))) K)
      (.app K (.app M (church n))) := by
    simpa [substAt, liftBy, hs0, hn0] using
      (Beta.contract (.app (.var 0) (.app M (church n))) K)
  exact .step (.appLeft hb1) (.step hb2 (reaches_appRight K h))

theorem cpsLiftTotal_represents {M : Term} (hM : Scoped 0 M) (f : Nat → Nat)
    (hrun : ∀ n, Reaches (.app M (church n)) (church (f n))) :
    CPSRepresents (cpsLiftTotal M) (fun n => Part.some (f n)) := by
  constructor
  · change Scoped 2 (.app (.var 0) (.app M (.var 1)))
    exact ⟨by simp [Scoped], scoped_mono hM (Nat.zero_le 2), by simp [Scoped]⟩
  · intro n K
    constructor
    · intro m hm
      have heq : m = f n := by simpa using hm
      subst m
      exact cpsLiftTotal_run hM (hrun n) K
    · intro hnone
      simp at hnone

theorem cpsNumericLeft_represents :
    CPSRepresents (cpsLiftTotal churchNumericLeft) (Nat.Partrec.Code.eval .left) := by
  change CPSRepresents (cpsLiftTotal churchNumericLeft) (fun n => Part.some n.unpair.1)
  exact cpsLiftTotal_represents churchNumericLeft_closed (fun n => n.unpair.1) churchNumericLeft_run

theorem cpsNumericRight_represents :
    CPSRepresents (cpsLiftTotal churchNumericRight) (Nat.Partrec.Code.eval .right) := by
  change CPSRepresents (cpsLiftTotal churchNumericRight) (fun n => Part.some n.unpair.2)
  exact cpsLiftTotal_represents churchNumericRight_closed (fun n => n.unpair.2) churchNumericRight_run

#print axioms cpsNumericLeft_represents
#print axioms cpsNumericRight_represents

end LambdaTuring
