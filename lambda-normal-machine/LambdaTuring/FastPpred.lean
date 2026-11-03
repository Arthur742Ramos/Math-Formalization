/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EffectiveCode
public meta import LambdaTuring.EffectiveCode

@[expose] public section

namespace LambdaTuring.EffectiveCode
open Nat.Partrec

def predCode : Code :=
  .comp (.prec .zero (.comp .left .right)) (.pair .zero Code.id)

def zeroTestCode : Code :=
  .comp (.prec (Code.const 1) .zero) (.pair .zero Code.id)

theorem eval_predCode (n : Nat) : predCode.eval n = Part.some n.pred := by
  have h (k : Nat) : Code.eval (.prec .zero (.comp .left .right)) (Nat.pair 0 k) =
      Part.some k.pred := by
    induction k with
    | zero => rw [Code.eval_prec_zero]; rfl
    | succ k ih =>
      rw [Code.eval_prec_succ, ih]
      change (Part.some k.pred).bind
        (fun x => Code.eval (.comp .left .right) (Nat.pair 0 (Nat.pair k x))) = _
      rw [Part.bind_some]
      change (Code.eval .right (Nat.pair 0 (Nat.pair k k.pred))).bind
        (fun x => Code.eval .left x) = _
      have hr : Code.eval .right (Nat.pair 0 (Nat.pair k k.pred)) =
          Part.some (Nat.pair k k.pred) := by simp [Code.eval]
      rw [hr, Part.bind_some]
      simp [Code.eval]
  change (Code.eval (.pair .zero Code.id) n).bind
    (fun x => Code.eval (.prec .zero (.comp .left .right)) x) = _
  have hpair : Code.eval (.pair .zero Code.id) n = Part.some (Nat.pair 0 n) := by
    change Nat.pair <$> Part.some 0 <*> Code.eval Code.id n = _
    simp [Code.eval_id, Seq.seq]
  rw [hpair, Part.bind_some, h]

theorem eval_zeroTestCode (n : Nat) :
    zeroTestCode.eval n = Part.some (if n = 0 then 1 else 0) := by
  have h (k : Nat) : Code.eval (.prec (Code.const 1) .zero) (Nat.pair 0 k) =
      Part.some (if k = 0 then 1 else 0) := by
    induction k with
    | zero => simp [Code.eval_prec_zero, Code.eval_const]
    | succ k ih =>
      rw [Code.eval_prec_succ, ih]
      simp [Code.eval, Part.bind_some, pure, PFun.pure]
  change (Code.eval (.pair .zero Code.id) n).bind
    (fun x => Code.eval (.prec (Code.const 1) .zero) x) = _
  have hpair : Code.eval (.pair .zero Code.id) n = Part.some (Nat.pair 0 n) := by
    change Nat.pair <$> Part.some 0 <*> Code.eval Code.id n = _
    simp [Code.eval_id, Seq.seq]
  rw [hpair, Part.bind_some, h]

def ppredCode : Code :=
  .comp (.rfind' (.comp zeroTestCode .left)) (.pair Code.id predCode)

theorem eval_ppredCode (n : Nat) : ppredCode.eval n = (Nat.ppred n : Part Nat) := by
  have hpair : Code.eval (.pair Code.id predCode) n = Part.some (Nat.pair n n.pred) := by
    change Nat.pair <$> Code.eval Code.id n <*> Code.eval predCode n = _
    simp [Code.eval_id, eval_predCode, Seq.seq]
  have htest (k : Nat) : Code.eval (.comp zeroTestCode .left) (Nat.pair n k) =
      Part.some (if n = 0 then 1 else 0) := by
    change (Code.eval .left (Nat.pair n k)).bind (fun x => Code.eval zeroTestCode x) = _
    have hl : Code.eval .left (Nat.pair n k) = Part.some n := by simp [Code.eval]
    rw [hl, Part.bind_some, eval_zeroTestCode]
  change (Code.eval (.pair Code.id predCode) n).bind
    (fun x => Code.eval (.rfind' (.comp zeroTestCode .left)) x) = _
  rw [hpair, Part.bind_some]
  rw [Code.eval, Nat.unpaired, Nat.unpair_pair]
  simp only [htest]
  cases n with
  | zero =>
    apply Part.eq_none_iff.2
    intro m hm
    rcases (Part.mem_map_iff _).1 hm with ⟨k, hk, _⟩
    have := Nat.rfind_spec hk
    simp at this
  | succ n =>
    have h : Nat.rfind (fun _ => Part.some true) = Part.some 0 := by
      apply Part.eq_some_iff.2
      apply Nat.mem_rfind.2
      simp
    simp [h]

def ppredWitness : Witness (fun n => (Nat.ppred n : Part Nat)) := ⟨ppredCode, funext eval_ppredCode⟩
end LambdaTuring.EffectiveCode
