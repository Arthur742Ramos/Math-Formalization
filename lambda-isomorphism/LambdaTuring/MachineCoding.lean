/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.MachineRun
public meta import LambdaTuring.MachineRun
public import Mathlib.Computability.Primrec.List
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace LambdaTuring.Machine

def symbolEquiv : Symbol ≃ Fin 3 where
  toFun
    | .blank => 0
    | .one => 1
    | .mark => 2
  invFun n := if n.val = 0 then .blank else if n.val = 1 then .one else .mark
  left_inv := by intro s; cases s <;> rfl
  right_inv := by intro n; fin_cases n <;> rfl

instance : Primcodable Symbol := Primcodable.ofEquiv (Fin 3) symbolEquiv

def actionEquiv : Action ≃ Option (Option Symbol) where
  toFun
    | .left => none
    | .right => some none
    | .write s => some (some s)
  invFun
    | none => .left
    | some none => .right
    | some (some s) => .write s
  left_inv := by intro a; cases a <;> rfl
  right_inv := by intro a; rcases a with _ | (_ | s) <;> rfl

instance : Primcodable Action := Primcodable.ofEquiv (Option (Option Symbol)) actionEquiv

def tapeEquiv : Tape ≃ List Symbol × Symbol × List Symbol where
  toFun t := (t.left, t.head, t.right)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := by intro t; cases t; rfl
  right_inv := by intro p; rcases p with ⟨l, h, r⟩; rfl

instance : Primcodable Tape := Primcodable.ofEquiv (List Symbol × Symbol × List Symbol) tapeEquiv

def configEquiv (states : Nat) : Config states ≃ Fin (states + 1) × Tape where
  toFun c := (c.state, c.tape)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by intro c; cases c; rfl
  right_inv := by intro p; cases p; rfl

instance (states : Nat) : Primcodable (Config states) :=
  Primcodable.ofEquiv (Fin (states + 1) × Tape) (configEquiv states)

theorem primrec_tapeParts : Primrec tapeEquiv := Primrec.of_equiv
theorem primrec_tapeMk : Primrec tapeEquiv.symm := Primrec.of_equiv_symm
theorem primrec_configParts (states : Nat) : Primrec (configEquiv states) := Primrec.of_equiv
theorem primrec_configMk (states : Nat) : Primrec (configEquiv states).symm := Primrec.of_equiv_symm

theorem primrec_tapeLeft : Primrec Tape.left :=
  Primrec.fst.comp primrec_tapeParts
theorem primrec_tapeHead : Primrec Tape.head :=
  Primrec.fst.comp (Primrec.snd.comp primrec_tapeParts)
theorem primrec_tapeRight : Primrec Tape.right :=
  Primrec.snd.comp (Primrec.snd.comp primrec_tapeParts)

theorem primrec_moveLeft : Primrec moveLeft := by
  have hl : Primrec (fun t : Tape => t.left.tail) := Primrec.list_tail.comp primrec_tapeLeft
  have hh : Primrec (fun t : Tape => t.left.head?.getD .blank) :=
    Primrec.option_getD.comp (Primrec.list_head?.comp primrec_tapeLeft) (Primrec.const Symbol.blank)
  have hr : Primrec (fun t : Tape => t.head :: t.right) :=
    Primrec.list_cons.comp primrec_tapeHead primrec_tapeRight
  have h := primrec_tapeMk.comp (hl.pair (hh.pair hr))
  apply h.of_eq
  intro t
  cases t with
  | mk l h r => cases l <;> rfl

theorem primrec_moveRight : Primrec moveRight := by
  have hl : Primrec (fun t : Tape => t.head :: t.left) :=
    Primrec.list_cons.comp primrec_tapeHead primrec_tapeLeft
  have hh : Primrec (fun t : Tape => t.right.head?.getD .blank) :=
    Primrec.option_getD.comp (Primrec.list_head?.comp primrec_tapeRight) (Primrec.const Symbol.blank)
  have hr : Primrec (fun t : Tape => t.right.tail) := Primrec.list_tail.comp primrec_tapeRight
  have h := primrec_tapeMk.comp (hl.pair (hh.pair hr))
  apply h.of_eq
  intro t
  cases t with
  | mk l h r => cases r <;> rfl

theorem primrec_symbolIndex : Primrec symbolIndex := by
  have h : Primrec (fun s : Symbol => (symbolEquiv s).val) :=
    Primrec.fin_val.comp Primrec.of_equiv
  exact h.of_eq (fun s => by cases s <;> rfl)

theorem primrec_write : Primrec₂ (fun (t : Tape) (s : Symbol) => { t with head := s }) := by
  have hl := primrec_tapeLeft.comp (Primrec.fst : Primrec (fun p : Tape × Symbol => p.1))
  have hr := primrec_tapeRight.comp (Primrec.fst : Primrec (fun p : Tape × Symbol => p.1))
  exact (primrec_tapeMk.comp (hl.pair (Primrec.snd.pair hr))).of_eq (fun ⟨t, s⟩ => by cases t; rfl)

theorem primrec_perform : Primrec₂ perform := by
  let P := Action × Tape
  have ha : Primrec (fun p : P => p.1) := Primrec.fst
  have ht : Primrec (fun p : P => p.2) := Primrec.snd
  have hcode : Primrec (fun p : P => actionEquiv p.1) := Primrec.of_equiv.comp ha
  have hs : Primrec (fun p : P => ((actionEquiv p.1).getD none).getD Symbol.blank) :=
    Primrec.option_getD.comp (Primrec.option_getD.comp hcode (Primrec.const none))
      (Primrec.const Symbol.blank)
  have hl : Primrec (fun p : P => moveLeft p.2) := primrec_moveLeft.comp ht
  have hr : Primrec (fun p : P => moveRight p.2) := primrec_moveRight.comp ht
  have hw : Primrec (fun p : P => { p.2 with head := ((actionEquiv p.1).getD none).getD Symbol.blank }) :=
    primrec_write.comp ht hs
  have h : Primrec (fun p : P => if p.1 = .left then moveLeft p.2 else
      if p.1 = .right then moveRight p.2 else
        { p.2 with head := ((actionEquiv p.1).getD none).getD Symbol.blank }) :=
    Primrec.ite (Primrec.eq.comp ha (Primrec.const Action.left)) hl
      (Primrec.ite (Primrec.eq.comp ha (Primrec.const Action.right)) hr hw)
  exact h.of_eq (fun ⟨a, t⟩ => by cases a <;> rfl)

theorem primrec_instruction {states : Nat} (p : Program states) :
    Primrec₂ (instruction p) := by
  let P := Fin (states + 1) × Symbol
  have hq : Primrec (fun x : P => x.1.val) := Primrec.fin_val.comp Primrec.fst
  have hs : Primrec (fun x : P => symbolIndex x.2) := primrec_symbolIndex.comp Primrec.snd
  have hi : Primrec (fun x : P => x.1.val * 3 + symbolIndex x.2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp hq (Primrec.const 3)) hs
  exact Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.const p.table) hi) (Primrec.const none)

theorem primrec_step {states : Nat} (p : Program states) : Primrec (step p) := by
  have hparts : Primrec (configEquiv states) := primrec_configParts states
  have hstate : Primrec (fun c : Config states => c.state) := Primrec.fst.comp hparts
  have htape : Primrec (fun c : Config states => c.tape) := Primrec.snd.comp hparts
  have hi : Primrec (fun c : Config states => instruction p c.state c.tape.head) :=
    primrec_instruction p |>.comp hstate (primrec_tapeHead.comp htape)
  have hnext : Primrec₂ (fun (c : Config states) (qa : Fin (states + 1) × Action) =>
      (⟨qa.1, perform qa.2 c.tape⟩ : Config states)) := by
    have hq : Primrec (fun x : Config states × (Fin (states + 1) × Action) => x.2.1) :=
      Primrec.fst.comp Primrec.snd
    have ha : Primrec (fun x : Config states × (Fin (states + 1) × Action) => x.2.2) :=
      Primrec.snd.comp Primrec.snd
    have ht : Primrec (fun x : Config states × (Fin (states + 1) × Action) => x.1.tape) :=
      htape.comp Primrec.fst
    exact (primrec_configMk states).comp (hq.pair (primrec_perform.comp ha ht))
  exact Primrec.option_map hi hnext

theorem primrec_blanksOnly : Primrec blanksOnly := by
  have hstep : Primrec₂ (fun (_ : List Symbol) (p : Symbol × Bool) =>
      if p.1 = Symbol.blank then p.2 else false) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const Symbol.blank))
      (Primrec.snd.comp Primrec.snd) (Primrec.const false)
  have h := Primrec.list_foldr (Primrec.id : Primrec (fun xs : List Symbol => xs))
    (Primrec.const true) hstep
  apply h.of_eq
  intro xs
  simp only [id_eq]
  induction xs with
  | nil => rfl
  | cons s xs ih =>
    cases s with
    | blank => change _ = blanksOnly xs; exact ih
    | one => rfl
    | mark => rfl

theorem primrec_unaryCount : Primrec unaryCount := by
  let P := Symbol × List Symbol × Option Nat
  let Q := List Symbol × P
  have hs : Primrec (fun q : Q => q.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun q : Q => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun q : Q => q.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hone : Primrec (fun q : Q => q.2.2.2.map Nat.succ) :=
    Primrec.option_map₁ Primrec.succ |>.comp hr
  have hblank : Primrec (fun q : Q => if blanksOnly q.2.2.1 then some 0 else none) :=
    Primrec.ite (Primrec.eq.comp (primrec_blanksOnly.comp ht) (Primrec.const true))
      (Primrec.const (some 0)) (Primrec.const none)
  have hstep : Primrec₂ (fun (_ : List Symbol) (p : P) =>
      if p.1 = Symbol.one then p.2.2.map Nat.succ else
      if p.1 = Symbol.blank then (if blanksOnly p.2.1 then some 0 else none) else none) :=
    Primrec.ite (Primrec.eq.comp hs (Primrec.const Symbol.one)) hone
      (Primrec.ite (Primrec.eq.comp hs (Primrec.const Symbol.blank)) hblank (Primrec.const none))
  have h := Primrec.list_rec (Primrec.id : Primrec (fun xs : List Symbol => xs))
    (Primrec.const (some 0)) hstep
  apply h.of_eq
  intro xs
  simp only [id_eq]
  induction xs with
  | nil => rfl
  | cons s xs ih =>
    cases s with
    | blank => rfl
    | one => change Option.map Nat.succ _ = Option.map (fun x => x + 1) (unaryCount xs); rw [ih]
    | mark => rfl

theorem primrec_decode : Primrec decode := by
  have hs : Primrec₂ (fun (_ : List Symbol) (n : Nat) =>
      if n = 0 then none else some (n - 1)) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const none)
      (Primrec.option_some.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
  have h := Primrec.option_casesOn primrec_unaryCount (Primrec.const none) hs
  apply h.of_eq
  intro xs
  cases hcount : unaryCount xs with
  | none => simp [decode, hcount]
  | some n => cases n <;> simp [decode, hcount]

theorem primrec_replicateOne : Primrec (fun n => List.replicate n Symbol.one) := by
  have hs : Primrec₂ (fun (_ : Nat) (p : Nat × List Symbol) => Symbol.one :: p.2) :=
    Primrec.list_cons.comp (Primrec.const Symbol.one) (Primrec.snd.comp Primrec.snd)
  have h := Primrec.nat_rec (Primrec.const ([] : List Symbol)) hs
  have h' := h.comp (Primrec.const (0 : Nat)) (Primrec.id : Primrec (fun n : Nat => n))
  apply h'.of_eq
  intro n
  simp only [id_eq]
  induction n with
  | zero => rfl
  | succ n ih => change Symbol.one :: _ = Symbol.one :: _; rw [ih]

theorem primrec_initial (states : Nat) : Primrec (initial (states := states)) := by
  have ht : Primrec (fun n : Nat => (⟨[], Symbol.one, List.replicate n Symbol.one⟩ : Tape)) :=
    primrec_tapeMk.comp ((Primrec.const []).pair ((Primrec.const Symbol.one).pair primrec_replicateOne))
  exact (primrec_configMk states).comp ((Primrec.const (⟨0, Nat.zero_lt_succ states⟩ : Fin (states + 1))).pair ht)

#print axioms primrec_tapeParts
#print axioms primrec_configMk
#print axioms primrec_moveLeft
#print axioms primrec_moveRight
#print axioms primrec_step
#print axioms primrec_decode
#print axioms primrec_initial

end LambdaTuring.Machine
