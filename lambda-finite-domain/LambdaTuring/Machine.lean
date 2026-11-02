/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import Lean

@[expose] public section

/-! An executable finite-state Post–Turing machine with a concrete numerical
observation. Correspondence with Mathlib's quotient tape model remains to be proved. -/

namespace LambdaTuring.Machine

inductive Symbol where
  | blank | one | mark
  deriving DecidableEq, Repr

inductive Action where
  | left | right | write (s : Symbol)
  deriving DecidableEq, Repr

/-- The nearest cell occurs first on each side; missing cells are blank. -/
structure Tape where
  left : List Symbol
  head : Symbol
  right : List Symbol
  deriving DecidableEq, Repr

def moveLeft (t : Tape) : Tape :=
  match t.left with
  | [] => ⟨[], .blank, t.head :: t.right⟩
  | a :: l => ⟨l, a, t.head :: t.right⟩

def moveRight (t : Tape) : Tape :=
  match t.right with
  | [] => ⟨t.head :: t.left, .blank, []⟩
  | a :: r => ⟨t.head :: t.left, a, r⟩

def perform (a : Action) (t : Tape) : Tape :=
  match a with
  | .left => moveLeft t
  | .right => moveRight t
  | .write s => { t with head := s }

/-- The table is indexed by three consecutive symbols per state. Missing
entries halt; extra entries are unreachable. State zero is the initial state. -/
structure Program (states : Nat) where
  table : List (Option (Fin (states + 1) × Action))
  deriving DecidableEq, Repr

def symbolIndex : Symbol → Nat
  | .blank => 0
  | .one => 1
  | .mark => 2

def instruction {states : Nat} (p : Program states) (q : Fin (states + 1))
    (s : Symbol) : Option (Fin (states + 1) × Action) :=
  (p.table[q.val * 3 + symbolIndex s]?).getD none

structure Config (states : Nat) where
  state : Fin (states + 1)
  tape : Tape
  deriving DecidableEq, Repr

def step {states : Nat} (p : Program states) (c : Config states) : Option (Config states) :=
  (instruction p c.state c.tape.head).map fun (q, a) => ⟨q, perform a c.tape⟩

inductive Reaches {states : Nat} (p : Program states) : Config states → Config states → Prop where
  | refl (c : Config states) : Reaches p c c
  | step {a b c} : Machine.step p a = some b → Reaches p b c → Reaches p a c

def Halted {states : Nat} (p : Program states) (c : Config states) : Prop := step p c = none

theorem halted_reaches_eq {states : Nat} {p : Program states} {a b : Config states}
    (h : Halted p a) (r : Reaches p a b) : a = b := by
  cases r with
  | refl => rfl
  | step s _ =>
    change step p a = none at h
    rw [h] at s
    cases s

theorem terminal_unique {states : Nat} {p : Program states} {a b c : Config states}
    (ab : Reaches p a b) (ac : Reaches p a c) (hb : Halted p b) (hc : Halted p c) : b = c := by
  induction ab generalizing c with
  | refl => exact halted_reaches_eq hb ac
  | @step a next b hs reach ih =>
    cases ac with
    | refl => exact (halted_reaches_eq hc (.step hs reach)).symm
    | @step _ next' c hs' reach' =>
      have eqnext : next = next' := Option.some.inj (hs.symm.trans hs')
      subst next'
      exact ih reach' hb hc

/-- All symbols following a first blank must themselves be blanks. -/
def blanksOnly : List Symbol → Bool
  | [] => true
  | .blank :: xs => blanksOnly xs
  | _ :: _ => false

/-- Count ones until the infinite blank tail; malformed output returns none. -/
def unaryCount : List Symbol → Option Nat
  | [] => some 0
  | .one :: xs => (unaryCount xs).map (· + 1)
  | .blank :: xs => if blanksOnly xs then some 0 else none
  | .mark :: _ => none

/-- A positive unary count represents its predecessor; an empty output is malformed. -/
def decode (xs : List Symbol) : Option Nat :=
  match unaryCount xs with
  | some (n + 1) => some n
  | _ => none

def input (n : Nat) : List Symbol := List.replicate (n + 1) .one

def initial {states : Nat} (n : Nat) : Config states :=
  ⟨⟨0, Nat.zero_lt_succ states⟩, ⟨[], .one, List.replicate n .one⟩⟩

/-- A numerical observation is a reached terminal configuration with a valid output. -/
def Yields {states : Nat} (p : Program states) (n m : Nat) : Prop :=
  ∃ c, Reaches p (initial n) c ∧ Halted p c ∧ decode (c.tape.head :: c.tape.right) = some m

theorem yields_unique {states : Nat} {p : Program states} {n m k : Nat}
    (hm : Yields p n m) (hk : Yields p n k) : m = k := by
  obtain ⟨a, ha, ah, ao⟩ := hm
  obtain ⟨b, hb, bh, bo⟩ := hk
  have eq : a = b := terminal_unique ha hb ah bh
  subst b
  exact Option.some.inj (ao.symm.trans bo)

/-- A machine that halts immediately. Its initial configuration can still fail
    to produce a number if its tape contains a marker. -/
def immediateHalt : Program 0 := ⟨[]⟩

example : Halted immediateHalt ⟨⟨0, by decide⟩, ⟨[], .mark, []⟩⟩ := rfl
example : decode [.mark] = none := rfl
example : decode [.one, .one, .blank, .blank] = some 1 := rfl
example : decode [.one, .blank, .one] = none := rfl



theorem blanksOnly_replicate (n : Nat) : blanksOnly (List.replicate n .blank) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate, blanksOnly] using ih

theorem blanksOnly_append_blanks (xs : List Symbol) (n : Nat) :
    blanksOnly (xs ++ List.replicate n .blank) = blanksOnly xs := by
  induction xs with
  | nil => simpa [blanksOnly] using blanksOnly_replicate n
  | cons x xs ih => cases x <;> simp [blanksOnly, ih]

theorem unaryCount_blanks (n : Nat) : unaryCount (List.replicate n .blank) = some 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [List.replicate, unaryCount, blanksOnly_replicate]

theorem unaryCount_append_blanks (xs : List Symbol) (n : Nat) :
    unaryCount (xs ++ List.replicate n .blank) = unaryCount xs := by
  induction xs with
  | nil => simpa [unaryCount] using unaryCount_blanks n
  | cons x xs ih => cases x <;> simp [unaryCount, ih, blanksOnly_append_blanks]

/-- Numerical observations are invariant under extension of the represented tape by blanks. -/
theorem decode_append_blanks (xs : List Symbol) (n : Nat) :
    decode (xs ++ List.replicate n .blank) = decode xs := by
  simp only [decode, unaryCount_append_blanks]
theorem unaryCount_replicate (n : Nat) : unaryCount (List.replicate n .one) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate, unaryCount, ih]

theorem decode_input (n : Nat) : decode (input n) = some n := by
  simp [input, decode, unaryCount_replicate]

/-- This finite table writes a marker on input and then halts. -/
def markHalt : Program 1 :=
  ⟨[none, some (⟨1, by decide⟩, .write .mark)]⟩

def marked (n : Nat) : Config 1 :=
  ⟨⟨1, by decide⟩, ⟨[], .mark, List.replicate n .one⟩⟩

theorem mark_reaches (n : Nat) : Reaches markHalt (initial n) (marked n) := by
  apply Reaches.step (b := marked n)
  · rfl
  · exact .refl _

theorem mark_halts (n : Nat) : Halted markHalt (marked n) := rfl

/-- Halting need not imply a numerical result: the output can be malformed. -/
theorem mark_no_numerical_result (n m : Nat) : ¬ Yields markHalt n m := by
  rintro ⟨c, hc, hh, ho⟩
  have eq : c = marked n := terminal_unique hc (mark_reaches n) hh (mark_halts n)
  subst c
  simp [marked, decode, unaryCount] at ho

#print axioms decode_append_blanks
#print axioms decode_input
#print axioms mark_no_numerical_result
#print axioms terminal_unique
#print axioms yields_unique

end LambdaTuring.Machine
