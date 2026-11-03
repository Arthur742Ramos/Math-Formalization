/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

The deliberate holes below state the comparison obligations only. They are
not imported by the Solution or its proof dependencies. The public definitions
of terms, beta reduction, finite machines and observation are concrete.
-/
module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Data.PFun

@[expose] public section

namespace LambdaTuring

/-- Untyped lambda terms with de Bruijn indices. -/
inductive Term where
  | var : Nat → Term
  | abs : Term → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

/-- Lift indices free at or above a cutoff. -/
def liftFrom (cutoff : Nat) : Term → Term
  | .var i => .var (if i < cutoff then i else i + 1)
  | .abs body => .abs (liftFrom (cutoff + 1) body)
  | .app f x => .app (liftFrom cutoff f) (liftFrom cutoff x)

def liftBy : Nat → Term → Term
  | 0, t => t
  | n + 1, t => liftFrom 0 (liftBy n t)

/-- Capture-avoiding substitution and removal of the discharged binder. -/
def substAt (depth : Nat) (value : Term) : Term → Term
  | .var i => if i = depth then liftBy depth value
      else .var (if depth < i then i - 1 else i)
  | .abs body => .abs (substAt (depth + 1) value body)
  | .app f x => .app (substAt depth value f) (substAt depth value x)

/-- Full compatible beta reduction, including both application branches and binders. -/
inductive Beta : Term → Term → Prop where
  | contract (body value : Term) : Beta (.app (.abs body) value) (substAt 0 value body)
  | abs {a b : Term} : Beta a b → Beta (.abs a) (.abs b)
  | appLeft {a b x : Term} : Beta a b → Beta (.app a x) (.app b x)
  | appRight {f a b : Term} : Beta a b → Beta (.app f a) (.app f b)

/-- Reflexive-transitive full-beta reachability. -/
inductive Reaches : Term → Term → Prop where
  | refl (t : Term) : Reaches t t
  | step {a b c : Term} : Beta a b → Reaches b c → Reaches a c

def churchBody : Nat → Term
  | 0 => .var 0
  | n + 1 => .app (.var 1) (churchBody n)

/-- Church numeral using variables 1 and 0 for the function and argument. -/
def church (n : Nat) : Term := .abs (.abs (churchBody n))

/-- All free indices lie below the supplied binder depth. -/
def Scoped (depth : Nat) : Term → Prop
  | .var i => i < depth
  | .abs body => Scoped (depth + 1) body
  | .app f x => Scoped depth f ∧ Scoped depth x

/-- A numerical observation is reachability of the corresponding Church numeral. -/
def NumericalResult (t : Term) (n m : Nat) : Prop :=
  Reaches (.app t (church n)) (church m)

/-- Exact partial numerical observation; its domain is existence of a numeral. -/
noncomputable def numericalValue (t : Term) (n : Nat) : Part Nat :=
  ⟨∃ m, NumericalResult t n m, fun h => Classical.choose h⟩

/-- A closed term represents a partial numerical function exactly. -/
def Represents (t : Term) (f : Nat →. Nat) : Prop :=
  Scoped 0 t ∧ ∀ n, numericalValue t n = f n

def LambdaComputable (f : Nat →. Nat) : Prop := ∃ t, Represents t f

namespace Machine

inductive Symbol where
  | blank | one | mark
  deriving DecidableEq, Repr

inductive Action where
  | left | right | write (s : Symbol)
  deriving DecidableEq, Repr

/-- Two finite tape sides with implicit blank tails. -/
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

/-- Finite transition table, with state zero initial and missing entries halting. -/
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

def blanksOnly : List Symbol → Bool
  | [] => true
  | .blank :: xs => blanksOnly xs
  | _ :: _ => false

def unaryCount : List Symbol → Option Nat
  | [] => some 0
  | .one :: xs => (unaryCount xs).map (· + 1)
  | .blank :: xs => if blanksOnly xs then some 0 else none
  | .mark :: _ => none

/-- A positive run of ones represents its predecessor; malformed output is none. -/
def decode (xs : List Symbol) : Option Nat :=
  match unaryCount xs with
  | some (n + 1) => some n
  | _ => none

/-- Unary input for n has n + 1 ones with the head at the first one. -/
def initial {states : Nat} (n : Nat) : Config states :=
  ⟨⟨0, Nat.zero_lt_succ states⟩, ⟨[], .one, List.replicate n .one⟩⟩

/-- A numerical result is a reached halt with a valid current/right output. -/
def Yields {states : Nat} (p : Program states) (n m : Nat) : Prop :=
  ∃ c, Reaches p (initial n) c ∧ Halted p c ∧ decode (c.tape.head :: c.tape.right) = some m


end Machine

def directTermNumber : Term → Nat
  | .app f x => Nat.succ (Nat.pair 2 (Nat.pair (directTermNumber f) (directTermNumber x)))
  | .abs body => Nat.succ (Nat.pair 1 (directTermNumber body))
  | .var n => Nat.succ (Nat.pair 0 n)


theorem normalMachine_exists :
    ∃ (states : Nat) (p : Machine.Program states), ∀ t : Term,
      (∀ n, Machine.Yields p (directTermNumber t) (n + 1) ↔ Reaches t (church n)) ∧
      (Machine.Yields p (directTermNumber t) 0 ↔
        (∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v) ∧ ¬ ∃ n, Reaches t (church n)) ∧
      ((¬ ∃ d, Machine.Reaches p (Machine.initial (directTermNumber t)) d ∧ Machine.Halted p d) ↔
        ¬ ∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v) ∧
      (∀ d, Machine.Reaches p (Machine.initial (directTermNumber t)) d → Machine.Halted p d →
        ∃ m, Machine.decode (d.tape.head :: d.tape.right) = some m) := by
  sorry

end LambdaTuring
