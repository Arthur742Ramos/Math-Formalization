/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import Mathlib.Computability.PartrecCode

@[expose] public section

namespace LambdaTuring.EffectiveCode

open Nat.Partrec

/-- A recursive program together with its exact partial-function semantics.
    Unlike an existential proposition, this carries the syntax as data. -/
structure Witness (f : Nat →. Nat) where
  code : Code
  sound : Code.eval code = f

def zero : Witness (pure 0) := ⟨.zero, rfl⟩
def succ : Witness Nat.succ := ⟨.succ, rfl⟩
def left : Witness (↑fun n : Nat => n.unpair.1) := ⟨.left, rfl⟩
def right : Witness (↑fun n : Nat => n.unpair.2) := ⟨.right, rfl⟩

def ofEq {f g : Nat →. Nat} (w : Witness f) (h : f = g) : Witness g :=
  ⟨w.code, w.sound.trans h⟩

def pair {f g : Nat →. Nat} (wf : Witness f) (wg : Witness g) :
    Witness (fun n => Nat.pair <$> f n <*> g n) :=
  ⟨.pair wf.code wg.code, by simp only [Code.eval, wf.sound, wg.sound]; rfl⟩

def comp {f g : Nat →. Nat} (wf : Witness f) (wg : Witness g) :
    Witness (fun n => g n >>= f) :=
  ⟨.comp wf.code wg.code, by simp only [Code.eval, wf.sound, wg.sound]; rfl⟩

def prec {f g : Nat →. Nat} (wf : Witness f) (wg : Witness g) :
    Witness (Nat.unpaired fun a n => n.rec (f a) fun y ih => do
      let i ← ih
      g (Nat.pair a (Nat.pair y i))) :=
  ⟨.prec wf.code wg.code, by simp only [Code.eval, wf.sound, wg.sound]; rfl⟩

def rfind {f : Nat →. Nat} (wf : Witness f) :
    Witness (fun a => Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)) := by
  refine ⟨.comp (.rfind' wf.code) (.pair Code.id .zero), ?_⟩
  simp only [Code.eval, wf.sound]
  simp [Seq.seq, pure, PFun.pure, Part.map_id']
  rfl

/-- Explicit code for a total numerical function. -/
structure TotalWitness (f : Nat → Nat) where
  code : Code
  sound : ∀ n, Code.eval code n = Part.some (f n)

namespace TotalWitness

def toWitness {f : Nat → Nat} (w : TotalWitness f) : Witness f :=
  ⟨w.code, funext w.sound⟩

def ofEq {f g : Nat → Nat} (w : TotalWitness f) (h : ∀ n, f n = g n) : TotalWitness g :=
  ⟨w.code, fun n => (w.sound n).trans (congrArg Part.some (h n))⟩

def zero : TotalWitness (fun _ => 0) := ⟨.zero, fun _ => rfl⟩
def succ : TotalWitness Nat.succ := ⟨.succ, fun _ => rfl⟩
def left : TotalWitness (fun n => n.unpair.1) := ⟨.left, fun _ => rfl⟩
def right : TotalWitness (fun n => n.unpair.2) := ⟨.right, fun _ => rfl⟩
def const (n : Nat) : TotalWitness (fun _ => n) := ⟨Code.const n, Code.eval_const n⟩

def pair {f g : Nat → Nat} (wf : TotalWitness f) (wg : TotalWitness g) :
    TotalWitness (fun n => Nat.pair (f n) (g n)) := by
  refine ⟨.pair wf.code wg.code, ?_⟩
  intro n
  simp [Code.eval, wf.sound n, wg.sound n, Seq.seq]

def comp {f g : Nat → Nat} (wf : TotalWitness f) (wg : TotalWitness g) :
    TotalWitness (fun n => f (g n)) := by
  refine ⟨.comp wf.code wg.code, ?_⟩
  intro n
  change (Code.eval wg.code n).bind (fun k => Code.eval wf.code k) = _
  rw [wg.sound n, Part.bind_some, wf.sound]

def prec {f g : Nat → Nat} (wf : TotalWitness f) (wg : TotalWitness g) :
    TotalWitness (Nat.unpaired fun z n => n.rec (f z) fun y ih =>
      g (Nat.pair z (Nat.pair y ih))) := by
  refine ⟨.prec wf.code wg.code, ?_⟩
  intro n
  generalize hp : Nat.unpair n = p
  rcases p with ⟨a, k⟩
  have h : n = Nat.pair a k := by
    have h := Nat.pair_unpair n
    rw [hp] at h
    exact h.symm
  subst n
  clear hp
  induction k with
  | zero => simpa [Nat.unpaired] using wf.sound a
  | succ k ih =>
    simp only [Nat.unpaired, Nat.unpair_pair]
    rw [Code.eval_prec_succ, ih]
    simpa using wg.sound (Nat.pair a (Nat.pair k _))

end TotalWitness

#print axioms zero
#print axioms pair
#print axioms prec
#print axioms rfind
#print axioms TotalWitness.prec
end LambdaTuring.EffectiveCode
