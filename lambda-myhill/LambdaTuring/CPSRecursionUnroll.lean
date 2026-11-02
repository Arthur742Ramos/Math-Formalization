/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSPair
public meta import LambdaTuring.CPSPair
public import LambdaTuring.CPSComposition
public meta import LambdaTuring.CPSComposition

@[expose] public section

/- Strict finite unrolling follows the related Isabelle CPS primitive recursion
   development, adapted to Mathlib's nested square-based numeric pairing. -/

namespace LambdaTuring

theorem bindSome_eq (v : Nat) (f : Nat → Part Nat) : (Part.some v).bind f = f v := by
  apply Part.ext
  intro m
  simp

theorem cpsConstant_total (a : Nat) : CPSRepresents (cpsConstant a) (fun _ => Part.some a) := by
  have h := cpsConstant_represents a
  have heq : Nat.Partrec.Code.eval (Nat.Partrec.Code.const a) = (fun _ => Part.some a) := by
    funext x
    exact Nat.Partrec.Code.eval_const a x
  rw [heq] at h
  exact h

theorem cpsIdentity_total : CPSRepresents cpsIdentity (fun x => Part.some x) := by
  have h := cpsIdentity_represents
  have heq : Nat.Partrec.Code.eval Nat.Partrec.Code.id = (fun x => Part.some x) := by
    funext x
    exact Nat.Partrec.Code.eval_id x
  rw [heq] at h
  exact h

/-- The step-code input `pair a (pair i previous)`, as a strict CPS program. -/
def cpsRecInput (a i : Nat) : Term :=
  cpsPair (cpsConstant a) (cpsPair (cpsConstant i) cpsIdentity)

theorem cpsRecInput_represents (a i : Nat) :
    CPSRepresents (cpsRecInput a i) (fun x => Part.some (Nat.pair a (Nat.pair i x))) := by
  have ha := cpsConstant_total a
  have hi := cpsConstant_total i
  have hx := cpsIdentity_total
  have h := cpsPair_represents ha (cpsPair_represents hi hx)
  have heq : numericalPairBind (fun _ => Part.some a)
      (numericalPairBind (fun _ => Part.some i) (fun x => Part.some x)) =
        (fun x => Part.some (Nat.pair a (Nat.pair i x))) := by
    funext x
    simp [numericalPairBind]
  rw [heq] at h
  exact h

/-- Finite host-level unrolling, parameterized by the fixed first argument.
    A later Church iterator must construct this unrolling inside the calculus. -/
def cpsRecUnroll (F G : Term) (a : Nat) : Nat → Term
  | 0 => cpsCompose F (cpsConstant a)
  | i + 1 => cpsCompose (cpsCompose G (cpsRecInput a i)) (cpsRecUnroll F G a i)

def partialRecUnroll (f g : Nat →. Nat) (a : Nat) : Nat → Part Nat
  | 0 => f a
  | i + 1 => (partialRecUnroll f g a i).bind (fun v => g (Nat.pair a (Nat.pair i v)))

theorem cpsRecUnroll_represents {F G : Term} {f g : Nat →. Nat}
    (hf : CPSRepresents F f) (hg : CPSRepresents G g) (a n : Nat) :
    CPSRepresents (cpsRecUnroll F G a n) (fun _ => partialRecUnroll f g a n) := by
  induction n with
  | zero =>
    have hc := cpsConstant_total a
    have h := cpsCompose_represents hf hc
    have heq : (fun _ : Nat => (Part.some a).bind f) = (fun _ => f a) := by
      funext x
      exact bindSome_eq a f
    rw [heq] at h
    exact h
  | succ n ih =>
    have hs := cpsCompose_represents hg (cpsRecInput_represents a n)
    have hs' : CPSRepresents (cpsCompose G (cpsRecInput a n))
        (fun v => g (Nat.pair a (Nat.pair n v))) := by
      have heq : (fun v => (Part.some (Nat.pair a (Nat.pair n v))).bind g) =
          (fun v => g (Nat.pair a (Nat.pair n v))) := by
        funext v
        exact bindSome_eq _ g
      rw [heq] at hs
      exact hs
    simpa [cpsRecUnroll, partialRecUnroll] using cpsCompose_represents hs' ih

/-- This statement identifies the finite unrolling with Mathlib's actual
    primitive-recursion evaluator, without claiming a uniform term compiler. -/
theorem partialRecUnroll_code (f g : Nat.Partrec.Code) (a n : Nat) :
    partialRecUnroll (Nat.Partrec.Code.eval f) (Nat.Partrec.Code.eval g) a n =
      Nat.Partrec.Code.eval (.prec f g) (Nat.pair a n) := by
  simp only [Nat.Partrec.Code.eval, Nat.unpaired, Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih => simp only [partialRecUnroll, ih, Part.bind_eq_bind]

#print axioms cpsRecUnroll_represents
#print axioms partialRecUnroll_code

end LambdaTuring
