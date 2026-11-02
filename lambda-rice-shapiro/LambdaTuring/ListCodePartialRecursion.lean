/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodeProjectionCompiler
public meta import LambdaTuring.ListCodeProjectionCompiler

@[expose] public section

namespace LambdaTuring

/-- Iteration whose next result is undefined if any intermediate step is. -/
def partialIter (g : Nat → Nat →. Nat) : Nat → Nat → Nat →. Nat
  | 0, _, x => Part.some x
  | k+1, i, x => (g i x).bind (partialIter g k (i+1))

def partialRecLoop (g : Nat → Nat →. Nat) (v : List Nat) (w : List Nat) :
    Part (List Nat ⊕ List Nat) :=
  (g w.headI w.tail.tail.headI).map fun x =>
    if w.tail.headI = 0 then Sum.inl ((w.headI+1) :: 0 :: x :: v)
    else Sum.inr ((w.headI+1) :: (w.tail.headI-1) :: x :: v)

theorem partialRecLoop_eval_zero (g : Nat → Nat →. Nat) (v : List Nat) (i x : Nat) :
    partialRecLoop g v (i :: 0 :: x :: v) =
      (g i x).map (fun r => Sum.inl ((i+1) :: 0 :: r :: v)) := by
  rfl

theorem partialRecLoop_eval_succ (g : Nat → Nat →. Nat) (v : List Nat) (i k x : Nat) :
    partialRecLoop g v (i :: (k+1) :: x :: v) =
      (g i x).map (fun r => Sum.inr ((i+1) :: k :: r :: v)) := by
  simp [partialRecLoop]

set_option backward.isDefEq.respectTransparency false in
/-- The decreasing counter forces exactly `k+1` strict steps, preserving
    undefinedness of every intermediate call. -/
theorem partialRecLoop_fix (g : Nat → Nat →. Nat) (v : List Nat) (k i x : Nat)
    (out : List Nat) :
    out ∈ PFun.fix (partialRecLoop g v) (i :: k :: x :: v) ↔
      ∃ r, r ∈ partialIter g (k+1) i x ∧ out = ((i+k+1) :: 0 :: r :: v) := by
  induction k generalizing i x with
  | zero =>
    rw [PFun.mem_fix_iff, partialRecLoop_eval_zero]
    simp [partialIter, Part.mem_map_iff, eq_comm]
  | succ k ih =>
    rw [PFun.mem_fix_iff, partialRecLoop_eval_succ]
    change _ ↔ ∃ r, r ∈ (g i x).bind (partialIter g (k+1) (i+1)) ∧
      out = ((i+(k+1)+1) :: 0 :: r :: v)
    simp only [Part.mem_bind_iff, Part.mem_map_iff, reduceCtorEq,
      and_false, exists_false, false_or, Sum.inr.injEq]
    constructor
    · rintro ⟨state, ⟨r, hr, rfl⟩, hout⟩
      obtain ⟨z, hz, heq⟩ := (ih (i+1) r).1 hout
      refine ⟨z, ⟨r, hr, hz⟩, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq
    · rintro ⟨z, ⟨r, hr, hz⟩, heq⟩
      refine ⟨(i+1) :: k :: r :: v, ⟨r, hr, rfl⟩, ?_⟩
      apply (ih (i+1) r).2
      exact ⟨z, hz, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq⟩

def partialRecMachine (G : Turing.ToPartrec.Code) (w : List Nat) :
    Part (List Nat ⊕ List Nat) :=
  (G.eval (w.headI :: w.tail.tail)).bind fun x =>
    Part.some (if w.tail.headI = 0
      then Sum.inl ((w.headI+1) :: (w.tail.headI-1) :: x.headI :: w.tail.tail.tail)
      else Sum.inr ((w.headI+1) :: (w.tail.headI-1) :: x.headI :: w.tail.tail.tail))

set_option backward.isDefEq.respectTransparency false in
theorem partialRecMachine_eval (G : Turing.ToPartrec.Code) (g : Nat → Nat →. Nat)
    (v : List Nat) (hg : ∀ i x, G.eval (i :: x :: v) = (g i x).map (fun r => [r]))
    (i k x : Nat) :
    partialRecMachine G (i :: k :: x :: v) = partialRecLoop g v (i :: k :: x :: v) := by
  simp [partialRecMachine, partialRecLoop, hg, Part.bind_some_eq_map, Part.map_map]
  by_cases hk : k = 0 <;> simp [hk, Function.comp_def]

set_option backward.isDefEq.respectTransparency false in
theorem partialRecMachine_fix (G : Turing.ToPartrec.Code) (g : Nat → Nat →. Nat)
    (v : List Nat) (hg : ∀ i x, G.eval (i :: x :: v) = (g i x).map (fun r => [r]))
    (k i x : Nat) (out : List Nat) :
    out ∈ PFun.fix (partialRecMachine G) (i :: k :: x :: v) ↔
      out ∈ PFun.fix (partialRecLoop g v) (i :: k :: x :: v) := by
  induction k generalizing i x with
  | zero =>
    rw [PFun.mem_fix_iff, PFun.mem_fix_iff, partialRecMachine_eval G g v hg,
      partialRecLoop_eval_zero]
    simp [Part.mem_map_iff]
  | succ k ih =>
    rw [PFun.mem_fix_iff, PFun.mem_fix_iff, partialRecMachine_eval G g v hg,
      partialRecLoop_eval_succ]
    simp only [Part.mem_map_iff, reduceCtorEq, and_false, exists_false, false_or,
      Sum.inr.injEq]
    constructor
    · rintro ⟨w, ⟨r, hr, rfl⟩, hout⟩
      exact ⟨(i+1) :: k :: r :: v, ⟨r, hr, rfl⟩, (ih (i+1) r).1 hout⟩
    · rintro ⟨w, ⟨r, hr, rfl⟩, hout⟩
      exact ⟨(i+1) :: k :: r :: v, ⟨r, hr, rfl⟩, (ih (i+1) r).2 hout⟩

set_option backward.isDefEq.respectTransparency false in
theorem partialIter_succ_end (g : Nat → Nat →. Nat) (n i x : Nat) :
    partialIter g (n+1) i x = (partialIter g n i x).bind (g (i+n)) := by
  induction n generalizing i x with
  | zero => simp [partialIter, Part.bind_some]
  | succ n ih =>
    change (g i x).bind (partialIter g (n+1) (i+1)) =
      ((g i x).bind (partialIter g n (i+1))).bind (g (i+(n+1)))
    rw [Part.bind_assoc]
    apply congrArg ((g i x).bind)
    funext y
    rw [ih]
    congr 2
    omega

theorem partialIter_eq_rec (g : Nat → Nat →. Nat) (n i x : Nat) :
    partialIter g n i x = Nat.rec (Part.some x) (fun a p => p.bind (g (i+a))) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [partialIter_succ_end, ih]

set_option backward.isDefEq.respectTransparency false in
theorem partialIter_bind_rec (f : Part Nat) (g : Nat → Nat →. Nat) (n i : Nat) :
    f.bind (partialIter g n i) = Nat.rec (motive := fun _ => Part Nat) f
      (fun a p => p.bind (g (i+a))) n := by
  induction n with
  | zero => simp [partialIter, Part.bind_some_right]
  | succ n ih =>
    have heq : partialIter g (n+1) i =
        (fun x => (partialIter g n i x).bind (g (i+n))) := by
      funext x
      exact partialIter_succ_end g n i x
    rw [heq, ← Part.bind_assoc, ih]

set_option backward.isDefEq.respectTransparency false in
theorem partialRecMachine_fix_eq (G : Turing.ToPartrec.Code) (g : Nat → Nat →. Nat)
    (v : List Nat) (hg : ∀ i x, G.eval (i :: x :: v) = (g i x).map (fun r => [r]))
    (n i x : Nat) :
    PFun.fix (partialRecMachine G) (i :: n :: x :: v) =
      (partialIter g (n+1) i x).map (fun r => ((i+n+1) :: 0 :: r :: v)) := by
  apply Part.ext
  intro out
  rw [partialRecMachine_fix G g v hg, partialRecLoop_fix]
  simp [Part.mem_map_iff, eq_comm]

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some in
set_option backward.isDefEq.respectTransparency false in
/-- Exact partial semantics of Mathlib's list-code recursion combinator. -/
theorem listCode_prec_partial (F G : Turing.ToPartrec.Code)
    (f : List Nat →. Nat) (g : Nat → Nat → List Nat →. Nat)
    (hf : ∀ v, F.eval v = (f v).map (fun r => [r]))
    (hg : ∀ i x v, G.eval (i :: x :: v) = (g i x v).map (fun r => [r]))
    (n : Nat) (v : List Nat) :
    (Turing.ToPartrec.Code.prec F G).eval (n :: v) =
      (Nat.rec (motive := fun _ => Part Nat) (f v)
        (fun a p => p.bind (fun x => g a x v)) n).map (fun r => [r]) := by
  cases n with
  | zero =>
    simp [Turing.ToPartrec.Code.prec, hf, Bind.bind, Part.bind_map,
      Part.bind_some_eq_map, Part.map_map, Function.comp_def]
  | succ n =>
    have hfix := partialRecMachine_fix_eq G (fun i x => g i x v) v (fun i x => hg i x v) n
    simp [Turing.ToPartrec.Code.prec, Part.bind_assoc, Bind.bind]
    simp only [hf, Part.bind_map, List.headI_cons]
    change (f v).bind (fun y => (PFun.fix (partialRecMachine G) (0 :: n :: y :: v)).bind
      (fun x => Part.some [x.tail.tail.headI])) = _
    simp only [hfix, Part.bind_some_eq_map, Part.map_map, Function.comp_def,
      List.tail_cons, List.headI_cons]
    have hr := partialIter_bind_rec (f v) (fun i x => g i x v) (n+1) 0
    simp only [zero_add] at hr
    rw [← Part.map_bind, hr]
    rfl

#print axioms partialRecLoop_fix
#print axioms partialRecMachine_fix
#print axioms partialIter_succ_end
#print axioms listCode_prec_partial
end LambdaTuring
