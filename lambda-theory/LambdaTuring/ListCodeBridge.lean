/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSTotalCompiler
public meta import LambdaTuring.CPSTotalCompiler
public import LambdaTuring.CPSBottom
public meta import LambdaTuring.CPSBottom
public import Mathlib.Computability.TuringMachine.ToPartrec

@[expose] public section

namespace LambdaTuring

/-- Exact singleton-list semantics for a unary numerical partial function. -/
def ListCodeRepresents (c : Turing.ToPartrec.Code) (f : Nat →. Nat) : Prop :=
  ∀ n, c.eval [n] = (f n).map (fun m => [m])

theorem listCode_zero : ListCodeRepresents Turing.ToPartrec.Code.zero (Nat.Partrec.Code.eval .zero) := by
  intro n
  change Turing.ToPartrec.Code.zero.eval [n] = (Part.some 0).map (fun m => [m])
  simp

theorem listCode_succ : ListCodeRepresents Turing.ToPartrec.Code.succ (Nat.Partrec.Code.eval .succ) := by
  intro n
  simp [Turing.ToPartrec.Code.succ_eval, Nat.Partrec.Code.eval]

theorem listCode_identity : ListCodeRepresents Turing.ToPartrec.Code.head (Nat.Partrec.Code.eval Nat.Partrec.Code.id) := by
  intro n
  rw [Nat.Partrec.Code.eval_id]
  simp [Turing.ToPartrec.Code.head_eval]

/-- A fixed-point program that repeats with the same input state forever. -/
def listCodeBottom : Turing.ToPartrec.Code := .fix (.cons .succ .id)

theorem listCodeBottom_none (xs : List Nat) : listCodeBottom.eval xs = Part.none := by
  let step : List Nat →. (List Nat ⊕ List Nat) := fun v =>
    ((Turing.ToPartrec.Code.cons .succ .id).eval v).map fun w =>
      if w.headI = 0 then Sum.inl w.tail else Sum.inr w.tail
  have hstep : ∀ v, step v = Part.some (Sum.inr v) := by
    intro v
    simp [step, Turing.ToPartrec.Code.cons_eval, Turing.ToPartrec.Code.succ_eval,
      Turing.ToPartrec.Code.id_eval, Part.bind_eq_bind]
  change PFun.fix step xs = Part.none
  apply Part.eq_none_iff.2
  intro result hresult
  apply PFun.fixInduction' hresult (C := fun _ => False)
  · intro v hstop
    rw [hstep v] at hstop
    simp at hstop
  · intro a b hrest hnext ih
    exact ih

theorem listCode_bottom : ListCodeRepresents listCodeBottom (Nat.Partrec.Code.eval bottomCode) := by
  intro n
  rw [listCodeBottom_none, bottomCode_eval]
  exact (Part.map_none _).symm

theorem listCode_comp {F G : Turing.ToPartrec.Code} {f g : Nat →. Nat}
    (hf : ListCodeRepresents F f) (hg : ListCodeRepresents G g) :
    ListCodeRepresents (.comp F G) (fun n => (g n).bind f) := by
  intro n
  apply Part.ext
  intro out
  change out ∈ (G.eval [n]).bind F.eval ↔ out ∈ ((g n).bind f).map (fun m => [m])
  rw [hg n]
  constructor
  · intro hout
    obtain ⟨v, hv, hout⟩ := Part.mem_bind_iff.1 hout
    obtain ⟨m, hm, rfl⟩ := (Part.mem_map_iff _).1 hv
    rw [hf m] at hout
    obtain ⟨k, hk, rfl⟩ := (Part.mem_map_iff _).1 hout
    exact (Part.mem_map_iff _).2 ⟨k, Part.mem_bind_iff.2 ⟨m, hm, hk⟩, rfl⟩
  · intro hout
    obtain ⟨k, hk, rfl⟩ := (Part.mem_map_iff _).1 hout
    obtain ⟨m, hm, hk⟩ := Part.mem_bind_iff.1 hk
    apply Part.mem_bind_iff.2
    refine ⟨[m], (Part.mem_map_iff _).2 ⟨m, hm, rfl⟩, ?_⟩
    rw [hf m]
    exact (Part.mem_map_iff _).2 ⟨k, hk, rfl⟩

/-- A first structural bridge for zero, successor, identity, one undefined
    code, and their compositions.
    `none` means the source syntax is not handled by this fragment. -/
def compileListCode : Nat.Partrec.Code → Option Turing.ToPartrec.Code
  | .zero => some .zero
  | .succ => some .succ
  | .pair f g =>
      if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some .head else none
  | .rfind' f =>
      if Encodable.encode (Nat.Partrec.Code.rfind' f) = Encodable.encode bottomCode then some listCodeBottom else none
  | .comp f g => do
      let F ← compileListCode f
      let G ← compileListCode g
      pure (.comp F G)
  | _ => none

inductive ListCodeSupported : Nat.Partrec.Code → Prop where
  | zero : ListCodeSupported .zero
  | succ : ListCodeSupported .succ
  | identity : ListCodeSupported Nat.Partrec.Code.id
  | bottom : ListCodeSupported bottomCode
  | comp {f g : Nat.Partrec.Code} : ListCodeSupported f → ListCodeSupported g → ListCodeSupported (.comp f g)

theorem compileListCode_complete {c : Nat.Partrec.Code} (hc : ListCodeSupported c) :
    ∃ C, compileListCode c = some C := by
  induction hc with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | identity => exact ⟨.head, by simp [compileListCode, Nat.Partrec.Code.id]⟩
  | bottom => exact ⟨listCodeBottom, by simp [compileListCode, bottomCode]⟩
  | @comp f g _ _ ihf ihg =>
    obtain ⟨F, hF⟩ := ihf
    obtain ⟨G, hG⟩ := ihg
    exact ⟨.comp F G, by simp [compileListCode, hF, hG]⟩

theorem compileListCode_sound (c : Nat.Partrec.Code) (C : Turing.ToPartrec.Code)
    (h : compileListCode c = some C) : ListCodeRepresents C (Nat.Partrec.Code.eval c) := by
  induction c generalizing C with
  | zero =>
    have heq : Turing.ToPartrec.Code.zero = C := by simpa [compileListCode] using h
    subst C
    exact listCode_zero
  | succ =>
    have heq : Turing.ToPartrec.Code.succ = C := by simpa [compileListCode] using h
    subst C
    exact listCode_succ
  | pair f g ihf ihg =>
    by_cases hi : Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id
    · have heq : Nat.Partrec.Code.pair f g = Nat.Partrec.Code.id := Encodable.encode_injective hi
      have hC : Turing.ToPartrec.Code.head = C := by simpa [compileListCode, hi] using h
      subst C
      rw [heq]
      exact listCode_identity
    · simp [compileListCode, hi] at h
  | rfind' f ih =>
    by_cases hi : Encodable.encode (Nat.Partrec.Code.rfind' f) = Encodable.encode bottomCode
    · have heq : Nat.Partrec.Code.rfind' f = bottomCode := Encodable.encode_injective hi
      have hC : listCodeBottom = C := by simpa [compileListCode, hi] using h
      subst C
      rw [heq]
      exact listCode_bottom
    · simp [compileListCode, hi] at h
  | comp f g ihf ihg =>
    cases hf : compileListCode f with
    | none => simp [compileListCode, hf] at h
    | some F =>
      cases hg : compileListCode g with
      | none => simp [compileListCode, hf, hg] at h
      | some G =>
        have heq : Turing.ToPartrec.Code.comp F G = C := by simpa [compileListCode, hf, hg] using h
        subst C
        have heval : Nat.Partrec.Code.eval (.comp f g) =
            (fun n => (Nat.Partrec.Code.eval g n).bind (Nat.Partrec.Code.eval f)) := by
          funext n
          exact Part.bind_eq_bind _ _
        rw [heval]
        exact listCode_comp (ihf F hf) (ihg G hg)
  | left | right | prec => simp [compileListCode] at h

/-- Mathlib's concrete TM2 evaluator preserves the translated fragment's
    exact singleton output and undefinedness. Its finite-support theorem and
    the later TM2-to-TM0 and tape-decoding bridges are separate obligations. -/
theorem compileListCode_tm2_eval (c : Nat.Partrec.Code) (C : Turing.ToPartrec.Code)
    (h : compileListCode c = some C) (n : Nat) :
    StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
      (Turing.PartrecToTM2.init C [n]) =
      (Nat.Partrec.Code.eval c n).map (fun m => Turing.PartrecToTM2.halt [m]) := by
  rw [Turing.PartrecToTM2.tr_eval, (compileListCode_sound c C h) n]
  change Part.map Turing.PartrecToTM2.halt (Part.map (fun m : Nat => [m]) (Nat.Partrec.Code.eval c n)) = _
  exact Part.map_map _ _ _

/-- The concrete list-code evaluator has a finite support containing its
    initial label, as required by Mathlib's later machine simulations. -/
theorem listCode_tm2_supports (C : Turing.ToPartrec.Code) :
    @Turing.TM2.Supports _ _ _ _ ⟨Turing.PartrecToTM2.trNormal C Turing.PartrecToTM2.Cont'.halt⟩
      Turing.PartrecToTM2.tr (Turing.PartrecToTM2.codeSupp C Turing.PartrecToTM2.Cont'.halt) :=
  Turing.PartrecToTM2.tr_supports C Turing.PartrecToTM2.Cont'.halt

theorem part_map_none_iff {α β : Type} (f : α → β) (p : Part α) : p.map f = Part.none ↔ p = Part.none := by
  constructor
  · intro h
    apply Part.eq_none_iff.2
    intro a ha
    have hm : f a ∈ p.map f := (Part.mem_map_iff _).2 ⟨a, ha, rfl⟩
    rw [h] at hm
    simp at hm
  · intro h
    rw [h]
    exact Part.map_none f

theorem compileListCode_tm2_none_iff (c : Nat.Partrec.Code) (C : Turing.ToPartrec.Code)
    (h : compileListCode c = some C) (n : Nat) :
    StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
      (Turing.PartrecToTM2.init C [n]) = Part.none ↔ Nat.Partrec.Code.eval c n = Part.none := by
  rw [compileListCode_tm2_eval c C h n]
  exact part_map_none_iff _ _

theorem compileListCode_bottom : compileListCode bottomCode = some listCodeBottom := by
  simp [compileListCode, bottomCode]

theorem compiledListBottom_tm2_none (n : Nat) :
    StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
      (Turing.PartrecToTM2.init listCodeBottom [n]) = Part.none := by
  rw [compileListCode_tm2_eval bottomCode listCodeBottom compileListCode_bottom n, bottomCode_eval]
  exact Part.map_none _

#print axioms listCode_comp
#print axioms listCodeBottom_none
#print axioms compileListCode_sound
#print axioms compileListCode_tm2_eval
#print axioms listCode_tm2_supports
#print axioms compileListCode_tm2_none_iff
#print axioms compiledListBottom_tm2_none

end LambdaTuring
