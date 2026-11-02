/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodePairTM0
public meta import LambdaTuring.ListCodePairTM0
public import LambdaTuring.ListCodeUnpair
public meta import LambdaTuring.ListCodeUnpair

@[expose] public section

namespace LambdaTuring

/-- The executable fragment now handles both numeric projections and all
    compositions and pairings generated from the supported codes. -/
def compileListCodeProjection : Nat.Partrec.Code → Option Turing.ToPartrec.Code
  | .left => some listCodeUnpairLeft
  | .right => some listCodeUnpairRight
  | .pair f g => do
      let F ← compileListCodeProjection f
      let G ← compileListCodeProjection g
      pure (.comp listCodeNatPair (listCodeTuple F G))
  | .comp f g => do
      let F ← compileListCodeProjection f
      let G ← compileListCodeProjection g
      pure (.comp F G)
  | c => compileListCode c

theorem listCode_left : ListCodeRepresents listCodeUnpairLeft (Nat.Partrec.Code.eval .left) := by
  intro n
  simpa [Nat.Partrec.Code.eval, Part.map_eq_map] using listCodeUnpairLeft_eval n

theorem listCode_right : ListCodeRepresents listCodeUnpairRight (Nat.Partrec.Code.eval .right) := by
  intro n
  simpa [Nat.Partrec.Code.eval, Part.map_eq_map] using listCodeUnpairRight_eval n

theorem compileListCodeProjection_sound (c : Nat.Partrec.Code) (C : Turing.ToPartrec.Code)
    (h : compileListCodeProjection c = some C) : ListCodeRepresents C (Nat.Partrec.Code.eval c) := by
  induction c generalizing C with
  | zero => exact compileListCode_sound .zero C h
  | succ => exact compileListCode_sound .succ C h
  | left =>
    have hC : listCodeUnpairLeft = C := by simpa [compileListCodeProjection] using h
    subst C
    exact listCode_left
  | right =>
    have hC : listCodeUnpairRight = C := by simpa [compileListCodeProjection] using h
    subst C
    exact listCode_right
  | prec f g ihf ihg => exact compileListCode_sound (.prec f g) C h
  | rfind' f ih => exact compileListCode_sound (.rfind' f) C h
  | comp f g ihf ihg =>
    cases hf : compileListCodeProjection f with
    | none => simp [compileListCodeProjection, hf] at h
    | some F =>
      cases hg : compileListCodeProjection g with
      | none => simp [compileListCodeProjection, hf, hg] at h
      | some G =>
        have heq : Turing.ToPartrec.Code.comp F G = C := by
          simpa [compileListCodeProjection, hf, hg] using h
        subst C
        have heval : Nat.Partrec.Code.eval (.comp f g) =
            (fun n => (Nat.Partrec.Code.eval g n).bind (Nat.Partrec.Code.eval f)) := by
          funext n
          exact Part.bind_eq_bind _ _
        rw [heval]
        exact listCode_comp (ihf F hf) (ihg G hg)
  | pair f g ihf ihg =>
    cases hf : compileListCodeProjection f with
    | none => simp [compileListCodeProjection, hf] at h
    | some F =>
      cases hg : compileListCodeProjection g with
      | none => simp [compileListCodeProjection, hf, hg] at h
      | some G =>
        have heq : Turing.ToPartrec.Code.comp listCodeNatPair (listCodeTuple F G) = C := by
          simpa [compileListCodeProjection, hf, hg] using h
        subst C
        have heval : Nat.Partrec.Code.eval (.pair f g) =
            (fun n => (Nat.Partrec.Code.eval f n).bind
              (fun a => (Nat.Partrec.Code.eval g n).map (Nat.pair a))) := by
          rw [codePair_eval]
          funext n
          simp [numericalPairBind, Part.bind_some_eq_map]
        rw [heval]
        exact listCode_pair_of_encoder (ihf F hf) (ihg G hg) listCodeNatPair_eval

inductive ListCodeProjectionSupported : Nat.Partrec.Code → Prop where
  | zero : ListCodeProjectionSupported .zero
  | succ : ListCodeProjectionSupported .succ
  | left : ListCodeProjectionSupported .left
  | right : ListCodeProjectionSupported .right
  | bottom : ListCodeProjectionSupported bottomCode
  | comp {f g} : ListCodeProjectionSupported f → ListCodeProjectionSupported g → ListCodeProjectionSupported (.comp f g)
  | pair {f g} : ListCodeProjectionSupported f → ListCodeProjectionSupported g → ListCodeProjectionSupported (.pair f g)

theorem compileListCodeProjection_complete {c : Nat.Partrec.Code} (hc : ListCodeProjectionSupported c) :
    ∃ C, compileListCodeProjection c = some C := by
  induction hc with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨listCodeUnpairLeft, rfl⟩
  | right => exact ⟨listCodeUnpairRight, rfl⟩
  | bottom => exact ⟨listCodeBottom, by simp [compileListCodeProjection, compileListCode, bottomCode]⟩
  | @comp f g _ _ ihf ihg =>
    obtain ⟨F, hF⟩ := ihf
    obtain ⟨G, hG⟩ := ihg
    exact ⟨.comp F G, by simp [compileListCodeProjection, hF, hG]⟩
  | @pair f g _ _ ihf ihg =>
    obtain ⟨F, hF⟩ := ihf
    obtain ⟨G, hG⟩ := ihg
    exact ⟨.comp listCodeNatPair (listCodeTuple F G), by simp [compileListCodeProjection, hF, hG]⟩

set_option linter.style.haveILetI false in
theorem compileListCodeProjection_lambda_tm0 (c : Nat.Partrec.Code)
    (C : Turing.ToPartrec.Code) (h : compileListCodeProjection c = some C) (n m : Nat) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    (∃ out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ m ∈ numericalValue (compileLambdaTotal c) n := by
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  have hrep := (compileListCodeProjection_sound c C h) n
  rw [(compileLambdaTotal_sound c).2 n]
  constructor
  · rintro ⟨out, hout, hdecode⟩
    have hd : (C.eval [n]).Dom := (tm0List_domain C [n]).1 (Part.dom_iff_mem.2 ⟨out, hout⟩)
    obtain ⟨ys, hys⟩ := Part.dom_iff_mem.1 hd
    rw [hrep] at hys
    obtain ⟨k, hk, hys⟩ := (Part.mem_map_iff _).1 hys
    subst ys
    have hstack := tm0List_output_stack C [n] [k] out hout
      (by rw [hrep]; exact (Part.mem_map_iff _).2 ⟨k, hk, rfl⟩)
    simp only [tm0DecodedNumber, hstack, decodeSingleton_trList, Option.some.injEq] at hdecode
    simpa [hdecode] using hk
  · intro hm
    have hc : [m] ∈ C.eval [n] := by
      rw [hrep]
      exact (Part.mem_map_iff _).2 ⟨m, hm, rfl⟩
    have hd : (Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n])).Dom :=
      (tm0List_domain C [n]).2 (Part.dom_iff_mem.2 ⟨[m], hc⟩)
    obtain ⟨out, hout⟩ := Part.dom_iff_mem.1 hd
    refine ⟨out, hout, ?_⟩
    unfold tm0DecodedNumber
    rw [tm0List_output_stack C [n] [m] out hout hc]
    exact decodeSingleton_trList m

set_option linter.style.haveILetI false in
theorem compileListCodeProjection_lambda_tm0_none (c : Nat.Partrec.Code)
    (C : Turing.ToPartrec.Code) (h : compileListCodeProjection c = some C) (n : Nat) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    (¬ ∃ m out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ numericalValue (compileLambdaTotal c) n = Part.none := by
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  rw [Part.eq_none_iff]
  constructor
  · intro hnone m hm
    obtain ⟨out, hout, hdecode⟩ := (compileListCodeProjection_lambda_tm0 c C h n m).2 hm
    exact hnone ⟨m, out, hout, hdecode⟩
  · rintro hnone ⟨m, out, hout, hdecode⟩
    exact hnone m ((compileListCodeProjection_lambda_tm0 c C h n m).1 ⟨out, hout, hdecode⟩)

#print axioms compileListCodeProjection_sound
#print axioms compileListCodeProjection_complete
#print axioms compileListCodeProjection_lambda_tm0
#print axioms compileListCodeProjection_lambda_tm0_none
end LambdaTuring
