/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodeArithmetic
public meta import LambdaTuring.ListCodeArithmetic

@[expose] public section

namespace LambdaTuring

/-- Extend the executable list-code fragment to arbitrary strict pairing.
    Unsupported syntax still returns `none`. -/
def compileListCodePair : Nat.Partrec.Code → Option Turing.ToPartrec.Code
  | .pair f g =>
      if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some .head
      else do
        let F ← compileListCodePair f
        let G ← compileListCodePair g
        pure (.comp listCodeNatPair (listCodeTuple F G))
  | .comp f g => do
      let F ← compileListCodePair f
      let G ← compileListCodePair g
      pure (.comp F G)
  | c => compileListCode c

theorem compileListCodePair_sound (c : Nat.Partrec.Code) (C : Turing.ToPartrec.Code)
    (h : compileListCodePair c = some C) : ListCodeRepresents C (Nat.Partrec.Code.eval c) := by
  induction c generalizing C with
  | zero => exact compileListCode_sound .zero C h
  | succ => exact compileListCode_sound .succ C h
  | left => exact compileListCode_sound .left C h
  | right => exact compileListCode_sound .right C h
  | prec f g ihf ihg => exact compileListCode_sound (.prec f g) C h
  | rfind' f ih => exact compileListCode_sound (.rfind' f) C h
  | comp f g ihf ihg =>
    cases hf : compileListCodePair f with
    | none => simp [compileListCodePair, hf] at h
    | some F =>
      cases hg : compileListCodePair g with
      | none => simp [compileListCodePair, hf, hg] at h
      | some G =>
        have heq : Turing.ToPartrec.Code.comp F G = C := by
          simpa [compileListCodePair, hf, hg] using h
        subst C
        have heval : Nat.Partrec.Code.eval (.comp f g) =
            (fun n => (Nat.Partrec.Code.eval g n).bind (Nat.Partrec.Code.eval f)) := by
          funext n
          exact Part.bind_eq_bind _ _
        rw [heval]
        exact listCode_comp (ihf F hf) (ihg G hg)
  | pair f g ihf ihg =>
    by_cases hi : Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id
    · have heq : Nat.Partrec.Code.pair f g = Nat.Partrec.Code.id := Encodable.encode_injective hi
      have hC : Turing.ToPartrec.Code.head = C := by simpa [compileListCodePair, hi] using h
      subst C
      rw [heq]
      exact listCode_identity
    · cases hf : compileListCodePair f with
      | none => simp [compileListCodePair, hi, hf] at h
      | some F =>
        cases hg : compileListCodePair g with
        | none => simp [compileListCodePair, hi, hf, hg] at h
        | some G =>
          have heq : Turing.ToPartrec.Code.comp listCodeNatPair (listCodeTuple F G) = C := by
            simpa [compileListCodePair, hi, hf, hg] using h
          subst C
          have heval : Nat.Partrec.Code.eval (.pair f g) =
              (fun n => (Nat.Partrec.Code.eval f n).bind
                (fun a => (Nat.Partrec.Code.eval g n).map (Nat.pair a))) := by
            rw [codePair_eval]
            funext n
            simp [numericalPairBind, Part.bind_some_eq_map]
          rw [heval]
          exact listCode_pair_of_encoder (ihf F hf) (ihg G hg) listCodeNatPair_eval

inductive ListCodePairSupported : Nat.Partrec.Code → Prop where
  | zero : ListCodePairSupported .zero
  | succ : ListCodePairSupported .succ
  | identity : ListCodePairSupported Nat.Partrec.Code.id
  | bottom : ListCodePairSupported bottomCode
  | comp {f g} : ListCodePairSupported f → ListCodePairSupported g → ListCodePairSupported (.comp f g)
  | pair {f g} : ListCodePairSupported f → ListCodePairSupported g → ListCodePairSupported (.pair f g)

theorem compileListCodePair_complete {c : Nat.Partrec.Code} (hc : ListCodePairSupported c) :
    ∃ C, compileListCodePair c = some C := by
  induction hc with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | identity => exact ⟨.head, by simp [compileListCodePair, Nat.Partrec.Code.id]⟩
  | bottom => exact ⟨listCodeBottom, by simp [compileListCodePair, compileListCode, bottomCode]⟩
  | @comp f g _ _ ihf ihg =>
    obtain ⟨F, hF⟩ := ihf
    obtain ⟨G, hG⟩ := ihg
    exact ⟨.comp F G, by simp [compileListCodePair, hF, hG]⟩
  | @pair f g _ _ ihf ihg =>
    by_cases hi : Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id
    · exact ⟨.head, by simp [compileListCodePair, hi]⟩
    · obtain ⟨F, hF⟩ := ihf
      obtain ⟨G, hG⟩ := ihg
      exact ⟨.comp listCodeNatPair (listCodeTuple F G), by simp [compileListCodePair, hi, hF, hG]⟩

#print axioms compileListCodePair_sound
#print axioms compileListCodePair_complete
end LambdaTuring
