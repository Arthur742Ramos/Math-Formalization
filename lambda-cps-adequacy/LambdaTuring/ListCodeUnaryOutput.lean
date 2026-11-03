/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.UnarySequenceBridge
public meta import LambdaTuring.UnarySequenceBridge

@[expose] public section

namespace LambdaTuring

/-- Encode an output number as a binary word consisting only of ones. -/
def listCodeOutputOnes : Turing.ToPartrec.Code := .comp .pred listCodePow2Next

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some in
set_option backward.isDefEq.respectTransparency false in
theorem listCodeOutputOnes_eval (n : Nat) :
    listCodeOutputOnes.eval [n] = Part.some [onesNumber n] := by
  have hs : (listCodeSuccOf .head).eval [n] = Part.some [n+1] := by
    apply listCodeSuccOf_eval
    simp [Turing.ToPartrec.Code.head_eval]
  have hp : listCodePow2Next.eval [n] = Part.some [2^(n+1)] := by
    simp [listCodePow2Next, Turing.ToPartrec.Code.comp_eval, hs, Bind.bind, Part.bind_some, listCodePow2_eval]
  simp [listCodeOutputOnes, Turing.ToPartrec.Code.comp_eval, Turing.ToPartrec.Code.pred_eval,
    hp, Bind.bind, Part.bind_some]
  rw [← onesNumber_add_one]
  omega

/-- Recovery of the input and all-ones encoding of every defined result. -/
def compileUnaryOutputCode (c : Nat.Partrec.Code) : Turing.ToPartrec.Code :=
  .comp listCodeOutputOnes (compileRecoveredListCode c)

set_option backward.isDefEq.respectTransparency false in
theorem compileUnaryOutputCode_eval (c : Nat.Partrec.Code) (n : Nat) :
    (compileUnaryOutputCode c).eval [onesNumber n] =
      (Nat.Partrec.Code.eval c n).map (fun r => [onesNumber r]) := by
  change ((compileRecoveredListCode c).eval [onesNumber n]).bind listCodeOutputOnes.eval = _
  rw [compileRecoveredListCode_eval]
  apply Part.ext
  intro out
  simp only [Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨input, ⟨v, hv, rfl⟩, hout⟩
    rw [listCodeOutputOnes_eval] at hout
    exact ⟨v, hv, (Part.mem_some_iff.1 hout).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨[v], ⟨v, hv, rfl⟩, by simp [listCodeOutputOnes_eval]⟩

theorem onesNumber_injective : Function.Injective onesNumber := by
  intro a b h
  have hp : 2^(a+1) = 2^(b+1) := by rw [← onesNumber_add_one, ← onesNumber_add_one, h]
  have he : a+1 = b+1 := Nat.pow_right_injective (by decide : 2 ≤ 2) hp
  omega

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem unaryOutput_mainTrack (c : Nat.Partrec.Code) (n m : Nat)
    (hm : m ∈ numericalValue (compileLambdaTotal c) n) :
    let C := compileUnaryOutputCode c
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    ∃ (out : Turing.ListBlank SimAlphabet) (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol)),
      out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [onesNumber n]) ∧
      Turing.TM2to1.addBottom L = out ∧
      L.map (Turing.proj Turing.PartrecToTM2.K'.main) =
        Turing.ListBlank.mk (some Turing.PartrecToTM2.Γ'.cons ::
          List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1)) := by
  let C := compileUnaryOutputCode c
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  rw [(compileLambdaTotal_sound c).2 n] at hm
  have hc : [onesNumber m] ∈ C.eval [onesNumber n] := by
    rw [compileUnaryOutputCode_eval]
    exact (Part.mem_map_iff _).2 ⟨m, hm, rfl⟩
  have hd : (Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [onesNumber n])).Dom :=
    (tm0List_domain C [onesNumber n]).2 (Part.dom_iff_mem.2 ⟨[onesNumber m], hc⟩)
  obtain ⟨out, hout⟩ := Part.dom_iff_mem.1 hd
  obtain ⟨S, L, heq, hproj, hmain⟩ :=
    tm0List_output_relation C [onesNumber n] [onesNumber m] out hout hc
  refine ⟨out, L, hout, heq, ?_⟩
  have hp := hproj Turing.PartrecToTM2.K'.main
  rw [hmain, trList_ones] at hp
  simpa [List.map_append, List.map_replicate, List.reverse_append] using hp

set_option backward.isDefEq.respectTransparency false in
theorem encodedOutputMain_read
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol)) (m i : Nat)
    (h : L.map (Turing.proj Turing.PartrecToTM2.K'.main) =
      Turing.ListBlank.mk (some Turing.PartrecToTM2.Γ'.cons ::
        List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1))) :
    (decodedBlockAt (encodeBlankSide (Turing.TM2to1.addBottom L)) i).2 Turing.PartrecToTM2.K'.main =
      (some Turing.PartrecToTM2.Γ'.cons ::
        List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1)).getI i := by
  rw [decodedBlockAt_encoded, Turing.TM2to1.addBottom_nth_snd]
  rw [← Turing.proj_map_nth, h, Turing.ListBlank.nth_mk]

#print axioms listCodeOutputOnes_eval
#print axioms compileUnaryOutputCode_eval
#print axioms onesNumber_injective
#print axioms unaryOutput_mainTrack
#print axioms encodedOutputMain_read
end LambdaTuring
