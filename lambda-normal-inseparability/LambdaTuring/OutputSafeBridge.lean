/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputSafeAppend
public meta import LambdaTuring.OutputSafeAppend

@[expose] public section

namespace LambdaTuring.Machine

/- Transport a terminating concrete table run across equality of the
blank-quotiented tapes. Its control state and the quotient result are exact. -/
theorem transportTapeRun {states : Nat} (p : Program states) (q : Fin (states+1))
    (t₁ t₂ : Tape) (heq : mathTape t₁ = mathTape t₂) (d₁ : Config states)
    (hr : Reaches p ⟨q, t₁⟩ d₁) (hh : Halted p d₁) :
    ∃ d₂, Reaches p ⟨q, t₂⟩ d₂ ∧ Halted p d₂ ∧ mathConfig d₂ = mathConfig d₁ := by
  have hinit : mathConfig (⟨q, t₁⟩ : Config states) = mathConfig ⟨q, t₂⟩ := by
    simp [mathConfig, heq]
  obtain ⟨z, hz, hm⟩ := StateTransition.tr_reaches (math_respects p)
    (show mathConfig (⟨q, t₁⟩ : Config states) = mathConfig ⟨q, t₁⟩ from rfl)
    (reaches_stateTransition.1 hr)
  subst z
  rw [hinit] at hm
  obtain ⟨d₂, hd₂, heq₂⟩ := mathReachLift p ⟨q, t₂⟩ (mathConfig d₁) hm
  have hhalt : Turing.TM0.step (mathProgram p) (mathConfig d₁) = none := by
    have h := math_step p d₁
    rw [hh] at h
    exact h.symm
  have hd₂halt : Halted p d₂ := by
    apply mathHaltLift
    rw [heq₂]
    exact hhalt
  exact ⟨d₂, hd₂, hd₂halt, heq₂⟩

def safeScratch (gap n : Nat) (old : Turing.ListBlank Symbol) : Turing.ListBlank Symbol :=
  Turing.ListBlank.append (List.replicate gap .blank ++ .mark :: (List.replicate n .one ++ [.blank])) old

theorem safeOutputAppend_quotient (t : Tape) (gap n : Nat)
    (old R : Turing.ListBlank Symbol)
    (ht : mathTape t = Turing.Tape.mk' (safeScratch gap n old) (R.cons .mark)) :
    ∃ d, Reaches safeOutputAppend ⟨⟨0, by decide⟩, t⟩ d ∧ Halted safeOutputAppend d ∧
      mathTape d.tape = Turing.Tape.mk' (safeScratch gap (n+1) old.tail) (R.cons .mark) := by
  induction old using Turing.ListBlank.induction_on with
  | h old =>
    induction R using Turing.ListBlank.induction_on with
    | h right =>
      let t₀ : Tape := ⟨List.replicate gap .blank ++ .mark ::
        (List.replicate n .one ++ .blank :: old), .mark, right⟩
      let d₀ := safeAppendCfg ⟨5, by decide⟩
        (List.replicate gap .blank ++ .mark :: (List.replicate (n+1) .one ++ .blank :: old.tail))
        .mark right
      have ht₀ : mathTape t₀ =
          Turing.Tape.mk' (safeScratch gap n (Turing.ListBlank.mk old))
            ((Turing.ListBlank.mk right).cons .mark) := by
        simp [t₀, mathTape, safeScratch, Turing.ListBlank.append_mk, Turing.Tape.mk',
          List.append_assoc]
      have heq : mathTape t₀ = mathTape t := ht₀.trans ht.symm
      have hs := safeOutputAppend_runs gap n old right
      obtain ⟨d, hd, hdh, he⟩ := transportTapeRun safeOutputAppend ⟨0, by decide⟩
        t₀ t heq d₀ hs.1 hs.2
      refine ⟨d, hd, hdh, ?_⟩
      have htape := congrArg Turing.TM0.Cfg.Tape he
      change mathTape d.tape = mathTape d₀.tape at htape
      rw [htape]
      simp [d₀, safeAppendCfg, mathTape, safeScratch, Turing.ListBlank.append_mk,
        Turing.Tape.mk', List.append_assoc]

def safeMarkAndAppend := sequenceProgram markOutputBlock safeOutputAppend

set_option backward.isDefEq.respectTransparency false in
theorem safeMarkAndAppend_runs (t : Tape) (gap n : Nat)
    (old : Turing.ListBlank Symbol) (R : Turing.ListBlank SimAlphabet)
    (ht : mathTape t = Turing.Tape.mk' (safeScratch gap n old) (encodeBlankSide R)) :
    ∃ d, Reaches safeMarkAndAppend ⟨⟨0, by omega⟩, t⟩ d ∧ Halted safeMarkAndAppend d ∧
      mathTape d.tape = Turing.Tape.mk' (safeScratch gap (n+1) old.tail)
        (Turing.ListBlank.append waypointBlock (encodeBlankSide R.tail)) := by
  obtain ⟨mid, hrun, hhalt, hmid⟩ := markOutputBlock_runs t (safeScratch gap n old) R ht
  have hrun' : Reaches markOutputBlock ⟨⟨0, by omega⟩, t⟩ mid := by
    simpa [sequenceLeftConfig, sequenceLeftState, writerConfig] using hrun
  let tail := Turing.ListBlank.append (List.replicate 12 Symbol.blank) (encodeBlankSide R.tail)
  have hmid' : mathTape mid.tape =
      Turing.Tape.mk' (safeScratch gap n old) (tail.cons .mark) := by
    simpa [waypointBlock, Turing.ListBlank.append, tail] using hmid
  obtain ⟨out, hrun₂, hhalt₂, hout⟩ := safeOutputAppend_quotient mid.tape gap n old tail hmid'
  have hs := sequence_complete markOutputBlock safeOutputAppend ⟨⟨0, by omega⟩, t⟩ mid out
    hrun' hhalt hrun₂ hhalt₂
  refine ⟨sequenceRightConfig (n := 2 * waypointBlock.length + 13 + 1) (m := 8) out,
    ?_, hs.2, ?_⟩
  · simpa [safeMarkAndAppend, sequenceLeftConfig, sequenceLeftState] using hs.1
  · simpa [sequenceRightConfig, waypointBlock, Turing.ListBlank.append, tail] using hout

def safeMarkAppendNext := sequenceProgram safeMarkAndAppend clearWaypoint

set_option backward.isDefEq.respectTransparency false in
theorem safeMarkAppendNext_runs (t : Tape) (gap n : Nat)
    (old : Turing.ListBlank Symbol) (R : Turing.ListBlank SimAlphabet)
    (ht : mathTape t = Turing.Tape.mk' (safeScratch gap n old) (encodeBlankSide R)) :
    ∃ d, Reaches safeMarkAppendNext ⟨⟨0, by omega⟩, t⟩ d ∧ Halted safeMarkAppendNext d ∧
      mathTape d.tape = Turing.Tape.mk' (safeScratch (13+gap) (n+1) old.tail)
        (encodeBlankSide R.tail) := by
  obtain ⟨mid, hrun, hhalt, hmid⟩ := safeMarkAndAppend_runs t gap n old R ht
  obtain ⟨out, hrun₂, hhalt₂, hout⟩ := clearWaypoint_runs mid.tape
    (safeScratch gap (n+1) old.tail) (encodeBlankSide R.tail) hmid
  have hs := sequence_complete safeMarkAndAppend clearWaypoint ⟨⟨0, by omega⟩, t⟩ mid out
    hrun hhalt hrun₂ hhalt₂
  refine ⟨sequenceRightConfig out, ?_, hs.2, ?_⟩
  · simpa [safeMarkAppendNext, sequenceLeftConfig, sequenceLeftState] using hs.1
  · change mathTape out.tape = _
    rw [hout]
    congr 1
    simp only [safeScratch, ← Turing.ListBlank.append_assoc]
    congr 1
    rw [← List.append_assoc, ← List.replicate_add]

theorem safeOutputFinish_quotient (t : Tape) (gap n : Nat) (old : Turing.ListBlank Symbol)
    (ht : mathTape t = Turing.Tape.mk' (safeScratch gap (n+1) old) ∅) :
    ∃ d, Reaches outputFinish ⟨⟨0, by decide⟩, t⟩ d ∧ Halted outputFinish d ∧
      decode (d.tape.head :: d.tape.right) = some n := by
  induction old using Turing.ListBlank.induction_on with
  | h old =>
    let t₀ : Tape := ⟨List.replicate gap .blank ++ .mark ::
      (List.replicate (n+1) .one ++ .blank :: old), .blank, []⟩
    have ht₀ : mathTape t₀ =
        Turing.Tape.mk' (safeScratch gap (n+1) (Turing.ListBlank.mk old)) ∅ := by
      simp [t₀, mathTape, safeScratch, Turing.ListBlank.append_mk, Turing.Tape.mk',
        List.append_assoc]
      exact ⟨rfl, rfl⟩
    have heq : mathTape t₀ = mathTape t := ht₀.trans ht.symm
    obtain ⟨d₀, hd₀, hd₀h, hdecoded⟩ := safeOutputFinish_observes gap n old [] rfl
    obtain ⟨d, hd, hdh, he⟩ := transportTapeRun outputFinish ⟨0, by decide⟩
      t₀ t heq d₀ hd₀ hd₀h
    refine ⟨d, hd, hdh, ?_⟩
    have htape := congrArg Turing.TM0.Cfg.Tape he
    change mathTape d.tape = mathTape d₀.tape at htape
    rw [← mathTape_output, htape, mathTape_output]
    exact hdecoded

def clearThenSafeFinish := sequenceProgram clearSweepProgram outputFinish

set_option backward.isDefEq.respectTransparency false in
theorem clearThenSafeFinish_observes (t : Tape) (n offset gap : Nat)
    (old : Turing.ListBlank Symbol) (S : ∀ _ : StackIndex, List StackSymbol)
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse)
    (hoff : 0 < offset)
    (ht : mathTape t = Turing.Tape.mk' (safeScratch gap (n+1) old)
      (encodeBlankSide ((Turing.ListBlank.tail^[offset]) (Turing.TM2to1.addBottom L)))) :
    ∃ d, Reaches clearThenSafeFinish ⟨⟨0, by omega⟩, t⟩ d ∧ Halted clearThenSafeFinish d ∧
      decode (d.tape.head :: d.tape.right) = some n := by
  obtain ⟨k, mid, hrun, hhalt, hmid⟩ :=
    clearOutputTailProgram_clean t (safeScratch gap (n+1) old) S L hproj offset hoff ht
  have hmid' : mathTape mid.tape = Turing.Tape.mk'
      (safeScratch (13 * (k+1) + gap) (n+1) old) ∅ := by
    rw [hmid]
    congr 1
    simp only [safeScratch, ← Turing.ListBlank.append_assoc]
    congr 1
    rw [← List.append_assoc, ← List.replicate_add]
  obtain ⟨out, hrun₂, hhalt₂, hout⟩ :=
    safeOutputFinish_quotient mid.tape (13 * (k+1) + gap) n old hmid'
  have hs := sequence_complete clearSweepProgram outputFinish ⟨⟨0, by omega⟩, t⟩ mid out
    hrun hhalt hrun₂ hhalt₂
  refine ⟨sequenceRightConfig out, ?_, hs.2, hout⟩
  simpa [clearThenSafeFinish, sequenceLeftConfig, sequenceLeftState] using hs.1

/- This is still an unconditional append stage. The stored reader value is
exposed so the surrounding loop can choose this stage only for a bit-one. -/
def safeReadAppendNext := sequenceProgram mainReaderProgram safeMarkAppendNext

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem safeReadAppendNext_runs (t : Tape) (gap n : Nat)
    (old : Turing.ListBlank Symbol) (R : Turing.ListBlank SimAlphabet)
    (ht : mathTape t = Turing.Tape.mk' (safeScratch gap n old) (encodeBlankSide R)) :
    ∃ rd out, Reaches mainReaderProgram ⟨⟨0, by omega⟩, t⟩ rd ∧ Halted mainReaderProgram rd ∧
      (let s := (tm1NumberRead mainTrackReader mainReaderLabels mainReaderStores rd.state).2
       decodeMainTriple s.1 s.2.1 s.2.2 = some (encodeSimAlphabet R.head).main) ∧
      Reaches safeReadAppendNext ⟨⟨0, by omega⟩, t⟩ out ∧ Halted safeReadAppendNext out ∧
      mathTape out.tape = Turing.Tape.mk' (safeScratch (13+gap) (n+1) old.tail)
        (encodeBlankSide R.tail) := by
  obtain ⟨rd, hrd, hrdh, hvalue, hrdtape⟩ := mainReader_table_runs t (safeScratch gap n old) R ht
  have hmid : mathTape rd.tape = Turing.Tape.mk' (safeScratch gap n old) (encodeBlankSide R) :=
    hrdtape.trans ht
  obtain ⟨out, hout, houth, houttape⟩ := safeMarkAppendNext_runs rd.tape gap n old R hmid
  have hs := sequence_complete mainReaderProgram safeMarkAppendNext ⟨⟨0, by omega⟩, t⟩ rd out
    hrd hrdh hout houth
  refine ⟨rd, sequenceRightConfig out, hrd, hrdh, hvalue, ?_, hs.2, houttape⟩
  simpa [safeReadAppendNext, sequenceLeftConfig, sequenceLeftState] using hs.1

#print axioms transportTapeRun
#print axioms safeOutputAppend_quotient
#print axioms safeMarkAppendNext_runs
#print axioms safeOutputFinish_quotient
#print axioms clearThenSafeFinish_observes
#print axioms safeReadAppendNext_runs
end LambdaTuring.Machine
