/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputRepeat
public meta import LambdaTuring.OutputRepeat

@[expose] public section

namespace LambdaTuring.Machine

/- Reserve a marker immediately left of the current head and a blank one
cell farther left. Both cells are scratch: their former values are irrelevant
to output, while the unprocessed right tape and head are preserved. -/
def outputScratchSetup : Program 6 :=
  ⟨[some (⟨1, by decide⟩, .left), some (⟨1, by decide⟩, .left), some (⟨1, by decide⟩, .left),
    some (⟨2, by decide⟩, .write .mark), some (⟨2, by decide⟩, .write .mark), some (⟨2, by decide⟩, .write .mark),
    some (⟨3, by decide⟩, .left), some (⟨3, by decide⟩, .left), some (⟨3, by decide⟩, .left),
    some (⟨4, by decide⟩, .write .blank), some (⟨4, by decide⟩, .write .blank), some (⟨4, by decide⟩, .write .blank),
    some (⟨5, by decide⟩, .right), some (⟨5, by decide⟩, .right), some (⟨5, by decide⟩, .right),
    some (⟨6, by decide⟩, .right), some (⟨6, by decide⟩, .right), some (⟨6, by decide⟩, .right)]⟩

def scratchSetupTape (t : Tape) : Tape :=
  moveRight (moveRight { moveLeft { moveLeft t with head := .mark } with head := .blank })

theorem scratchSetup_reaches (t : Tape) :
    Reaches outputScratchSetup ⟨⟨0, by decide⟩, t⟩ ⟨⟨6, by decide⟩, scratchSetupTape t⟩ := by
  let t₁ := moveLeft t
  let t₂ := { t₁ with head := Symbol.mark }
  let t₃ := moveLeft t₂
  let t₄ := { t₃ with head := Symbol.blank }
  let t₅ := moveRight t₄
  have s₀ : step outputScratchSetup ⟨⟨0, by decide⟩, t⟩ = some ⟨⟨1, by decide⟩, t₁⟩ := by
    cases h : t.head <;> simp [outputScratchSetup, step, instruction, symbolIndex, perform, t₁, h]
  have s₁ : step outputScratchSetup ⟨⟨1, by decide⟩, t₁⟩ = some ⟨⟨2, by decide⟩, t₂⟩ := by
    cases h : t₁.head <;> simp [outputScratchSetup, step, instruction, symbolIndex, perform, t₂, h]
  have s₂ : step outputScratchSetup ⟨⟨2, by decide⟩, t₂⟩ = some ⟨⟨3, by decide⟩, t₃⟩ := by
    simp [outputScratchSetup, step, instruction, symbolIndex, perform, t₃, t₂]
  have s₃ : step outputScratchSetup ⟨⟨3, by decide⟩, t₃⟩ = some ⟨⟨4, by decide⟩, t₄⟩ := by
    cases h : t₃.head <;> simp [outputScratchSetup, step, instruction, symbolIndex, perform, t₄, h]
  have s₄ : step outputScratchSetup ⟨⟨4, by decide⟩, t₄⟩ = some ⟨⟨5, by decide⟩, t₅⟩ := by
    simp [outputScratchSetup, step, instruction, symbolIndex, perform, t₅, t₄]
  have s₅ : step outputScratchSetup ⟨⟨5, by decide⟩, t₅⟩ =
      some ⟨⟨6, by decide⟩, scratchSetupTape t⟩ := by
    change step outputScratchSetup ⟨⟨5, by decide⟩, t₅⟩ = some ⟨⟨6, by decide⟩, moveRight t₅⟩
    cases h : t₅.head <;> simp [outputScratchSetup, step, instruction, symbolIndex, perform, h]
  exact .step s₀ (.step s₁ (.step s₂ (.step s₃ (.step s₄ (.step s₅ (.refl _))))))

theorem scratchSetup_halts (t : Tape) :
    Halted outputScratchSetup ⟨⟨6, by decide⟩, scratchSetupTape t⟩ := by
  cases h : (scratchSetupTape t).head <;>
    simp [Halted, outputScratchSetup, step, instruction, symbolIndex, h]

theorem scratchSetup_mathTape (t : Tape) :
    mathTape (scratchSetupTape t) =
      Turing.Tape.mk' (safeScratch 0 0 ((mathTape t).left.tail.tail)) (mathTape t).right₀ := by
  cases t with
  | mk left head right =>
    cases left with
    | nil =>
      simp [scratchSetupTape, mathTape, moveLeft, moveRight, safeScratch,
        Turing.Tape.mk', Turing.Tape.right₀]
    | cons a rest =>
      cases rest with
      | nil =>
        simp [scratchSetupTape, mathTape, moveLeft, moveRight, safeScratch,
          Turing.Tape.mk', Turing.Tape.right₀]
      | cons b rest =>
        simp [scratchSetupTape, mathTape, moveLeft, moveRight, safeScratch,
          Turing.Tape.mk', Turing.Tape.right₀]

def outputInitialize := sequenceProgram outputScratchSetup clearWaypoint

/- Clear the initial header block after reserving scratch. The caller is
responsible for the source-level fact that this block is the header. -/
set_option backward.isDefEq.respectTransparency false in
theorem outputInitialize_runs (t : Tape) (R : Turing.ListBlank SimAlphabet)
    (ht : (mathTape t).right₀ = encodeBlankSide R) :
    ∃ d, Reaches outputInitialize ⟨⟨0, by omega⟩, t⟩ d ∧ Halted outputInitialize d ∧
      mathTape d.tape = Turing.Tape.mk'
        (safeScratch 13 0 ((mathTape t).left.tail.tail)) (encodeBlankSide R.tail) := by
  let mid : Config 6 := ⟨⟨6, by decide⟩, scratchSetupTape t⟩
  let xs := List.replicate 13 Symbol.blank
  let out := writerConfig xs xs.length (by omega) (writeRun xs mid.tape)
  have hrun : Reaches (fixedWriter xs) ⟨⟨0, by omega⟩, mid.tape⟩ out := by
    simpa [xs, out, writerConfig] using fixedWriter_run xs mid.tape
  have hs := sequence_complete outputScratchSetup clearWaypoint ⟨⟨0, by decide⟩, t⟩ mid out
    (scratchSetup_reaches t) (scratchSetup_halts t) hrun (fixedWriter_halts xs _)
  refine ⟨sequenceRightConfig out, ?_, hs.2, ?_⟩
  · simpa [outputInitialize, sequenceLeftConfig, sequenceLeftState] using hs.1
  · change mathTape (writeRun xs (scratchSetupTape t)) = _
    rw [mathTape_writeRun, scratchSetup_mathTape, ht]
    have hR : encodeBlankSide R =
        Turing.ListBlank.append (encodeSimSymbol R.head) (encodeBlankSide R.tail) := by
      conv_lhs => rw [← Turing.ListBlank.cons_head_tail R]
      exact encodeBlankSide_cons R.head R.tail
    rw [hR]
    have hlen : xs.length = (encodeSimSymbol R.head).length := by
      simp [xs, encodeSimSymbol, encodeSymbolBlock_length]
    rw [writeBlock_list xs (encodeSimSymbol R.head)
      (safeScratch 0 0 ((mathTape t).left.tail.tail)) (encodeBlankSide R.tail) hlen]
    simp only [xs, List.reverse_replicate]
    congr 1

def unaryOutputConverter := sequenceProgram outputInitialize outputValueLoop

/- Starting from the reached encoded simulator output, initialize scratch,
remove the header, read each bit-one before erasing, then clean and finish.
The input left tape can contain arbitrary data. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem unaryOutputConverter_observes (t : Tape) (m : Nat)
    (S : ∀ _ : StackIndex, List StackSymbol)
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse)
    (hshape : L.map (Turing.proj Turing.PartrecToTM2.K'.main) =
      Turing.ListBlank.mk (some Turing.PartrecToTM2.Γ'.cons ::
        List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1)))
    (ht : (mathTape t).right₀ = encodeBlankSide (Turing.TM2to1.addBottom L)) :
    ∃ d, Reaches unaryOutputConverter ⟨⟨0, by omega⟩, t⟩ d ∧ Halted unaryOutputConverter d ∧
      decode (d.tape.head :: d.tape.right) = some m := by
  obtain ⟨mid, hrun, hhalt, hmid⟩ := outputInitialize_runs t (Turing.TM2to1.addBottom L) ht
  have hmid' : mathTape mid.tape = Turing.Tape.mk'
      (safeScratch 13 0 ((mathTape t).left.tail.tail))
      (encodeBlankSide ((Turing.ListBlank.tail^[1]) (Turing.TM2to1.addBottom L))) := by
    simpa using hmid
  obtain ⟨out, hrun₂, hhalt₂, hout⟩ :=
    outputValueLoop_observes mid.tape 13 m ((mathTape t).left.tail.tail) S L hproj hshape hmid'
  have hs := sequence_complete outputInitialize outputValueLoop ⟨⟨0, by omega⟩, t⟩ mid out
    hrun hhalt hrun₂ hhalt₂
  refine ⟨sequenceRightConfig out, ?_, hs.2, hout⟩
  simpa [unaryOutputConverter, sequenceLeftConfig, sequenceLeftState] using hs.1

#print axioms scratchSetup_reaches
#print axioms scratchSetup_mathTape
#print axioms outputInitialize_runs
#print axioms unaryOutputConverter_observes
end LambdaTuring.Machine
