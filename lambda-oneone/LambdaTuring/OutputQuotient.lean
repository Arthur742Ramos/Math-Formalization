/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputFinish
public meta import LambdaTuring.OutputFinish

@[expose] public section

namespace LambdaTuring.Machine

/- A representative ending in one cannot be shortened by removing blank
suffixes. Every equivalent representative is that list plus blanks. -/
theorem listBlank_one_end (pre ys : List Symbol)
    (h : Turing.ListBlank.mk (pre ++ [.one]) = Turing.ListBlank.mk ys) :
    ∃ z, ys = (pre ++ [.one]) ++ List.replicate z .blank := by
  have hr : Turing.BlankRel (pre ++ [.one]) ys := Quotient.exact h
  cases hr with
  | inl h =>
    rcases h with ⟨z, hz⟩
    exact ⟨z, hz⟩
  | inr h =>
    rcases h with ⟨z, hz⟩
    cases z with
    | zero =>
      refine ⟨0, ?_⟩
      simpa using hz.symm
    | succ z =>
      have hl := congrArg List.getLast? hz
      simp [List.getLast?_append, List.getLast?_replicate] at hl

theorem listBlank_empty_blanksOnly (xs : List Symbol)
    (h : Turing.ListBlank.mk xs = (∅ : Turing.ListBlank Symbol)) : blanksOnly xs = true := by
  have hr : Turing.BlankRel ([] : List Symbol) xs := Quotient.exact h.symm
  cases hr with
  | inl h =>
    rcases h with ⟨z, hz⟩
    simpa using hz ▸ blanksOnly_replicate z
  | inr h =>
    rcases h with ⟨z, hz⟩
    have hx : xs = [] := (List.append_eq_nil_iff.mp hz.symm).1
    subst xs
    rfl

theorem outputFinish_from_quotient (t : Tape) (gap n : Nat)
    (ht : mathTape t = Turing.Tape.mk'
      (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one)) ∅) :
    ∃ c, Reaches outputFinish ⟨⟨0, by decide⟩, t⟩ c ∧ Halted outputFinish c ∧
      decode (c.tape.head :: c.tape.right) = some n := by
  have hh : t.head = .blank := by
    have h := congrArg Turing.Tape.head ht
    change t.head = Symbol.blank at h
    exact h
  have hl : Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one) =
      Turing.ListBlank.mk t.left := by
    have h := congrArg Turing.Tape.left ht
    simpa [mathTape, Turing.Tape.mk'] using h.symm
  have hr : Turing.ListBlank.mk t.right = (∅ : Turing.ListBlank Symbol) := by
    have h := congrArg Turing.Tape.right ht
    change Turing.ListBlank.mk t.right = (∅ : Turing.ListBlank Symbol) at h
    exact h
  have hcanon : List.replicate gap Symbol.blank ++ .mark :: List.replicate (n+1) .one =
      (List.replicate gap .blank ++ .mark :: List.replicate n .one) ++ [.one] := by
    rw [List.replicate_succ']
    simp [List.append_assoc]
  rw [hcanon] at hl
  obtain ⟨z, hz⟩ := listBlank_one_end _ _ hl
  rw [← hcanon] at hz
  have hright := listBlank_empty_blanksOnly t.right hr
  obtain ⟨c, hc, hhalt, hout⟩ :=
    outputFinish_observes_with_blank_extensions gap n (List.replicate z .blank) t.right
      (blanksOnly_replicate z) hright
  refine ⟨c, ?_, hhalt, hout⟩
  cases t with
  | mk left head right =>
    simp only at hh hl hr hz hright
    subst head
    subst left
    simpa [finishCfg, List.append_assoc] using hc

def clearThenFinish := sequenceProgram clearSweepProgram outputFinish

/- The scratch result must already have been constructed to the left of the
encoded tail. The cleanup uses all tracks to identify the first wholly blank
source cell, then the finishing machine exposes that scratch to the public
head/right decoder. -/
set_option backward.isDefEq.respectTransparency false in
theorem clearThenFinish_observes (t : Tape) (n offset gap : Nat)
    (S : ∀ _ : StackIndex, List StackSymbol)
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse)
    (hoff : 0 < offset)
    (ht : mathTape t = Turing.Tape.mk'
      (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one))
      (encodeBlankSide ((Turing.ListBlank.tail^[offset]) (Turing.TM2to1.addBottom L)))) :
    ∃ c, Reaches clearThenFinish (sequenceLeftConfig ⟨⟨0, by omega⟩, t⟩) c ∧
      Halted clearThenFinish c ∧ decode (c.tape.head :: c.tape.right) = some n := by
  obtain ⟨k, d, hrun, hhalt, hd⟩ :=
    clearOutputTailProgram_clean t
      (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one))
      S L hproj offset hoff ht
  have hcanonical : mathTape d.tape = Turing.Tape.mk'
      (Turing.ListBlank.mk (List.replicate (13 * (k+1) + gap) .blank ++
        .mark :: List.replicate (n+1) .one)) ∅ := by
    rw [hd, Turing.ListBlank.append_mk]
    congr 2
    rw [← List.append_assoc, ← List.replicate_add]
  obtain ⟨c, hc, hch, hout⟩ :=
    outputFinish_from_quotient d.tape (13 * (k+1) + gap) n hcanonical
  have hseq := sequence_complete clearSweepProgram outputFinish ⟨⟨0, by omega⟩, t⟩ d c
    hrun hhalt hc hch
  exact ⟨sequenceRightConfig c, hseq.1, hseq.2, hout⟩

#print axioms listBlank_one_end
#print axioms outputFinish_from_quotient
#print axioms clearThenFinish_observes
end LambdaTuring.Machine
