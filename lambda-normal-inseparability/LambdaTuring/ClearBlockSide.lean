/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ClearBlockMachine
public meta import LambdaTuring.ClearBlockMachine

@[expose] public section

namespace LambdaTuring

abbrev ClearSides := Turing.ListBlank Machine.Symbol × Turing.ListBlank SimAlphabet

def clearSideNext (p : ClearSides) : ClearSides :=
  (Turing.ListBlank.append (List.replicate 13 .blank) p.1, p.2.tail)

def clearSideCfg (p : ClearSides) : Turing.TM1.Cfg Machine.Symbol Unit Bool :=
  ⟨some (), false, Turing.Tape.mk' p.1 (encodeBlankSide p.2)⟩

def clearSideEnd (p : ClearSides) : Turing.TM1.Cfg Machine.Symbol Unit Bool :=
  ⟨none, false, Turing.Tape.mk' (clearSideNext p).1 (encodeBlankSide (clearSideNext p).2)⟩

set_option backward.isDefEq.respectTransparency false in
theorem clearScan_side (L : Turing.ListBlank Machine.Symbol) (R : Turing.ListBlank SimAlphabet) :
    clearScan 13 false (Turing.Tape.mk' L (encodeBlankSide R)) =
      (decide (R.head ≠ default), Turing.Tape.mk'
        (Turing.ListBlank.append (List.replicate 13 .blank) L) (encodeBlankSide R.tail)) := by
  have hR : encodeBlankSide R =
      Turing.ListBlank.append (encodeSimSymbol R.head) (encodeBlankSide R.tail) := by
    conv_lhs => rw [← Turing.ListBlank.cons_head_tail R]
    exact encodeBlankSide_cons R.head R.tail
  have hlen : (encodeSimSymbol R.head).length = 13 := encodeSymbolBlock_length _
  have hs := clearScan_list (encodeSimSymbol R.head) L (encodeBlankSide R.tail) false
  rw [hlen, encodedBlock_any_nonblank] at hs
  rw [← hR] at hs
  simpa only [Bool.false_or] using hs

set_option backward.isDefEq.respectTransparency false in
theorem clearSide_step_nonblank (p : ClearSides) (h : p.2.head ≠ default) :
    Turing.TM1.step clearSweep (clearSideCfg p) = some (clearSideCfg (clearSideNext p)) := by
  simp [Turing.TM1.step, clearSideCfg, clearSideNext, clearSweep, clearCells_stepAux, clearScan_side, h]

set_option backward.isDefEq.respectTransparency false in
theorem clearSide_step_blank (p : ClearSides) (h : p.2.head = default) :
    Turing.TM1.step clearSweep (clearSideCfg p) = some (clearSideEnd p) := by
  simp [Turing.TM1.step, clearSideCfg, clearSideEnd, clearSideNext, clearSweep,
    clearCells_stepAux, clearScan_side, h]

theorem clearSide_end_halted (p : ClearSides) : Turing.TM1.step clearSweep (clearSideEnd p) = none := rfl

set_option backward.isDefEq.respectTransparency false in
theorem clearSide_reaches (L : Turing.ListBlank Machine.Symbol) (R : Turing.ListBlank SimAlphabet) (n : Nat)
    (hprior : ∀ k, k < n → R.nth k ≠ default) (hstop : R.nth n = default) :
    StateTransition.Reaches (Turing.TM1.step clearSweep) (clearSideCfg (L, R))
      (clearSideEnd ((clearSideNext^[n]) (L, R))) := by
  induction n generalizing L R with
  | zero =>
    have hh : R.head = default := by simpa using hstop
    apply Relation.ReflTransGen.head (b := clearSideEnd (L, R))
    · rw [clearSide_step_blank (L, R) hh]; simp
    · simpa using Relation.ReflTransGen.refl
  | succ n ih =>
    have hh : R.head ≠ default := by simpa using hprior 0 (by omega)
    have hp : ∀ k, k < n → R.tail.nth k ≠ default := by
      intro k hk
      rw [← Turing.ListBlank.nth_succ]
      exact hprior (k+1) (by omega)
    have hs : R.tail.nth n = default := by
      rw [← Turing.ListBlank.nth_succ]
      exact hstop
    rw [Function.iterate_succ_apply]
    apply Relation.ReflTransGen.head (b := clearSideCfg (clearSideNext (L, R)))
    · rw [clearSide_step_nonblank (L, R) hh]; simp
    · exact ih (Turing.ListBlank.append (List.replicate 13 .blank) L) R.tail hp hs

theorem clearSideProgram_run (t : Machine.Tape) (L : Turing.ListBlank Machine.Symbol)
    (R : Turing.ListBlank SimAlphabet) (ht : Machine.mathTape t = Turing.Tape.mk' L (encodeBlankSide R))
    (hex : ∃ n, R.nth n = default) :
    ∃ n d, R.nth n = default ∧
      Machine.Reaches clearSweepProgram ⟨⟨0, by omega⟩, t⟩ d ∧
      Machine.Halted clearSweepProgram d ∧
      Machine.mathTape d.tape = (clearSideEnd ((clearSideNext^[n]) (L, R))).Tape := by
  let n := Nat.find hex
  have hstop : R.nth n = default := Nat.find_spec hex
  have hprior : ∀ k, k < n → R.nth k ≠ default := fun k hk => Nat.find_min hex hk
  have hr := clearSide_reaches L R n hprior hstop
  have hh := clearSide_end_halted ((clearSideNext^[n]) (L, R))
  have hrun : StateTransition.Reaches (Turing.TM1.step clearSweep)
      ⟨some (), false, Machine.mathTape t⟩ (clearSideEnd ((clearSideNext^[n]) (L, R))) := by
    rw [ht]
    exact hr
  obtain ⟨d, hd, hdh, hdt⟩ := clearSweepProgram_of_run t _ hrun hh
  exact ⟨n, d, hstop, hd, hdh, hdt⟩

theorem clearSide_iter_right (p : ClearSides) (n : Nat) :
    ((clearSideNext^[n]) p).2 = (Turing.ListBlank.tail^[n]) p.2 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    rfl

theorem clearSide_iter_left (L : Turing.ListBlank Machine.Symbol)
    (R : Turing.ListBlank SimAlphabet) (n : Nat) :
    ((clearSideNext^[n]) (L, R)).1 =
      Turing.ListBlank.append (List.replicate (13 * n) .blank) L := by
  induction n generalizing L R with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    change Turing.ListBlank.append (List.replicate (13 * n) .blank)
      (Turing.ListBlank.append (List.replicate 13 .blank) L) = _
    rw [← Turing.ListBlank.append_assoc, ← List.replicate_add]
    congr 2

theorem clearSideEnd_clean (L : Turing.ListBlank Machine.Symbol) (R : Turing.ListBlank SimAlphabet)
    (n : Nat) (hgap : ∀ j, n ≤ j → R.nth j = default) :
    (clearSideEnd ((clearSideNext^[n]) (L, R))).Tape =
      Turing.Tape.mk' (Turing.ListBlank.append (List.replicate (13 * (n+1)) .blank) L) ∅ := by
  have hempty : ((clearSideNext^[n]) (L, R)).2 = ∅ := by
    apply Turing.ListBlank.ext
    intro k
    rw [clearSide_iter_right, blank_tail_iter_nth]
    change R.nth (n+k) = (Turing.ListBlank.mk ([] : List SimAlphabet)).nth k
    simp only [Turing.ListBlank.nth_mk, List.getI_nil]
    exact hgap (n+k) (by omega)
  have hleft := clearSide_iter_left L R n
  simp only [clearSideEnd, clearSideNext]
  rw [hleft, hempty]
  have htail : (∅ : Turing.ListBlank SimAlphabet).tail = ∅ := rfl
  rw [htail]
  have henc : encodeBlankSide (∅ : Turing.ListBlank SimAlphabet) = ∅ := rfl
  rw [henc, ← Turing.ListBlank.append_assoc, ← List.replicate_add]
  congr 3
  omega

theorem clearSideProgram_clean (t : Machine.Tape) (L : Turing.ListBlank Machine.Symbol)
    (R : Turing.ListBlank SimAlphabet) (ht : Machine.mathTape t = Turing.Tape.mk' L (encodeBlankSide R))
    (hex : ∃ n, R.nth n = default)
    (hgap : ∀ i j, i ≤ j → R.nth i = default → R.nth j = default) :
    ∃ n d, Machine.Reaches clearSweepProgram ⟨⟨0, by omega⟩, t⟩ d ∧
      Machine.Halted clearSweepProgram d ∧
      Machine.mathTape d.tape =
        Turing.Tape.mk' (Turing.ListBlank.append (List.replicate (13 * (n+1)) .blank) L) ∅ := by
  obtain ⟨n, d, hblank, hr, hh, htape⟩ := clearSideProgram_run t L R ht hex
  refine ⟨n, d, hr, hh, ?_⟩
  rw [htape]
  exact clearSideEnd_clean L R n (fun j hj => hgap n j hj hblank)

set_option backward.isDefEq.respectTransparency false in
theorem outputTail_gapless (S : ∀ _ : StackIndex, List StackSymbol)
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse)
    (offset i j : Nat) (hoff : 0 < offset) (hij : i ≤ j)
    (hi : ((Turing.ListBlank.tail^[offset]) (Turing.TM2to1.addBottom L)).nth i = default) :
    ((Turing.ListBlank.tail^[offset]) (Turing.TM2to1.addBottom L)).nth j = default := by
  rw [blank_tail_iter_nth] at hi ⊢
  change (Turing.TM2to1.addBottom L).nth (offset + i) = (false, fun _ => none) at hi
  change (Turing.TM2to1.addBottom L).nth (offset + j) = (false, fun _ => none)
  exact outputBottom_gapless S L hproj (offset+i) (offset+j) (by omega) (by omega) hi

set_option backward.isDefEq.respectTransparency false in
theorem outputTail_eventually_blank (S : ∀ _ : StackIndex, List StackSymbol)
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse)
    (offset : Nat) :
    ∃ n, ((Turing.ListBlank.tail^[offset]) (Turing.TM2to1.addBottom L)).nth n = default := by
  obtain ⟨bound, _, hblank⟩ := encodedOutput_eventually_blank S L hproj
  refine ⟨bound, ?_⟩
  rw [blank_tail_iter_nth]
  have h := hblank (offset + bound) (by omega)
  rw [decodedBlockAt_encoded] at h
  exact h

/- Once all output bits have been read, clear every remaining encoded
track while preserving arbitrary scratch data to the left. -/
set_option backward.isDefEq.respectTransparency false in
theorem clearOutputTailProgram_clean (t : Machine.Tape) (scratch : Turing.ListBlank Machine.Symbol)
    (S : ∀ _ : StackIndex, List StackSymbol) (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse)
    (offset : Nat) (hoff : 0 < offset)
    (ht : Machine.mathTape t = Turing.Tape.mk' scratch
      (encodeBlankSide ((Turing.ListBlank.tail^[offset]) (Turing.TM2to1.addBottom L)))) :
    ∃ n d, Machine.Reaches clearSweepProgram ⟨⟨0, by omega⟩, t⟩ d ∧
      Machine.Halted clearSweepProgram d ∧
      Machine.mathTape d.tape = Turing.Tape.mk'
        (Turing.ListBlank.append (List.replicate (13 * (n+1)) .blank) scratch) ∅ := by
  apply clearSideProgram_clean t scratch _ ht
  · exact outputTail_eventually_blank S L hproj offset
  · intro i j hij hi
    exact outputTail_gapless S L hproj offset i j hoff hij hi

#print axioms clearScan_side
#print axioms clearSide_reaches
#print axioms clearSideProgram_run
#print axioms clearSideProgram_clean
#print axioms clearOutputTailProgram_clean
end LambdaTuring
