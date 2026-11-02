/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputGapless
public meta import LambdaTuring.OutputGapless

@[expose] public section

namespace LambdaTuring

/-- Clear a fixed number of tape cells while recording whether any was
nonblank. The final boolean determines whether the scan repeats. -/
def clearCells : Nat → Turing.TM1.Stmt Machine.Symbol Unit Bool
  | 0 => .branch (fun _ seen => seen) (.load (fun _ _ => false) (.goto fun _ _ => ())) .halt
  | n + 1 => .load (fun a seen => seen || decide (a ≠ .blank))
      (.write (fun _ _ => .blank) (.move .right (clearCells n)))

def clearScan : Nat → Bool → Turing.Tape Machine.Symbol → Bool × Turing.Tape Machine.Symbol
  | 0, seen, t => (seen, t)
  | n + 1, seen, t => clearScan n (seen || decide (t.head ≠ .blank)) ((t.write .blank).move .right)

set_option backward.isDefEq.respectTransparency false in
theorem clearCells_stepAux (n : Nat) (seen : Bool) (t : Turing.Tape Machine.Symbol) :
    Turing.TM1.stepAux (clearCells n) seen t =
      ⟨if (clearScan n seen t).1 then some () else none, false, (clearScan n seen t).2⟩ := by
  induction n generalizing seen t with
  | zero => cases seen <;> rfl
  | succ n ih =>
    change Turing.TM1.stepAux (clearCells n) (seen || decide (t.head ≠ .blank))
      ((t.write .blank).move .right) = _
    exact ih (seen || decide (t.head ≠ .blank)) ((t.write .blank).move .right)

def clearSweep (_ : Unit) : Turing.TM1.Stmt Machine.Symbol Unit Bool := clearCells 13

theorem clearScan_list (xs : List Machine.Symbol) (L R : Turing.ListBlank Machine.Symbol) (seen : Bool) :
    clearScan xs.length seen (Turing.Tape.mk' L (Turing.ListBlank.append xs R)) =
      (seen || xs.any (fun a => decide (a ≠ .blank)),
        Turing.Tape.mk' (Turing.ListBlank.append (List.replicate xs.length .blank) L) R) := by
  induction xs generalizing L seen with
  | nil => simp [clearScan]
  | cons a xs ih =>
    have happ : Turing.ListBlank.append (List.replicate xs.length .blank)
        (Turing.ListBlank.cons .blank L) =
        Turing.ListBlank.cons .blank (Turing.ListBlank.append (List.replicate xs.length .blank) L) := by
      have hr : List.replicate xs.length Machine.Symbol.blank ++ [.blank] =
          .blank :: List.replicate xs.length .blank := by
        rw [← List.replicate_succ', List.replicate_succ]
      calc
        _ = Turing.ListBlank.append (List.replicate xs.length .blank ++ [.blank]) L := by
          rw [Turing.ListBlank.append_assoc]
          rfl
        _ = _ := by rw [hr]; rfl
    simp only [List.length_cons, clearScan, Turing.ListBlank.append, Turing.Tape.mk'_head,
      Turing.ListBlank.head_cons, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
      Turing.ListBlank.tail_cons]
    rw [ih]
    simp [List.any_cons, List.replicate_succ, Bool.or_assoc, happ]

theorem encodeSimSymbol_eq_blank_iff (a : SimAlphabet) :
    encodeSimSymbol a = List.replicate 13 .blank ↔ a = default := by
  constructor
  · intro h
    rw [← encodeSimSymbol_blank] at h
    have he := congrArg decodeSymbolBlock h
    simp only [encodeSimSymbol, decodeSymbolBlock_encode, Option.some.injEq] at he
    have hd := congrArg decodeSimAlphabet he
    simpa [decode_encodeSimAlphabet] using hd
  · rintro rfl
    exact encodeSimSymbol_blank

theorem encodedBlock_any_nonblank (a : SimAlphabet) :
    (encodeSimSymbol a).any (fun x => decide (x ≠ .blank)) = decide (a ≠ default) := by
  by_cases ha : a = default
  · subst a
    simp [encodeSimSymbol_blank]
  · have hn : (encodeSimSymbol a).any (fun x => decide (x ≠ .blank)) ≠ false := by
      intro hf
      have hall : ∀ x ∈ encodeSimSymbol a, x = .blank := by
        intro x hx
        have h := (List.any_eq_false.1 hf) x hx
        simpa using h
      have hrep := List.eq_replicate_of_mem hall
      have hblank : encodeSimSymbol a = List.replicate 13 .blank := by
        simpa [encodeSimSymbol, encodeSymbolBlock_length] using hrep
      exact ha (encodeSimSymbol_eq_blank_iff a |>.1 hblank)
    cases h : (encodeSimSymbol a).any (fun x => decide (x ≠ .blank)) with
    | false => exact (hn h).elim
    | true => simp [ha]

set_option backward.isDefEq.respectTransparency false in
theorem clearScan_encoded (T : Turing.Tape SimAlphabet) :
    clearScan 13 false (encodeBlockTape T) =
      (decide (T.head ≠ default),
        ((Turing.Tape.move .right)^[13]) (encodeBlockTape (T.write default))) := by
  obtain ⟨L, R, rfl⟩ := Turing.Tape.exists_mk' T
  have hR : encodeBlankSide R =
      Turing.ListBlank.append (encodeSimSymbol R.head) (encodeBlankSide R.tail) := by
    conv_lhs => rw [← Turing.ListBlank.cons_head_tail R]
    exact encodeBlankSide_cons R.head R.tail
  have ht : encodeBlockTape (Turing.Tape.mk' L R) =
      Turing.Tape.mk' (encodeBlankSideReverse L)
        (Turing.ListBlank.append (encodeSimSymbol R.head) (encodeBlankSide R.tail)) := by
    simp only [encodeBlockTape, Turing.Tape.mk'_left, Turing.Tape.mk'_right₀, hR]
  have hlen : (encodeSimSymbol R.head).length = 13 := encodeSymbolBlock_length _
  have hs := clearScan_list (encodeSimSymbol R.head) (encodeBlankSideReverse L) (encodeBlankSide R.tail) false
  rw [hlen] at hs
  have hw := writeBlock_list (List.replicate 13 Machine.Symbol.blank) (encodeSimSymbol R.head)
    (encodeBlankSideReverse L) (encodeBlankSide R.tail) (by simp [hlen])
  simp only [List.reverse_replicate] at hw
  rw [← ht] at hs hw
  rw [← hw, writeBlock_encoded_blank] at hs
  rw [encodedBlock_any_nonblank] at hs
  simpa only [Bool.false_or, Turing.Tape.mk'_head] using hs

def clearNext (T : Turing.Tape SimAlphabet) : Turing.Tape SimAlphabet :=
  (T.write default).move .right

def clearCfg (T : Turing.Tape SimAlphabet) : Turing.TM1.Cfg Machine.Symbol Unit Bool :=
  ⟨some (), false, encodeBlockTape T⟩

def clearEnd (T : Turing.Tape SimAlphabet) : Turing.TM1.Cfg Machine.Symbol Unit Bool :=
  ⟨none, false, ((Turing.Tape.move .right)^[13]) (encodeBlockTape (T.write default))⟩

set_option backward.isDefEq.respectTransparency false in
theorem clearSweep_step_nonblank (T : Turing.Tape SimAlphabet) (h : T.head ≠ default) :
    Turing.TM1.step clearSweep (clearCfg T) = some (clearCfg (clearNext T)) := by
  simp [Turing.TM1.step, clearCfg, clearSweep, clearCells_stepAux, clearScan_encoded,
    h, clearNext, encodeBlockTape_move_right]

set_option backward.isDefEq.respectTransparency false in
theorem clearSweep_step_blank (T : Turing.Tape SimAlphabet) (h : T.head = default) :
    Turing.TM1.step clearSweep (clearCfg T) = some (clearEnd T) := by
  simp [Turing.TM1.step, clearCfg, clearEnd, clearSweep, clearCells_stepAux, clearScan_encoded, h]

theorem clearSweep_end_halted (T : Turing.Tape SimAlphabet) :
    Turing.TM1.step clearSweep (clearEnd T) = none := rfl

theorem clearNext_right₀ (T : Turing.Tape SimAlphabet) : (clearNext T).right₀ = T.right₀.tail := by
  obtain ⟨L, R, rfl⟩ := Turing.Tape.exists_mk' T
  simp [clearNext, Turing.Tape.write_mk', Turing.Tape.move_right_mk']

theorem clearNext_iter_head (T : Turing.Tape SimAlphabet) (n : Nat) :
    ((clearNext^[n]) T).head = T.right₀.nth n := by
  induction n generalizing T with
  | zero => simp [Turing.Tape.right₀]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, clearNext_right₀, ← Turing.ListBlank.nth_succ]

theorem clearNext_iter_right₀_nth (T : Turing.Tape SimAlphabet) (n k : Nat) :
    ((clearNext^[n]) T).right₀.nth k = T.right₀.nth (n + k) := by
  induction n generalizing T with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, clearNext_right₀, ← Turing.ListBlank.nth_succ]
    congr 1
    omega

theorem moveRight_preserves_blank (T : Turing.Tape Machine.Symbol)
    (h : T.right₀ = ∅) : (T.move .right).right₀ = ∅ := by
  obtain ⟨L, R, rfl⟩ := Turing.Tape.exists_mk' T
  simp only [Turing.Tape.mk'_right₀] at h
  simp [Turing.Tape.move_right_mk', h]
  rfl

theorem moveRight_iter_preserves_blank (T : Turing.Tape Machine.Symbol) (n : Nat)
    (h : T.right₀ = ∅) : ((Turing.Tape.move .right)^[n] T).right₀ = ∅ := by
  induction n generalizing T with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (T.move .right) (moveRight_preserves_blank T h)

theorem clearEnd_blank_right (T : Turing.Tape SimAlphabet) (h : T.right₀ = ∅) :
    (clearEnd T).Tape.right₀ = ∅ := by
  have hhead : T.head = default := by
    have hh := congrArg Turing.ListBlank.head h
    have hz : (∅ : Turing.ListBlank SimAlphabet).head = default := rfl
    rw [hz] at hh
    simpa [Turing.Tape.right₀] using hh
  have hwrite : T.write default = T := by
    rw [← hhead]
    exact Turing.Tape.write_self T
  change (((Turing.Tape.move .right)^[13]) (encodeBlockTape (T.write default))).right₀ = ∅
  rw [hwrite]
  apply moveRight_iter_preserves_blank
  rw [encodeBlockTape_right, h]
  rfl

theorem clearSweep_clean_suffix (T : Turing.Tape SimAlphabet) (n : Nat)
    (hgap : ∀ j, n ≤ j → T.right₀.nth j = default) :
    (clearEnd ((clearNext^[n]) T)).Tape.right₀ = ∅ := by
  apply clearEnd_blank_right
  apply Turing.ListBlank.ext
  intro k
  rw [clearNext_iter_right₀_nth]
  change T.right₀.nth (n + k) = (Turing.ListBlank.mk ([] : List SimAlphabet)).nth k
  simp only [Turing.ListBlank.nth_mk, List.getI_nil]
  exact hgap (n + k) (by omega)

set_option backward.isDefEq.respectTransparency false in
theorem clearSweep_reaches (T : Turing.Tape SimAlphabet) (n : Nat)
    (hprior : ∀ k, k < n → T.right₀.nth k ≠ default) (hstop : T.right₀.nth n = default) :
    StateTransition.Reaches (Turing.TM1.step clearSweep) (clearCfg T) (clearEnd ((clearNext^[n]) T)) := by
  induction n generalizing T with
  | zero =>
    have hh : T.head = default := by simpa [Turing.Tape.right₀] using hstop
    apply Relation.ReflTransGen.head (b := clearEnd T)
    · rw [clearSweep_step_blank T hh]; simp
    · simpa using Relation.ReflTransGen.refl
  | succ n ih =>
    have hhead : T.head ≠ default := by simpa [Turing.Tape.right₀] using hprior 0 (by omega)
    have hp : ∀ k, k < n → (clearNext T).right₀.nth k ≠ default := by
      intro k hk
      rw [clearNext_right₀, ← Turing.ListBlank.nth_succ]
      exact hprior (k+1) (by omega)
    have hs : (clearNext T).right₀.nth n = default := by
      rw [clearNext_right₀, ← Turing.ListBlank.nth_succ]
      exact hstop
    rw [Function.iterate_succ_apply]
    apply Relation.ReflTransGen.head (b := clearCfg (clearNext T))
    · rw [clearSweep_step_nonblank T hhead]; simp
    · exact ih (clearNext T) hp hs

theorem clearSweep_terminates (T : Turing.Tape SimAlphabet)
    (hex : ∃ n, T.right₀.nth n = default) :
    ∃ n, StateTransition.Reaches (Turing.TM1.step clearSweep) (clearCfg T)
      (clearEnd ((clearNext^[n]) T)) ∧
        Turing.TM1.step clearSweep (clearEnd ((clearNext^[n]) T)) = none := by
  let n := Nat.find hex
  refine ⟨n, ?_, clearSweep_end_halted _⟩
  exact clearSweep_reaches T n (fun k hk => Nat.find_min hex hk) (Nat.find_spec hex)

/- Cleanup is intended only after all needed main-track information has
been read. It checks every symbol in a block, including auxiliary tracks. -/
set_option backward.isDefEq.respectTransparency false in
theorem clearSweep_terminates_output (S : ∀ _ : StackIndex, List StackSymbol)
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse)
    (T : Turing.Tape SimAlphabet) (ht : T.right₀ = Turing.TM2to1.addBottom L) :
    ∃ n, StateTransition.Reaches (Turing.TM1.step clearSweep) (clearCfg T)
      (clearEnd ((clearNext^[n]) T)) ∧
        Turing.TM1.step clearSweep (clearEnd ((clearNext^[n]) T)) = none := by
  obtain ⟨i, _, hblank⟩ := encodedOutput_eventually_blank S L hproj
  have hs := hblank i (le_refl i)
  rw [decodedBlockAt_encoded] at hs
  apply clearSweep_terminates T
  refine ⟨i, ?_⟩
  rw [ht]
  change (Turing.TM2to1.addBottom L).nth i = (false, fun _ => none)
  exact hs

abbrev clearSweepStateCount := (tm1RawTail clearSweep [()] [false, true]).length

def clearSweepTM0 :
    Fin (clearSweepStateCount + 1) → Machine.Symbol →
      Option (Fin (clearSweepStateCount + 1) × Turing.TM0.Stmt Machine.Symbol) :=
  tm1NumberedMachine clearSweep [()] [false, true]

def clearSweepProgram : Machine.Program clearSweepStateCount :=
  Machine.tableOfMathlib clearSweepTM0

set_option linter.style.haveILetI false in
theorem clearSweepProgram_eval (xs : List Machine.Symbol) :
    Turing.TM0.eval (Machine.mathProgram clearSweepProgram) xs = Turing.TM1.eval clearSweep xs := by
  letI : Inhabited (Fin (clearSweepStateCount + 1)) := ⟨0⟩
  have h : Machine.mathProgram clearSweepProgram = clearSweepTM0 := Machine.mathProgram_tableOfMathlib _
  rw [h]
  apply tm1NumberedMachine_eval clearSweep [()] [false, true]
  · intro l; cases l; simp
  · intro s; cases s <;> simp

#eval clearSweepStateCount
#eval clearSweepProgram.table.length
#print axioms clearCells_stepAux
#print axioms clearScan_list
#print axioms encodedBlock_any_nonblank
#print axioms clearScan_encoded
#print axioms clearSweep_reaches
#print axioms clearSweep_terminates
#print axioms clearSweep_terminates_output
#print axioms clearSweepProgram_eval
end LambdaTuring
