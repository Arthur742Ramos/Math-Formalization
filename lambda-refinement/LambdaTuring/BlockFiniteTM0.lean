/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.TM1FiniteTable
public meta import LambdaTuring.TM1FiniteTable

@[expose] public section

namespace LambdaTuring

def symbolList : List Machine.Symbol := [.blank, .one, .mark]

theorem symbolList_complete (s : Machine.Symbol) : s ∈ symbolList := by
  cases s <;> simp [symbolList]

/-- All words of the requested length over the three-symbol alphabet. -/
def symbolWords : Nat → List (List Machine.Symbol)
  | 0 => [[]]
  | n+1 => symbolList.flatMap fun a => (symbolWords n).map (a :: ·)

theorem symbolWords_complete (xs : List Machine.Symbol) : xs ∈ symbolWords xs.length := by
  induction xs with
  | nil => simp [symbolWords]
  | cons a xs ih =>
    simp only [List.length_cons, symbolWords, List.mem_flatMap]
    exact ⟨a, symbolList_complete a, List.mem_map.2 ⟨xs, ih, rfl⟩⟩

def blockStoreOfWord (xs : List Machine.Symbol) : BlockStore :=
  fun i => (xs[i.val]?).getD .blank

def blockStoreList : List BlockStore := (symbolWords 13).map blockStoreOfWord

theorem blockStoreOfWord_ofFn (store : BlockStore) : blockStoreOfWord (List.ofFn store) = store := by
  funext i
  unfold blockStoreOfWord
  rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn]
  rfl

theorem blockStoreList_complete (store : BlockStore) : store ∈ blockStoreList := by
  apply List.mem_map.2
  refine ⟨List.ofFn store, ?_, blockStoreOfWord_ofFn store⟩
  simpa using symbolWords_complete (List.ofFn store)

instance : DecidableEq BlockStore := fun f g =>
  decidable_of_iff' (∀ i, f i = g i) (by simp [funext_iff])

instance (C : Turing.ToPartrec.Code) : DecidableEq (BlockLabel C) := inferInstance

theorem blockLabelList_complete (C : Turing.ToPartrec.Code) (l : BlockLabel C) : l ∈ blockLabelList C := by
  cases l with
  | inl i => simp [blockLabelList]
  | inr p => rcases p with ⟨i, a⟩; simp [blockLabelList, simAlphabetDataList_complete]

abbrev BlockTM0StateCount (C : Turing.ToPartrec.Code) :=
  (tm1RawTail (blockMachine C) (blockLabelList C) blockStoreList).length

def blockTM0 (C : Turing.ToPartrec.Code) :
    Fin (BlockTM0StateCount C + 1) → Machine.Symbol →
      Option (Fin (BlockTM0StateCount C + 1) × Turing.TM0.Stmt Machine.Symbol) := by
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  exact tm1NumberedMachine (blockMachine C) (blockLabelList C) blockStoreList

set_option linter.style.haveILetI false in
theorem blockTM0_eval (C : Turing.ToPartrec.Code) (xs : List Machine.Symbol) :
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    letI : Inhabited (Fin (BlockTM0StateCount C + 1)) := ⟨0⟩
    Turing.TM0.eval (blockTM0 C) xs = Turing.TM1.eval (blockMachine C) xs := by
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  letI : Inhabited (Fin (BlockTM0StateCount C + 1)) := ⟨0⟩
  have h := tm1NumberedMachine_eval (blockMachine C) (blockLabelList C) blockStoreList
    (blockLabelList_complete C) blockStoreList_complete xs
  exact h

/-- Compile the finite-control block machine to the public finite transition
    table type. Its input and output are still block-encoded. -/
def blockProgram (C : Turing.ToPartrec.Code) : Machine.Program (BlockTM0StateCount C) := by
  letI : Inhabited (Fin (BlockTM0StateCount C + 1)) := ⟨0⟩
  exact Machine.tableOfMathlib (blockTM0 C)

set_option linter.style.haveILetI false in
theorem blockProgram_math_eval (C : Turing.ToPartrec.Code) (xs : List Machine.Symbol) :
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    Turing.TM0.eval (Machine.mathProgram (blockProgram C)) xs = Turing.TM1.eval (blockMachine C) xs := by
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  letI : Inhabited (Fin (BlockTM0StateCount C + 1)) := ⟨0⟩
  have h : Machine.mathProgram (blockProgram C) = blockTM0 C := Machine.mathProgram_tableOfMathlib _
  rw [h]
  exact blockTM0_eval C xs

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem blockProgram_encoded_eval (C : Turing.ToPartrec.Code) (xs : List SimAlphabet) :
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    Turing.TM0.eval (Machine.mathProgram (blockProgram C)) (encodeSimSymbols xs) =
      (Turing.TM0.eval (numberedMachine C) xs).map encodeBlankSide := by
  rw [blockProgram_math_eval]
  exact blockMachine_eval C xs

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem blockProgram_lambda_result (c : Nat.Partrec.Code) (n m : Nat) :
    let C := compileListCodeTotal c
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    (∃ out sourceOut,
      out ∈ Turing.TM0.eval (Machine.mathProgram (blockProgram C)) (encodeSimSymbols (tm0ListInput [n])) ∧
      out = encodeBlankSide sourceOut ∧ tm0DecodedNumber sourceOut = some m) ↔
        m ∈ numericalValue (compileLambdaTotal c) n := by
  let C := compileListCodeTotal c
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  change (∃ out sourceOut,
    out ∈ Turing.TM0.eval (Machine.mathProgram (blockProgram C)) (encodeSimSymbols (tm0ListInput [n])) ∧
    out = encodeBlankSide sourceOut ∧ tm0DecodedNumber sourceOut = some m) ↔ _
  rw [blockProgram_math_eval]
  exact blockMachine_lambda_result c n m

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem blockProgram_lambda_none (c : Nat.Partrec.Code) (n : Nat) :
    let C := compileListCodeTotal c
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    (¬ ∃ m out sourceOut,
      out ∈ Turing.TM0.eval (Machine.mathProgram (blockProgram C)) (encodeSimSymbols (tm0ListInput [n])) ∧
      out = encodeBlankSide sourceOut ∧ tm0DecodedNumber sourceOut = some m) ↔
        numericalValue (compileLambdaTotal c) n = Part.none := by
  let C := compileListCodeTotal c
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  change (¬ ∃ m out sourceOut,
    out ∈ Turing.TM0.eval (Machine.mathProgram (blockProgram C)) (encodeSimSymbols (tm0ListInput [n])) ∧
    out = encodeBlankSide sourceOut ∧ tm0DecodedNumber sourceOut = some m) ↔ _
  rw [blockProgram_math_eval]
  exact blockMachine_lambda_none c n

#print axioms blockStoreList_complete
#print axioms blockTM0_eval
#print axioms blockProgram_encoded_eval
#print axioms blockProgram_lambda_result
#print axioms blockProgram_lambda_none
end LambdaTuring
