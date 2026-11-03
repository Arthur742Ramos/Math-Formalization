/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.BlockListDecoder
public meta import LambdaTuring.BlockListDecoder
public import LambdaTuring.BlockFiniteTM0
public meta import LambdaTuring.BlockFiniteTM0

@[expose] public section

namespace LambdaTuring

/-- Read a block at a fixed offset, using blank extension of the target tape.
Malformed blocks are mapped to the source blank; this decoder is used only
for the reached encoded outputs in the correspondence theorem. -/
def decodedBlockAt (L : Turing.ListBlank Machine.Symbol) (n : Nat) : SimAlphabet :=
  decodeSimAlphabet ((decodeSymbolBlock (List.ofFn fun i : Fin 13 => L.nth (13 * n + i.val))).getD
    blankSimAlphabetData)

theorem decodedBlockAt_beyond (xs : List Machine.Symbol) (n : Nat) (h : xs.length ≤ n) :
    decodedBlockAt (Turing.ListBlank.mk xs) n = default := by
  have hs : (List.ofFn fun i : Fin 13 => (Turing.ListBlank.mk xs).nth (13 * n + i.val)) =
      List.replicate 13 Machine.Symbol.blank := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_ofFn, List.getElem_replicate, Turing.ListBlank.nth_mk]
      apply List.getI_eq_default
      omega
  unfold decodedBlockAt
  rw [hs]
  simp [decodeSymbolBlock, blankSimAlphabetData, decode_encodeSimAlphabet]

/-- A generously bounded finite representative of the decoded tape. -/
def decodedBlockPrefix (xs : List Machine.Symbol) : List SimAlphabet :=
  List.ofFn fun i : Fin xs.length => decodedBlockAt (Turing.ListBlank.mk xs) i.val

theorem decodedBlockPrefix_nth (xs : List Machine.Symbol) (n : Nat) :
    (Turing.ListBlank.mk (decodedBlockPrefix xs)).nth n =
      decodedBlockAt (Turing.ListBlank.mk xs) n := by
  by_cases h : n < xs.length
  · simp [Turing.ListBlank.nth_mk, decodedBlockPrefix, List.getI_eq_getElem, h]
  · have hn : xs.length ≤ n := Nat.le_of_not_gt h
    rw [Turing.ListBlank.nth_mk, List.getI_eq_default]
    · exact (decodedBlockAt_beyond xs n hn).symm
    · simp [decodedBlockPrefix, hn]

def decodeBlockSide (L : Turing.ListBlank Machine.Symbol) : Turing.ListBlank SimAlphabet :=
  L.liftOn (fun xs => Turing.ListBlank.mk (decodedBlockPrefix xs)) (by
    rintro xs _ ⟨n, rfl⟩
    apply Turing.ListBlank.ext
    intro i
    rw [decodedBlockPrefix_nth, decodedBlockPrefix_nth]
    have h : Turing.ListBlank.mk xs = Turing.ListBlank.mk (xs ++ List.replicate n .blank) := by
      apply Quotient.sound'
      exact Or.inl ⟨n, rfl⟩
    change decodedBlockAt (Turing.ListBlank.mk xs) i =
      decodedBlockAt (Turing.ListBlank.mk (xs ++ List.replicate n .blank)) i
    rw [h])

theorem decodeBlockSide_nth (L : Turing.ListBlank Machine.Symbol) (n : Nat) :
    (decodeBlockSide L).nth n = decodedBlockAt L n := by
  induction L using Turing.ListBlank.induction_on with
  | h xs => exact decodedBlockPrefix_nth xs n

theorem decodedBlockAt_zero_encoded (L : Turing.ListBlank SimAlphabet) :
    decodedBlockAt (encodeBlankSide L) 0 = L.head := by
  have hL : encodeBlankSide L =
      Turing.ListBlank.append (encodeSimSymbol L.head) (encodeBlankSide L.tail) := by
    conv_lhs => rw [← Turing.ListBlank.cons_head_tail L]
    exact encodeBlankSide_cons L.head L.tail
  have hblock : (List.ofFn fun i : Fin 13 => (encodeBlankSide L).nth (13 * 0 + i.val)) =
      encodeSimSymbol L.head := by
    apply List.ext_getElem
    · simp [encodeSimSymbol, encodeSymbolBlock_length]
    · intro i hi hj
      simp only [List.getElem_ofFn, Nat.mul_zero, Nat.zero_add, hL]
      exact listBlank_nth_append_left _ _ _ hj
  unfold decodedBlockAt
  rw [hblock]
  simp [encodeSimSymbol, decodeSymbolBlock_encode, decode_encodeSimAlphabet]

theorem blank_tail_iter_nth {Γ : Type} [Inhabited Γ] (L : Turing.ListBlank Γ)
    (n k : Nat) : ((Turing.ListBlank.tail^[n]) L).nth k = L.nth (n + k) := by
  induction n generalizing L with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, ← Turing.ListBlank.nth_succ]
    congr 1
    omega

theorem decodedBlockAt_succ (L : Turing.ListBlank Machine.Symbol) (n : Nat) :
    decodedBlockAt L (n + 1) = decodedBlockAt ((Turing.ListBlank.tail^[13]) L) n := by
  unfold decodedBlockAt
  congr 3
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, blank_tail_iter_nth]
    congr 1
    omega

theorem decodedBlockAt_encoded (L : Turing.ListBlank SimAlphabet) (n : Nat) :
    decodedBlockAt (encodeBlankSide L) n = L.nth n := by
  induction n generalizing L with
  | zero => simpa using decodedBlockAt_zero_encoded L
  | succ n ih =>
    rw [decodedBlockAt_succ, encodeBlankSide_tail, ih, Turing.ListBlank.nth_succ]

theorem decodeBlockSide_encoded (L : Turing.ListBlank SimAlphabet) :
    decodeBlockSide (encodeBlankSide L) = L := by
  apply Turing.ListBlank.ext
  intro n
  rw [decodeBlockSide_nth, decodedBlockAt_encoded]

/-- Numerical observation of an encoded output. Malformed blocks and the
source decoder's own noncanonical inputs are not claimed to be rejected. -/
def blockDecodedNumber (out : Turing.ListBlank Machine.Symbol) : Option Nat :=
  tm0DecodedNumber (decodeBlockSide out)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem blockProgram_decoded_lambda_result (c : Nat.Partrec.Code) (n m : Nat) :
    let C := compileListCodeTotal c
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    (∃ out, out ∈ Turing.TM0.eval (Machine.mathProgram (blockProgram C))
      (encodeSimSymbols (tm0ListInput [n])) ∧ blockDecodedNumber out = some m) ↔
      m ∈ numericalValue (compileLambdaTotal c) n := by
  let C := compileListCodeTotal c
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  constructor
  · rintro ⟨out, hout, hdecode⟩
    have hmap := hout
    rw [blockProgram_encoded_eval] at hmap
    obtain ⟨sourceOut, _, he⟩ := (Part.mem_map_iff _).1 hmap
    subst out
    apply (blockProgram_lambda_result c n m).1
    exact ⟨encodeBlankSide sourceOut, sourceOut, hout, rfl, by
      simpa [blockDecodedNumber, decodeBlockSide_encoded] using hdecode⟩
  · intro hm
    obtain ⟨out, sourceOut, hout, he, hd⟩ := (blockProgram_lambda_result c n m).2 hm
    refine ⟨out, hout, ?_⟩
    simpa [he, blockDecodedNumber, decodeBlockSide_encoded] using hd

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem blockProgram_decoded_lambda_none (c : Nat.Partrec.Code) (n : Nat) :
    let C := compileListCodeTotal c
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    (¬ ∃ m out, out ∈ Turing.TM0.eval (Machine.mathProgram (blockProgram C))
      (encodeSimSymbols (tm0ListInput [n])) ∧ blockDecodedNumber out = some m) ↔
      numericalValue (compileLambdaTotal c) n = Part.none := by
  rw [Part.eq_none_iff]
  constructor
  · intro h m hm
    obtain ⟨out, hout, hd⟩ := (blockProgram_decoded_lambda_result c n m).2 hm
    exact h ⟨m, out, hout, hd⟩
  · rintro h ⟨m, out, hout, hd⟩
    exact h m ((blockProgram_decoded_lambda_result c n m).1 ⟨out, hout, hd⟩)

#print axioms decodeBlockSide_nth
#print axioms decodeBlockSide_encoded
#print axioms blockProgram_decoded_lambda_result
#print axioms blockProgram_decoded_lambda_none
end LambdaTuring
