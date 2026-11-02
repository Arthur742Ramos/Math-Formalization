/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.FiniteTableExtraction
public meta import LambdaTuring.FiniteTableExtraction
public import LambdaTuring.MathlibBridge
public meta import LambdaTuring.MathlibBridge

@[expose] public section

namespace LambdaTuring

def encodeTrack : StackState → List Machine.Symbol
  | none => [.one, .one, .one]
  | some .consₗ => [.one, .one, .mark]
  | some .cons => [.one, .mark, .one]
  | some .bit0 => [.one, .mark, .mark]
  | some .bit1 => [.mark, .one, .one]

def decodeTrack : List Machine.Symbol → Option (StackState × List Machine.Symbol)
  | .one :: .one :: .one :: xs => some (none, xs)
  | .one :: .one :: .mark :: xs => some (some .consₗ, xs)
  | .one :: .mark :: .one :: xs => some (some .cons, xs)
  | .one :: .mark :: .mark :: xs => some (some .bit0, xs)
  | .mark :: .one :: .one :: xs => some (some .bit1, xs)
  | _ => none

theorem encodeTrack_length (s : StackState) : (encodeTrack s).length = 3 := by
  cases s with
  | none => rfl
  | some s => cases s <;> rfl

theorem decodeTrack_encode (s : StackState) (xs : List Machine.Symbol) :
    decodeTrack (encodeTrack s ++ xs) = some (s, xs) := by
  cases s with
  | none => rfl
  | some s => cases s <;> rfl

theorem decodeTrack_encode_nil (s : StackState) : decodeTrack (encodeTrack s) = some (s, []) := by
  simpa using decodeTrack_encode s []

def encodeFlag : Bool → Machine.Symbol
  | false => .one
  | true => .mark

def decodeFlag : Machine.Symbol → Option Bool
  | .one => some false
  | .mark => some true
  | .blank => none

def encodeSymbolBody (a : SimAlphabetData) : List Machine.Symbol :=
  encodeFlag a.bottom :: (encodeTrack a.main ++ encodeTrack a.rev ++ encodeTrack a.aux ++ encodeTrack a.stack)

def decodeSymbolBody : List Machine.Symbol → Option SimAlphabetData
  | [] => none
  | b :: xs => do
    let flag ← decodeFlag b
    let (main, xs) ← decodeTrack xs
    let (rev, xs) ← decodeTrack xs
    let (aux, xs) ← decodeTrack xs
    let (stack, xs) ← decodeTrack xs
    if xs = [] then some ⟨flag, main, rev, aux, stack⟩ else none

theorem encodeSymbolBody_length (a : SimAlphabetData) : (encodeSymbolBody a).length = 13 := by
  simp [encodeSymbolBody, encodeTrack_length]

theorem decodeSymbolBody_encode (a : SimAlphabetData) :
    decodeSymbolBody (encodeSymbolBody a) = some a := by
  rcases a with ⟨b, m, r, u, s⟩
  cases b <;> simp [encodeSymbolBody, decodeSymbolBody, encodeFlag, decodeFlag,
    List.append_assoc, decodeTrack_encode, decodeTrack_encode_nil]

def blankSimAlphabetData : SimAlphabetData := encodeSimAlphabet (default : SimAlphabet)

def encodeSymbolBlock (a : SimAlphabetData) : List Machine.Symbol :=
  if a = blankSimAlphabetData then List.replicate 13 .blank else encodeSymbolBody a

def decodeSymbolBlock (xs : List Machine.Symbol) : Option SimAlphabetData :=
  if xs = List.replicate 13 .blank then some blankSimAlphabetData else decodeSymbolBody xs

theorem encodeSymbolBlock_length (a : SimAlphabetData) : (encodeSymbolBlock a).length = 13 := by
  by_cases h : a = blankSimAlphabetData
  · simp [encodeSymbolBlock, h]
  · simp [encodeSymbolBlock, h, encodeSymbolBody_length]

theorem encodeSymbolBody_not_blank (a : SimAlphabetData) :
    encodeSymbolBody a ≠ List.replicate 13 .blank := by
  rcases a with ⟨b, m, r, u, s⟩
  cases b <;> simp [encodeSymbolBody, encodeFlag]

theorem decodeSymbolBlock_encode (a : SimAlphabetData) :
    decodeSymbolBlock (encodeSymbolBlock a) = some a := by
  by_cases h : a = blankSimAlphabetData
  · subst a
    simp [encodeSymbolBlock, decodeSymbolBlock]
  · simp only [encodeSymbolBlock, h, ite_false, decodeSymbolBlock,
      encodeSymbolBody_not_blank, ite_false]
    exact decodeSymbolBody_encode a

def encodeSimSymbol (a : SimAlphabet) : List Machine.Symbol := encodeSymbolBlock (encodeSimAlphabet a)

theorem encodeSimSymbol_blank :
    encodeSimSymbol (default : SimAlphabet) = List.replicate 13 Machine.Symbol.blank := by
  simp [encodeSimSymbol, encodeSymbolBlock, blankSimAlphabetData]

def encodeSimSymbols (xs : List SimAlphabet) : List Machine.Symbol := xs.flatMap encodeSimSymbol

theorem encodeSimSymbols_append (xs ys : List SimAlphabet) :
    encodeSimSymbols (xs ++ ys) = encodeSimSymbols xs ++ encodeSimSymbols ys := by
  simp [encodeSimSymbols]

theorem encodeSimSymbols_blank (n : Nat) :
    encodeSimSymbols (List.replicate n (default : SimAlphabet)) =
      List.replicate (n * 13) Machine.Symbol.blank := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [encodeSimSymbols, encodeSimSymbol_blank, ← ih, Nat.succ_mul, List.replicate_add]

/-- Encoding respects Mathlib's quotient by trailing blank tape cells. -/
def encodeBlankSide (L : Turing.ListBlank SimAlphabet) : Turing.ListBlank Machine.Symbol :=
  L.liftOn (fun xs => Turing.ListBlank.mk (encodeSimSymbols xs)) (by
    rintro xs _ ⟨n, rfl⟩
    apply Quotient.sound'
    left
    refine ⟨n * 13, ?_⟩
    change encodeSimSymbols (xs ++ List.replicate n (default : SimAlphabet)) =
      encodeSimSymbols xs ++ List.replicate (n * 13) Machine.Symbol.blank
    rw [encodeSimSymbols_append, encodeSimSymbols_blank])

theorem encodeBlankSide_mk (xs : List SimAlphabet) :
    encodeBlankSide (Turing.ListBlank.mk xs) = Turing.ListBlank.mk (encodeSimSymbols xs) := rfl

theorem encodeBlankSide_cons (a : SimAlphabet) (L : Turing.ListBlank SimAlphabet) :
    encodeBlankSide (L.cons a) = Turing.ListBlank.append (encodeSimSymbol a) (encodeBlankSide L) := by
  induction L using Turing.ListBlank.induction_on with
  | h xs => simp [Turing.ListBlank.cons_mk, encodeBlankSide_mk, encodeSimSymbols]

def encodeSimSymbolsReverse (xs : List SimAlphabet) : List Machine.Symbol :=
  xs.flatMap (fun a => (encodeSimSymbol a).reverse)

theorem encodeSimSymbolsReverse_append (xs ys : List SimAlphabet) :
    encodeSimSymbolsReverse (xs ++ ys) = encodeSimSymbolsReverse xs ++ encodeSimSymbolsReverse ys := by
  simp [encodeSimSymbolsReverse]

theorem encodeSimSymbolsReverse_blank (n : Nat) :
    encodeSimSymbolsReverse (List.replicate n (default : SimAlphabet)) =
      List.replicate (n * 13) Machine.Symbol.blank := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [encodeSimSymbolsReverse, encodeSimSymbol_blank, ← ih, Nat.succ_mul, List.replicate_add]

/-- The left half is stored nearest-first, so each encoded block is reversed. -/
def encodeBlankSideReverse (L : Turing.ListBlank SimAlphabet) : Turing.ListBlank Machine.Symbol :=
  L.liftOn (fun xs => Turing.ListBlank.mk (encodeSimSymbolsReverse xs)) (by
    rintro xs _ ⟨n, rfl⟩
    apply Quotient.sound'
    left
    refine ⟨n * 13, ?_⟩
    change encodeSimSymbolsReverse (xs ++ List.replicate n (default : SimAlphabet)) =
      encodeSimSymbolsReverse xs ++ List.replicate (n * 13) Machine.Symbol.blank
    rw [encodeSimSymbolsReverse_append, encodeSimSymbolsReverse_blank])

theorem encodeBlankSideReverse_mk (xs : List SimAlphabet) :
    encodeBlankSideReverse (Turing.ListBlank.mk xs) = Turing.ListBlank.mk (encodeSimSymbolsReverse xs) := rfl

theorem encodeBlankSideReverse_cons (a : SimAlphabet) (L : Turing.ListBlank SimAlphabet) :
    encodeBlankSideReverse (L.cons a) =
      Turing.ListBlank.append (encodeSimSymbol a).reverse (encodeBlankSideReverse L) := by
  induction L using Turing.ListBlank.induction_on with
  | h xs => simp [Turing.ListBlank.cons_mk, encodeBlankSideReverse_mk, encodeSimSymbolsReverse]

theorem tape_move_right_list {α : Type} [Inhabited α] (xs : List α)
    (L R : Turing.ListBlank α) :
    ((Turing.Tape.move Turing.Dir.right)^[xs.length])
      (Turing.Tape.mk' L (Turing.ListBlank.append xs R)) =
      Turing.Tape.mk' (Turing.ListBlank.append xs.reverse L) R := by
  induction xs generalizing L with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.length_cons, Function.iterate_succ_apply, Turing.ListBlank.append,
      Turing.Tape.move_right_mk', Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    rw [ih]
    simp [List.reverse_cons, Turing.ListBlank.append_assoc]

def writeBlock {α : Type} [Inhabited α] : List α → Turing.Tape α → Turing.Tape α
  | [], T => T
  | x :: xs, T => writeBlock xs ((T.write x).move .right)

theorem writeBlock_list {α : Type} [Inhabited α] (xs ys : List α)
    (L R : Turing.ListBlank α) (hlen : xs.length = ys.length) :
    writeBlock xs (Turing.Tape.mk' L (Turing.ListBlank.append ys R)) =
      Turing.Tape.mk' (Turing.ListBlank.append xs.reverse L) R := by
  induction xs generalizing ys L with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [writeBlock, Turing.ListBlank.append, Turing.Tape.write_mk',
        Turing.ListBlank.tail_cons, Turing.Tape.move_right_mk', Turing.ListBlank.head_cons]
      rw [ih ys _ hlen]
      simp [List.reverse_cons, Turing.ListBlank.append_assoc]

def encodeBlockTape (T : Turing.Tape SimAlphabet) : Turing.Tape Machine.Symbol :=
  Turing.Tape.mk' (encodeBlankSideReverse T.left) (encodeBlankSide T.right₀)

theorem encodeBlockTape_left (T : Turing.Tape SimAlphabet) :
    (encodeBlockTape T).left = encodeBlankSideReverse T.left := by simp [encodeBlockTape]

theorem encodeBlockTape_right (T : Turing.Tape SimAlphabet) :
    (encodeBlockTape T).right₀ = encodeBlankSide T.right₀ := by simp [encodeBlockTape]

theorem encodeBlockTape_initial (xs : List SimAlphabet) :
    encodeBlockTape (Turing.Tape.mk₁ xs) = Turing.Tape.mk₁ (encodeSimSymbols xs) := by
  simp [encodeBlockTape, Turing.Tape.mk₁, Turing.Tape.mk₂,
    encodeBlankSide_mk, encodeBlankSideReverse_mk, encodeSimSymbolsReverse]

theorem encodeBlockTape_move_right (T : Turing.Tape SimAlphabet) :
    encodeBlockTape (T.move .right) = ((Turing.Tape.move Turing.Dir.right)^[13]) (encodeBlockTape T) := by
  obtain ⟨L, R, rfl⟩ := Turing.Tape.exists_mk' T
  have hR : encodeBlankSide R =
      Turing.ListBlank.append (encodeSimSymbol R.head) (encodeBlankSide R.tail) := by
    conv_lhs => rw [← Turing.ListBlank.cons_head_tail R]
    exact encodeBlankSide_cons R.head R.tail
  have hm := tape_move_right_list (encodeSimSymbol R.head) (encodeBlankSideReverse L) (encodeBlankSide R.tail)
  have hlen : (encodeSimSymbol R.head).length = 13 := encodeSymbolBlock_length _
  rw [hlen] at hm
  simp only [encodeBlockTape, Turing.Tape.move_right_mk', Turing.Tape.mk'_left,
    Turing.Tape.mk'_right₀, encodeBlankSideReverse_cons] at ⊢
  rw [hR]
  exact hm.symm

theorem encodeBlockTape_move_left (T : Turing.Tape SimAlphabet) :
    encodeBlockTape (T.move .left) = ((Turing.Tape.move Turing.Dir.left)^[13]) (encodeBlockTape T) := by
  have hinv : Function.LeftInverse (Turing.Tape.move Turing.Dir.left : Turing.Tape Machine.Symbol → _)
      (Turing.Tape.move Turing.Dir.right) := Turing.Tape.move_right_left
  have h := congrArg ((Turing.Tape.move Turing.Dir.left)^[13])
    (encodeBlockTape_move_right (T.move .left))
  rw [Turing.Tape.move_left_right, (hinv.iterate 13) _] at h
  exact h.symm

theorem encodeBlockTape_write (T : Turing.Tape SimAlphabet) (a : SimAlphabet) :
    encodeBlockTape (T.write a) =
      ((Turing.Tape.move Turing.Dir.left)^[13]) (writeBlock (encodeSimSymbol a) (encodeBlockTape T)) := by
  obtain ⟨L, R, rfl⟩ := Turing.Tape.exists_mk' T
  have hR : encodeBlankSide R =
      Turing.ListBlank.append (encodeSimSymbol R.head) (encodeBlankSide R.tail) := by
    conv_lhs => rw [← Turing.ListBlank.cons_head_tail R]
    exact encodeBlankSide_cons R.head R.tail
  have hlen : (encodeSimSymbol a).length = (encodeSimSymbol R.head).length := by
    simp [encodeSimSymbol, encodeSymbolBlock_length]
  have hw := writeBlock_list (encodeSimSymbol a) (encodeSimSymbol R.head)
    (encodeBlankSideReverse L) (encodeBlankSide R.tail) hlen
  have hm := tape_move_right_list (encodeSimSymbol a) (encodeBlankSideReverse L) (encodeBlankSide R.tail)
  have hlen' : (encodeSimSymbol a).length = 13 := encodeSymbolBlock_length _
  rw [hlen'] at hm
  have htarget : writeBlock (encodeSimSymbol a) (encodeBlockTape (Turing.Tape.mk' L R)) =
      ((Turing.Tape.move Turing.Dir.right)^[13])
        (encodeBlockTape ((Turing.Tape.mk' L R).write a)) := by
    simp only [encodeBlockTape, Turing.Tape.write_mk', Turing.Tape.mk'_left,
      Turing.Tape.mk'_right₀, encodeBlankSide_cons]
    rw [hR]
    exact hw.trans hm.symm
  have hinv : Function.LeftInverse (Turing.Tape.move Turing.Dir.left : Turing.Tape Machine.Symbol → _)
      (Turing.Tape.move Turing.Dir.right) := Turing.Tape.move_right_left
  have h := congrArg ((Turing.Tape.move Turing.Dir.left)^[13]) htarget
  rw [(hinv.iterate 13) _] at h
  exact h.symm

theorem listBlank_nth_append_left {α : Type} [Inhabited α] (xs : List α)
    (R : Turing.ListBlank α) (i : Nat) (hi : i < xs.length) :
    (Turing.ListBlank.append xs R).nth i = xs[i] := by
  induction R using Turing.ListBlank.induction_on with
  | h ys =>
    rw [Turing.ListBlank.append_mk, Turing.ListBlank.nth_mk]
    rw [List.getI_eq_getElem _ (by simp; omega), List.getElem_append_left hi]

/-- The finite sequence observed while moving across one encoded block. -/
def readBlock (T : Turing.Tape Machine.Symbol) : List Machine.Symbol :=
  List.ofFn fun i : Fin 13 => ((Turing.Tape.move Turing.Dir.right)^[i.val] T).head

theorem readBlock_encodeBlockTape (T : Turing.Tape SimAlphabet) :
    readBlock (encodeBlockTape T) = encodeSimSymbol T.head := by
  have hlen : (encodeSimSymbol T.head).length = 13 := encodeSymbolBlock_length _
  have hR : (encodeBlockTape T).right₀ =
      Turing.ListBlank.append (encodeSimSymbol T.head) (encodeBlankSide T.right) := by
    rw [encodeBlockTape_right, Turing.Tape.right₀, encodeBlankSide_cons]
  apply List.ext_getElem
  · simp [readBlock, hlen]
  · intro i hi₁ hi₂
    simp only [readBlock, List.getElem_ofFn, Turing.Tape.move_right_n_head,
      ← Turing.Tape.right₀_nth, hR]
    exact listBlank_nth_append_left _ _ _ hi₂

theorem decode_readBlock_encodeBlockTape (T : Turing.Tape SimAlphabet) :
    decodeSymbolBlock (readBlock (encodeBlockTape T)) = some (encodeSimAlphabet T.head) := by
  rw [readBlock_encodeBlockTape]
  exact decodeSymbolBlock_encode _

theorem listBlank_tail_iter_append {α : Type} [Inhabited α] (xs : List α) (L : Turing.ListBlank α) :
    (Turing.ListBlank.tail^[xs.length]) (Turing.ListBlank.append xs L) = L := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [Function.iterate_succ_apply, ih]

theorem encodeBlankSide_tail (L : Turing.ListBlank SimAlphabet) :
    (Turing.ListBlank.tail^[13]) (encodeBlankSide L) = encodeBlankSide L.tail := by
  have hL : encodeBlankSide L =
      Turing.ListBlank.append (encodeSimSymbol L.head) (encodeBlankSide L.tail) := by
    conv_lhs => rw [← Turing.ListBlank.cons_head_tail L]
    exact encodeBlankSide_cons L.head L.tail
  rw [hL]
  have h := listBlank_tail_iter_append (encodeSimSymbol L.head) (encodeBlankSide L.tail)
  have hlen : (encodeSimSymbol L.head).length = 13 := encodeSymbolBlock_length _
  rwa [hlen] at h

theorem encodeBlankSide_head_eq {L₁ L₂ : Turing.ListBlank SimAlphabet}
    (h : encodeBlankSide L₁ = encodeBlankSide L₂) : L₁.head = L₂.head := by
  let T₁ : Turing.Tape SimAlphabet := Turing.Tape.mk' ∅ L₁
  let T₂ : Turing.Tape SimAlphabet := Turing.Tape.mk' ∅ L₂
  have hT : encodeBlockTape T₁ = encodeBlockTape T₂ := by
    simp only [T₁, T₂, encodeBlockTape, Turing.Tape.mk'_left, Turing.Tape.mk'_right₀]
    rw [h]
  have hread := decode_readBlock_encodeBlockTape T₁
  rw [hT, decode_readBlock_encodeBlockTape] at hread
  have hhead : encodeSimAlphabet T₁.head = encodeSimAlphabet T₂.head := Option.some.inj hread.symm
  have hdecoded := congrArg decodeSimAlphabet hhead
  simpa [T₁, T₂, decode_encodeSimAlphabet] using hdecoded

theorem encodeBlankSide_injective : Function.Injective encodeBlankSide := by
  intro L₁ L₂ h
  apply Turing.ListBlank.ext
  intro n
  induction n generalizing L₁ L₂ with
  | zero => simpa using encodeBlankSide_head_eq h
  | succ n ih =>
    rw [Turing.ListBlank.nth_succ, Turing.ListBlank.nth_succ]
    apply ih
    rw [← encodeBlankSide_tail L₁, ← encodeBlankSide_tail L₂, h]

#print axioms decodeSymbolBlock_encode
#print axioms encodeBlankSide_mk
#print axioms encodeBlockTape_initial
#print axioms encodeBlockTape_move_right
#print axioms encodeBlockTape_move_left
#print axioms encodeBlockTape_write
#print axioms decode_readBlock_encodeBlockTape
#print axioms encodeBlankSide_injective
end LambdaTuring
