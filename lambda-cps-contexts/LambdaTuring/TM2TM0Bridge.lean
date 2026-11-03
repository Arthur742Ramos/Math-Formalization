/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodeBridge
public meta import LambdaTuring.ListCodeBridge

@[expose] public section

namespace LambdaTuring

abbrev StackIndex := Turing.PartrecToTM2.K'
abbrev StackSymbol := Turing.PartrecToTM2.Γ'
abbrev StackLabel := Turing.PartrecToTM2.Λ'
abbrev StackState := Option StackSymbol
abbrev SimAlphabet := Turing.TM2to1.Γ' StackIndex (fun _ => StackSymbol)
abbrev SimLabel := Turing.TM2to1.Λ' StackIndex (fun _ => StackSymbol) StackLabel StackState

def tm1ListInterpreter : SimLabel → Turing.TM1.Stmt SimAlphabet SimLabel StackState :=
  Turing.TM2to1.tr Turing.PartrecToTM2.tr

abbrev RawTM0State := Option (Turing.TM1.Stmt SimAlphabet SimLabel StackState) × StackState

/-- The concrete TM0 program produced by composing Mathlib's simulators.
    Its state type is still infinite; the finite-support theorem is separate. -/
def tm0ListInterpreter (C : Turing.ToPartrec.Code) :
    RawTM0State → SimAlphabet → Option (RawTM0State × Turing.TM0.Stmt SimAlphabet) := by
  letI : Inhabited StackLabel := ⟨Turing.PartrecToTM2.trNormal C Turing.PartrecToTM2.Cont'.halt⟩
  exact Turing.TM1to0.tr tm1ListInterpreter

def tm0ListInput (xs : List Nat) : List SimAlphabet :=
  Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main (Turing.PartrecToTM2.trList xs)

theorem tm2List_init (C : Turing.ToPartrec.Code) (xs : List Nat) :
    letI : Inhabited StackLabel := ⟨Turing.PartrecToTM2.trNormal C Turing.PartrecToTM2.Cont'.halt⟩
    Turing.TM2.init Turing.PartrecToTM2.K'.main (Turing.PartrecToTM2.trList xs) =
      Turing.PartrecToTM2.init C xs := by
  classical
  simp only [Turing.TM2.init, Turing.PartrecToTM2.init]
  congr 1
  funext k
  cases k <;> simp [Turing.PartrecToTM2.K'.elim, Function.update]

set_option linter.style.haveILetI false in
theorem tm2List_output (C : Turing.ToPartrec.Code) (xs : List Nat) :
    letI : Inhabited StackLabel := ⟨Turing.PartrecToTM2.trNormal C Turing.PartrecToTM2.Cont'.halt⟩
    Turing.TM2.eval Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main (Turing.PartrecToTM2.trList xs) =
      (C.eval xs).map Turing.PartrecToTM2.trList := by
  classical
  letI : Inhabited StackLabel := ⟨Turing.PartrecToTM2.trNormal C Turing.PartrecToTM2.Cont'.halt⟩
  change (StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
    (Turing.TM2.init Turing.PartrecToTM2.K'.main (Turing.PartrecToTM2.trList xs))).map
      (fun c => c.stk Turing.PartrecToTM2.K'.main) = _
  rw [tm2List_init, Turing.PartrecToTM2.tr_eval]
  change Part.map (fun c : Turing.PartrecToTM2.Cfg' => c.stk Turing.PartrecToTM2.K'.main)
    (Part.map Turing.PartrecToTM2.halt (C.eval xs)) = _
  rw [Part.map_map]
  rfl

def tm0ListInitialState (C : Turing.ToPartrec.Code) : RawTM0State :=
  (some (tm1ListInterpreter (.normal (Turing.PartrecToTM2.trNormal C Turing.PartrecToTM2.Cont'.halt))), none)

/-- Finite reachable state support supplied by Mathlib's simulations. Its
    classical construction is not claimed to be an executable table extractor. -/
noncomputable def tm0ListSupport (C : Turing.ToPartrec.Code) : Finset RawTM0State := by
  classical
  letI : Inhabited StackLabel := ⟨Turing.PartrecToTM2.trNormal C Turing.PartrecToTM2.Cont'.halt⟩
  exact Turing.TM1to0.trStmts tm1ListInterpreter
    (Turing.TM2to1.trSupp Turing.PartrecToTM2.tr
      (Turing.PartrecToTM2.codeSupp C Turing.PartrecToTM2.Cont'.halt))

set_option linter.style.haveILetI false in
theorem tm0List_supported (C : Turing.ToPartrec.Code) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    Turing.TM0.Supports (tm0ListInterpreter C) ↑(tm0ListSupport C) := by
  classical
  letI : Inhabited StackLabel := ⟨Turing.PartrecToTM2.trNormal C Turing.PartrecToTM2.Cont'.halt⟩
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  have hs2 := Turing.PartrecToTM2.tr_supports C Turing.PartrecToTM2.Cont'.halt
  have hs1 := Turing.TM2to1.tr_supports Turing.PartrecToTM2.tr hs2
  exact Turing.TM1to0.tr_supports tm1ListInterpreter hs1

set_option linter.style.haveILetI false in
/-- The full TM2-to-TM1-to-TM0 simulator has the same evaluation domain as
    the source list code on the explicitly encoded input. -/
theorem tm0List_domain (C : Turing.ToPartrec.Code) (xs : List Nat) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    (Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput xs)).Dom ↔ (C.eval xs).Dom := by
  classical
  letI : Inhabited StackLabel := ⟨Turing.PartrecToTM2.trNormal C Turing.PartrecToTM2.Cont'.halt⟩
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  have h01 : Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput xs) =
      Turing.TM1.eval tm1ListInterpreter (tm0ListInput xs) := by
    exact Turing.TM1to0.tr_eval tm1ListInterpreter (tm0ListInput xs)
  have h12 := Turing.TM2to1.tr_eval_dom Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main
    (Turing.PartrecToTM2.trList xs)
  have hdom : (Turing.TM2.eval Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main
      (Turing.PartrecToTM2.trList xs)).Dom ↔ (C.eval xs).Dom := by
    rw [tm2List_output]
    rfl
  rw [h01]
  exact h12.trans hdom

set_option linter.style.haveILetI false in
/-- When both outputs are known members, the simulated tape contains the
    translated output stack. This retains both hypotheses of `TM2to1.tr_eval`. -/
theorem tm0List_output_relation (C : Turing.ToPartrec.Code) (xs ys : List Nat)
    (out : Turing.ListBlank SimAlphabet) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput xs) → ys ∈ C.eval xs →
    ∃ (S : ∀ _ : StackIndex, List StackSymbol) (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol)),
      Turing.TM2to1.addBottom L = out ∧
      (∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse) ∧
      S Turing.PartrecToTM2.K'.main = Turing.PartrecToTM2.trList ys := by
  classical
  letI : Inhabited StackLabel := ⟨Turing.PartrecToTM2.trNormal C Turing.PartrecToTM2.Cont'.halt⟩
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  intro h0 hcode
  have h1 : out ∈ Turing.TM1.eval tm1ListInterpreter (tm0ListInput xs) := by
    rw [← Turing.TM1to0.tr_eval tm1ListInterpreter (tm0ListInput xs)]
    exact h0
  have h2 : Turing.PartrecToTM2.trList ys ∈
      Turing.TM2.eval Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main (Turing.PartrecToTM2.trList xs) := by
    rw [tm2List_output]
    exact (Part.mem_map_iff _).2 ⟨ys, hcode, rfl⟩
  exact Turing.TM2to1.tr_eval Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main
    (Turing.PartrecToTM2.trList xs) h1 h2

/-- Remove blank cells from a quotient tape. Trailing blank extension does not
    change the result; internal blanks are removed as well. -/
def stripOptionBlanks (t : Turing.ListBlank (Option StackSymbol)) : List StackSymbol :=
  t.liftOn (fun xs => xs.filterMap id) (by
    rintro xs _ ⟨n, rfl⟩
    change xs.filterMap id = (xs ++ List.replicate n (none : Option StackSymbol)).filterMap id
    simp)

def tm0ProjectedStack (out : Turing.ListBlank SimAlphabet) : List StackSymbol :=
  (stripOptionBlanks ((out.map ⟨Prod.snd, rfl⟩).map
    (Turing.proj Turing.PartrecToTM2.K'.main))).reverse

set_option linter.style.haveILetI false in
theorem tm0List_output_stack (C : Turing.ToPartrec.Code) (xs ys : List Nat)
    (out : Turing.ListBlank SimAlphabet) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput xs) → ys ∈ C.eval xs →
    tm0ProjectedStack out = Turing.PartrecToTM2.trList ys := by
  intro h0 hc
  obtain ⟨S, L, hL, hp, hs⟩ := tm0List_output_relation C xs ys out h0 hc
  subst out
  simp only [tm0ProjectedStack, Turing.TM2to1.addBottom_map, hp,
    stripOptionBlanks, Turing.ListBlank.mk]
  simp [hs]

def decodeSingleton : List StackSymbol → Option Nat
  | [.cons] => some 0
  | .bit0 :: rest => (decodeSingleton rest).map (fun n => 2 * n)
  | .bit1 :: rest => (decodeSingleton rest).map (fun n => 2 * n + 1)
  | _ => none

theorem decodeSingleton_pos (n : PosNum) :
    decodeSingleton (Turing.PartrecToTM2.trPosNum n ++ [.cons]) = some (n : Nat) := by
  induction n with
  | one => rfl
  | bit0 n ih => simp [Turing.PartrecToTM2.trPosNum, decodeSingleton, ih,
      PosNum.cast_bit0, two_mul]
  | bit1 n ih => simp [Turing.PartrecToTM2.trPosNum, decodeSingleton, ih,
      PosNum.cast_bit1, two_mul]

theorem decodeSingleton_trList (n : Nat) :
    decodeSingleton (Turing.PartrecToTM2.trList [n]) = some n := by
  have h : decodeSingleton (Turing.PartrecToTM2.trNum (n : Num) ++ [.cons]) = some n := by
    generalize hn : (n : Num) = num
    have hcast : (num : Nat) = n := by rw [← hn, Num.to_of_nat]
    cases num with
    | zero => simp [Turing.PartrecToTM2.trNum, decodeSingleton] at hcast ⊢
              exact hcast
    | pos p =>
      change (p : Nat) = n at hcast
      simpa [Turing.PartrecToTM2.trNum, hcast] using decodeSingleton_pos p
  simpa [Turing.PartrecToTM2.trList, Turing.PartrecToTM2.trNat] using h

def tm0DecodedNumber (out : Turing.ListBlank SimAlphabet) : Option Nat :=
  decodeSingleton (tm0ProjectedStack out)

set_option linter.style.haveILetI false in
/-- For the supported compiler fragment, a decoded TM0 result exists exactly
    when the original partial numerical code has that result. -/
theorem compileListCode_tm0_numerical_iff (c : Nat.Partrec.Code)
    (C : Turing.ToPartrec.Code) (h : compileListCode c = some C) (n m : Nat) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    (∃ out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ m ∈ Nat.Partrec.Code.eval c n := by
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  have hrep := (compileListCode_sound c C h) n
  constructor
  · rintro ⟨out, hout, hdecode⟩
    have hd : (C.eval [n]).Dom := (tm0List_domain C [n]).1 (Part.dom_iff_mem.2 ⟨out, hout⟩)
    obtain ⟨ys, hys⟩ := Part.dom_iff_mem.1 hd
    rw [hrep] at hys
    obtain ⟨k, hk, hys⟩ := (Part.mem_map_iff _).1 hys
    subst ys
    have hstack := tm0List_output_stack C [n] [k] out hout
      (by rw [hrep]; exact (Part.mem_map_iff _).2 ⟨k, hk, rfl⟩)
    simp only [tm0DecodedNumber, hstack, decodeSingleton_trList, Option.some.injEq] at hdecode
    simpa [hdecode] using hk
  · intro hm
    have hc : [m] ∈ C.eval [n] := by
      rw [hrep]
      exact (Part.mem_map_iff _).2 ⟨m, hm, rfl⟩
    have hd : (Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n])).Dom :=
      (tm0List_domain C [n]).2 (Part.dom_iff_mem.2 ⟨[m], hc⟩)
    obtain ⟨out, hout⟩ := Part.dom_iff_mem.1 hd
    refine ⟨out, hout, ?_⟩
    unfold tm0DecodedNumber
    rw [tm0List_output_stack C [n] [m] out hout hc]
    exact decodeSingleton_trList m

#print axioms tm2List_init
#print axioms tm2List_output
#print axioms tm0List_supported
#print axioms tm0List_domain
#print axioms tm0List_output_relation
#print axioms tm0List_output_stack
#print axioms compileListCode_tm0_numerical_iff

end LambdaTuring
