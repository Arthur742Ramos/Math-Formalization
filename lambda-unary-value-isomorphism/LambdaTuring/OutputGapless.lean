/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ClearEncodedBlock
public meta import LambdaTuring.ClearEncodedBlock

@[expose] public section

namespace LambdaTuring

/-- A list of present stack cells cannot contain a hole before a later cell. -/
theorem presentList_gapless {α : Type} (xs : List α) (i j : Nat) (hij : i ≤ j)
    (hi : ((xs.map some).reverse).getI i = none) :
    ((xs.map some).reverse).getI j = none := by
  rw [← List.map_reverse] at hi ⊢
  by_cases h : i < xs.length
  · have hi' : i < (xs.reverse.map some).length := by simpa using h
    rw [List.getI_eq_getElem _ hi'] at hi
    simp at hi
  · have hj : (xs.reverse.map some).length ≤ j := by simp; omega
    exact List.getI_eq_default _ hj

/- Each simulated stack is contiguous; once all tracks are blank at a
cell, every later cell has blank tracks too. -/
set_option backward.isDefEq.respectTransparency false in
theorem outputTracks_gapless (S : ∀ _ : StackIndex, List StackSymbol)
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse)
    (i j : Nat) (hij : i ≤ j) (hi : L.nth i = fun _ => none) :
    L.nth j = fun _ => none := by
  funext k
  have he_i := congrArg (fun (l : Turing.ListBlank (Option StackSymbol)) => l.nth i) (hproj k)
  have he_j := congrArg (fun (l : Turing.ListBlank (Option StackSymbol)) => l.nth j) (hproj k)
  rw [Turing.proj_map_nth, Turing.ListBlank.nth_mk] at he_i he_j
  have hk : ((S k).map some).reverse.getI i = none := by
    rw [← he_i, hi]
  rw [he_j]
  exact presentList_gapless (S k) i j hij hk

/- Beyond the bottom marker, an entirely blank simulator cell means all
subsequent encoded source cells are blank. -/
set_option backward.isDefEq.respectTransparency false in
theorem outputBottom_gapless (S : ∀ _ : StackIndex, List StackSymbol)
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse)
    (i j : Nat) (hiPos : 0 < i) (hij : i ≤ j)
    (hi : (Turing.TM2to1.addBottom L).nth i = (false, fun _ => none)) :
    (Turing.TM2to1.addBottom L).nth j = (false, fun _ => none) := by
  have hli : L.nth i = fun _ => none := by
    have h := congrArg Prod.snd hi
    simpa only [Turing.TM2to1.addBottom_nth_snd] using h
  have hlj := outputTracks_gapless S L hproj i j hij hli
  cases j with
  | zero => omega
  | succ j =>
    apply Prod.ext
    · exact Turing.TM2to1.addBottom_nth_succ_fst L j
    · simpa only [Turing.TM2to1.addBottom_nth_snd] using hlj

set_option backward.isDefEq.respectTransparency false in
theorem encodedOutput_gapless (S : ∀ _ : StackIndex, List StackSymbol)
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse)
    (i j : Nat) (hiPos : 0 < i) (hij : i ≤ j)
    (hi : decodedBlockAt (encodeBlankSide (Turing.TM2to1.addBottom L)) i = (false, fun _ => none)) :
    decodedBlockAt (encodeBlankSide (Turing.TM2to1.addBottom L)) j = (false, fun _ => none) := by
  rw [decodedBlockAt_encoded] at hi ⊢
  exact outputBottom_gapless S L hproj i j hiPos hij hi

set_option backward.isDefEq.respectTransparency false in
theorem encodedOutput_eventually_blank (S : ∀ _ : StackIndex, List StackSymbol)
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse) :
    ∃ i, 0 < i ∧ ∀ j, i ≤ j →
      decodedBlockAt (encodeBlankSide (Turing.TM2to1.addBottom L)) j = (false, fun _ => none) := by
  let bound := (S .main).length + (S .rev).length + (S .aux).length + (S .stack).length + 1
  have hpos : 0 < bound := by dsimp [bound]; omega
  have hL : L.nth bound = fun _ => none := by
    funext k
    have he := congrArg (fun (l : Turing.ListBlank (Option StackSymbol)) => l.nth bound) (hproj k)
    rw [Turing.proj_map_nth, Turing.ListBlank.nth_mk] at he
    rw [he]
    apply List.getI_eq_default
    simp only [List.length_reverse, List.length_map]
    cases k <;> dsimp [bound] <;> omega
  have hblank : (Turing.TM2to1.addBottom L).nth bound = (false, fun _ => none) := by
    cases hb : bound with
    | zero => omega
    | succ k =>
      apply Prod.ext
      · exact Turing.TM2to1.addBottom_nth_succ_fst L k
      · rw [Turing.TM2to1.addBottom_nth_snd]
        simpa [hb] using hL
  refine ⟨bound, hpos, ?_⟩
  intro j hj
  rw [decodedBlockAt_encoded]
  exact outputBottom_gapless S L hproj bound j hpos hj hblank

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem unaryOutput_cleanup_boundary (c : Nat.Partrec.Code) (n m : Nat)
    (hm : m ∈ numericalValue (compileLambdaTotal c) n) :
    let C := compileUnaryOutputCode c
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    ∃ (out : Turing.ListBlank SimAlphabet)
      (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol)) (bound : Nat),
      out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [onesNumber n]) ∧
      Turing.TM2to1.addBottom L = out ∧ 0 < bound ∧
      (∀ j, bound ≤ j → decodedBlockAt (encodeBlankSide out) j = (false, fun _ => none)) ∧
      (∀ i j, 0 < i → i ≤ j →
        decodedBlockAt (encodeBlankSide out) i = (false, fun _ => none) →
        decodedBlockAt (encodeBlankSide out) j = (false, fun _ => none)) := by
  let C := compileUnaryOutputCode c
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  rw [(compileLambdaTotal_sound c).2 n] at hm
  have hc : [onesNumber m] ∈ C.eval [onesNumber n] := by
    rw [compileUnaryOutputCode_eval]
    exact (Part.mem_map_iff _).2 ⟨m, hm, rfl⟩
  have hd : (Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [onesNumber n])).Dom :=
    (tm0List_domain C [onesNumber n]).2 (Part.dom_iff_mem.2 ⟨[onesNumber m], hc⟩)
  obtain ⟨out, hout⟩ := Part.dom_iff_mem.1 hd
  obtain ⟨S, L, heq, hproj, _⟩ :=
    tm0List_output_relation C [onesNumber n] [onesNumber m] out hout hc
  obtain ⟨bound, hpos, hblank⟩ := encodedOutput_eventually_blank S L hproj
  refine ⟨out, L, bound, hout, heq, hpos, ?_, ?_⟩
  · intro j hj
    rw [← heq]
    exact hblank j hj
  · intro i j hi hij hblanki
    rw [← heq] at hblanki ⊢
    exact encodedOutput_gapless S L hproj i j hi hij hblanki

#print axioms outputTracks_gapless
#print axioms encodedOutput_gapless
#print axioms encodedOutput_eventually_blank
#print axioms unaryOutput_cleanup_boundary
end LambdaTuring
