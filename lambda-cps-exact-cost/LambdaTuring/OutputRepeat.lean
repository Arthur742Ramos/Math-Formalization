/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputValueLoop
public meta import LambdaTuring.OutputValueLoop

@[expose] public section

namespace LambdaTuring.Machine

/- Iterate the value-dependent bit-one pass. The count is a proof parameter;
the program control is finite and the scratch itself lives on the tape. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem outputValueLoop_repeat (count : Nat) (t : Tape) (gap n : Nat)
    (old : Turing.ListBlank Symbol) (R : Turing.ListBlank SimAlphabet)
    (ht : mathTape t = Turing.Tape.mk' (safeScratch gap n old) (encodeBlankSide R))
    (hbits : ∀ i, i < count →
      (encodeSimAlphabet (((Turing.ListBlank.tail^[i]) R).head)).main = some .bit1) :
    ∃ u, Reaches outputValueLoop ⟨⟨0, by omega⟩, t⟩ ⟨⟨0, by omega⟩, u⟩ ∧
      mathTape u = Turing.Tape.mk'
        (safeScratch (13*count+gap) (n+count) ((Turing.ListBlank.tail^[count]) old))
        (encodeBlankSide ((Turing.ListBlank.tail^[count]) R)) := by
  induction count generalizing t gap n old R with
  | zero =>
    refine ⟨t, .refl _, ?_⟩
    simpa using ht
  | succ count ih =>
    have hbit : (encodeSimAlphabet R.head).main = some .bit1 := by simpa using hbits 0 (by omega)
    obtain ⟨u, hu, hut⟩ := outputValueLoop_one t gap n old R ht hbit
    have hrest : ∀ i, i < count →
        (encodeSimAlphabet (((Turing.ListBlank.tail^[i]) R.tail).head)).main = some .bit1 := by
      intro i hi
      simpa [Function.iterate_succ_apply] using hbits (i+1) (by omega)
    obtain ⟨v, hv, hvt⟩ := ih u (13+gap) (n+1) old.tail R.tail hut hrest
    refine ⟨v, reaches_trans hu hv, ?_⟩
    simpa [Function.iterate_succ_apply, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvt

set_option backward.isDefEq.respectTransparency false in
theorem outputMain_tail_head (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (m i : Nat)
    (hshape : L.map (Turing.proj Turing.PartrecToTM2.K'.main) =
      Turing.ListBlank.mk (some Turing.PartrecToTM2.Γ'.cons ::
        List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1))) :
    (encodeSimAlphabet (((Turing.ListBlank.tail^[i]) (Turing.TM2to1.addBottom L)).head)).main =
      (some Turing.PartrecToTM2.Γ'.cons ::
        List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1)).getI i := by
  rw [← Turing.ListBlank.nth_zero, blank_tail_iter_nth]
  simp only [Nat.add_zero, encodeSimAlphabet, Turing.TM2to1.addBottom_nth_snd]
  rw [← Turing.proj_map_nth, hshape, Turing.ListBlank.nth_mk]

theorem outputMain_tail_bit (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (m i : Nat)
    (hshape : L.map (Turing.proj Turing.PartrecToTM2.K'.main) =
      Turing.ListBlank.mk (some Turing.PartrecToTM2.Γ'.cons ::
        List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1)))
    (hi : i < m+1) :
    (encodeSimAlphabet (((Turing.ListBlank.tail^[i+1]) (Turing.TM2to1.addBottom L)).head)).main =
      some .bit1 := by
  rw [outputMain_tail_head L m (i+1) hshape]
  have hlen : i < (List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1)).length := by simpa
  simp [List.getI_cons_succ, List.getI_eq_getElem _ hlen]

theorem outputMain_tail_end (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (m : Nat)
    (hshape : L.map (Turing.proj Turing.PartrecToTM2.K'.main) =
      Turing.ListBlank.mk (some Turing.PartrecToTM2.Γ'.cons ::
        List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1))) :
    (encodeSimAlphabet (((Turing.ListBlank.tail^[m+2]) (Turing.TM2to1.addBottom L)).head)).main = none := by
  rw [outputMain_tail_head L m (m+2) hshape]
  apply List.getI_eq_default
  simp

/- Starting at the first bit, with empty unary scratch and one reserved blank,
the actual reader-controlled machine copies the entire bit-one run, clears
the remaining tracks, and exposes the public result. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem outputValueLoop_observes (t : Tape) (gap m : Nat)
    (old : Turing.ListBlank Symbol) (S : ∀ _ : StackIndex, List StackSymbol)
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse)
    (hshape : L.map (Turing.proj Turing.PartrecToTM2.K'.main) =
      Turing.ListBlank.mk (some Turing.PartrecToTM2.Γ'.cons ::
        List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1)))
    (ht : mathTape t = Turing.Tape.mk' (safeScratch gap 0 old)
      (encodeBlankSide ((Turing.ListBlank.tail^[1]) (Turing.TM2to1.addBottom L)))) :
    ∃ d, Reaches outputValueLoop ⟨⟨0, by omega⟩, t⟩ d ∧ Halted outputValueLoop d ∧
      decode (d.tape.head :: d.tape.right) = some m := by
  let R := (Turing.ListBlank.tail^[1]) (Turing.TM2to1.addBottom L)
  have hbits : ∀ i, i < m+1 →
      (encodeSimAlphabet (((Turing.ListBlank.tail^[i]) R).head)).main = some .bit1 := by
    intro i hi
    simpa [R, Function.iterate_succ_apply] using outputMain_tail_bit L m i hshape hi
  obtain ⟨u, hu, hut⟩ := outputValueLoop_repeat (m+1) t gap 0 old R ht hbits
  have hu' : mathTape u = Turing.Tape.mk'
      (safeScratch (13*(m+1)+gap) (m+1) ((Turing.ListBlank.tail^[m+1]) old))
      (encodeBlankSide ((Turing.ListBlank.tail^[m+2]) (Turing.TM2to1.addBottom L))) := by
    simpa [R, Function.iterate_succ_apply, Nat.add_assoc] using hut
  obtain ⟨d, hd, hdh, hdec⟩ := outputValueLoop_finish u (13*(m+1)+gap) m (m+2)
    ((Turing.ListBlank.tail^[m+1]) old) S L hproj (by omega) hu' (outputMain_tail_end L m hshape)
  exact ⟨d, reaches_trans hu hd, hdh, hdec⟩

#print axioms outputValueLoop_repeat
#print axioms outputMain_tail_bit
#print axioms outputMain_tail_end
#print axioms outputValueLoop_observes
end LambdaTuring.Machine
