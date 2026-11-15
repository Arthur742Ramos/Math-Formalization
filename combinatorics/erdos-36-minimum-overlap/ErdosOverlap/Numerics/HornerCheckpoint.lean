/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.PolynomialBoxCachePair

/-!
# Exact checkpoints for fixed-point interval Horner evaluation

Each checked block has bounded expression depth. A literal checkpoint is
verified to be the exact suffix value, not merely an estimated enclosure.
The proof reconstructs the original Horner expression by list concatenation.
No property of the box endpoints or positive block width is assumed.
-/

namespace ErdosOverlap.Numerics

public section

namespace FixedBox

@[expose] def hornerChunk (I : FixedBox) : List FixedBox → FixedBox → FixedBox
  | [], tail => tail
  | c :: cs, tail => c.add (I.mul (hornerChunk I cs tail))

theorem hornerBoxes_append (I : FixedBox) (cs ds : List FixedBox) :
    hornerBoxes I (cs ++ ds) = hornerChunk I cs (hornerBoxes I ds) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, hornerBoxes, hornerChunk, ih]

@[expose] def hornerCheckpointCheck (I : FixedBox) (width : ℕ)
    (cs : List FixedBox) (result : FixedBox) : List FixedBox → Bool
  | [] => decide (cs = [] ∧ result = ofRat 0)
  | next :: rest =>
    decide (result = hornerChunk I (cs.take width) next) &&
      hornerCheckpointCheck I width (cs.drop width) next rest

theorem hornerCheckpointCheck_sound {I : FixedBox} {width : ℕ}
    {cs : List FixedBox} {result : FixedBox} {tails : List FixedBox}
    (hc : hornerCheckpointCheck I width cs result tails = true) :
    result = hornerBoxes I cs := by
  induction tails generalizing cs result with
  | nil =>
    have hs : cs = [] ∧ result = ofRat 0 := of_decide_eq_true hc
    rw [hs.1]
    exact hs.2
  | cons next rest ih =>
    change decide (result = hornerChunk I (cs.take width) next) &&
      hornerCheckpointCheck I width (cs.drop width) next rest = true at hc
    have hs := Bool.and_eq_true_iff.mp hc
    have hstep : result = hornerChunk I (cs.take width) next := of_decide_eq_true hs.1
    rw [hstep, ih hs.2, ← hornerBoxes_append, List.take_append_drop]

end FixedBox

structure HornerCheckpoint where
  result : FixedBox
  tails : List FixedBox
  deriving DecidableEq, Repr

@[expose] def HornerCheckpoint.check (c : HornerCheckpoint) (I : FixedBox)
    (width : ℕ) (cs : List FixedBox) : Bool :=
  FixedBox.hornerCheckpointCheck I width cs c.result c.tails

theorem HornerCheckpoint.check_sound {c : HornerCheckpoint} {I : FixedBox}
    {width : ℕ} {cs : List FixedBox} (hc : c.check I width cs = true) :
    c.result = FixedBox.hornerBoxes I cs :=
  FixedBox.hornerCheckpointCheck_sound hc

end
end ErdosOverlap.Numerics
