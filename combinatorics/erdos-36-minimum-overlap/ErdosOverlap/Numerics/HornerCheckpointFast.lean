/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FixedBoxFast
public import ErdosOverlap.Numerics.HornerCheckpoint

/-! # Exact sign-aware versions of the existing bounded Horner checker -/

@[expose] public section

namespace ErdosOverlap.Numerics

namespace FixedBox

def hornerChunkFast (I : FixedBox) : List FixedBox → FixedBox → FixedBox
  | [], tail => tail
  | c :: cs, tail => c.add (I.mulFast (hornerChunkFast I cs tail))

theorem hornerChunkFast_eq_hornerChunk (I : FixedBox) (cs : List FixedBox) (tail : FixedBox) :
    hornerChunkFast I cs tail = hornerChunk I cs tail := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [hornerChunkFast, hornerChunk, ih, mulFast_eq_mul]

def hornerCheckpointCheckFast (I : FixedBox) (width : ℕ)
    (cs : List FixedBox) (result : FixedBox) : List FixedBox → Bool
  | [] => decide (cs = [] ∧ result = ofRat 0)
  | next :: rest =>
    decide (result = hornerChunkFast I (cs.take width) next) &&
      hornerCheckpointCheckFast I width (cs.drop width) next rest

theorem hornerCheckpointCheckFast_eq (I : FixedBox) (width : ℕ)
    (cs : List FixedBox) (result : FixedBox) (tails : List FixedBox) :
    hornerCheckpointCheckFast I width cs result tails =
      hornerCheckpointCheck I width cs result tails := by
  induction tails generalizing cs result with
  | nil => rfl
  | cons next rest ih =>
    simp only [hornerCheckpointCheckFast, hornerCheckpointCheck,
      hornerChunkFast_eq_hornerChunk, ih]

theorem hornerCheckpointCheckFast_sound {I : FixedBox} {width : ℕ}
    {cs : List FixedBox} {result : FixedBox} {tails : List FixedBox}
    (hc : hornerCheckpointCheckFast I width cs result tails = true) :
    result = hornerBoxes I cs := by
  rw [hornerCheckpointCheckFast_eq] at hc
  exact hornerCheckpointCheck_sound hc

end FixedBox

def HornerCheckpoint.checkFast (c : HornerCheckpoint) (I : FixedBox)
    (width : ℕ) (cs : List FixedBox) : Bool :=
  FixedBox.hornerCheckpointCheckFast I width cs c.result c.tails

theorem HornerCheckpoint.checkFast_eq_check (c : HornerCheckpoint) (I : FixedBox)
    (width : ℕ) (cs : List FixedBox) : c.checkFast I width cs = c.check I width cs :=
  FixedBox.hornerCheckpointCheckFast_eq I width cs c.result c.tails

theorem HornerCheckpoint.checkFast_sound {c : HornerCheckpoint} {I : FixedBox}
    {width : ℕ} {cs : List FixedBox} (hc : c.checkFast I width cs = true) :
    c.result = FixedBox.hornerBoxes I cs :=
  FixedBox.hornerCheckpointCheckFast_sound hc

end ErdosOverlap.Numerics
