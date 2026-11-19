/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.FrontierPieceData
public import ErdosOverlap.Certificate.FrontierJumpBinding

namespace ErdosOverlap.FrontierJumps
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem fullPieces_eq_fast : fullPieces = compileAffinePiecesFast (-1) 3 0 0 finalJumps := by
  apply affinePiecesEqual_sound
  decide +kernel

theorem fullPieces_eq : fullPieces = compileAffinePieces (-1) 3 0 0 finalJumps := by
  rw [fullPieces_eq_fast, compileAffinePiecesFast_eq]

end
end ErdosOverlap.FrontierJumps
