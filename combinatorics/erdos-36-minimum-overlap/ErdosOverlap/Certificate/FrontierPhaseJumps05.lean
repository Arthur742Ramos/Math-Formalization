/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.KernelJumps
public import ErdosOverlap.Certificate.FrontierKernelData

namespace ErdosOverlap.FrontierJumps
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def phase05 : List AffineJump := [
  
]

theorem phase05_eq : phase05 = compressedJumps FrontierData.phase05.jumps := by
  apply affineJumpsEqual_sound
  decide +kernel

end
end ErdosOverlap.FrontierJumps
