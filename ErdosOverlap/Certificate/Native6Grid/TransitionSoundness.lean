/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness000
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness001
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness002
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness003
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness004
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness005
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness006
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness007
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness008
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness009
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness010
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness011
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness012
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness013
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness014
public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness015

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_checked (j : ℕ) (hj : j + 1 < 1024) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  by_cases h0512 : j < 512
  · by_cases h0256 : j < 256
    · by_cases h0128 : j < 128
      · by_cases h0064 : j < 64
        · exact transitions_chunk000 j (by omega) (by omega)
        · exact transitions_chunk001 j (by omega) (by omega)
      · by_cases h0192 : j < 192
        · exact transitions_chunk002 j (by omega) (by omega)
        · exact transitions_chunk003 j (by omega) (by omega)
    · by_cases h0384 : j < 384
      · by_cases h0320 : j < 320
        · exact transitions_chunk004 j (by omega) (by omega)
        · exact transitions_chunk005 j (by omega) (by omega)
      · by_cases h0448 : j < 448
        · exact transitions_chunk006 j (by omega) (by omega)
        · exact transitions_chunk007 j (by omega) (by omega)
  · by_cases h0768 : j < 768
    · by_cases h0640 : j < 640
      · by_cases h0576 : j < 576
        · exact transitions_chunk008 j (by omega) (by omega)
        · exact transitions_chunk009 j (by omega) (by omega)
      · by_cases h0704 : j < 704
        · exact transitions_chunk010 j (by omega) (by omega)
        · exact transitions_chunk011 j (by omega) (by omega)
    · by_cases h0896 : j < 896
      · by_cases h0832 : j < 832
        · exact transitions_chunk012 j (by omega) (by omega)
        · exact transitions_chunk013 j (by omega) (by omega)
      · by_cases h0960 : j < 960
        · exact transitions_chunk014 j (by omega) (by omega)
        · exact transitions_chunk015 j (by omega) (by omega)

end
end ErdosOverlap.Native6Grid
