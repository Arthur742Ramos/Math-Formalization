/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness000
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness001
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness002
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness003
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness004
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness005
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness006
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness007
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness008
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness009
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness010
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness011
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness012
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness013
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness014
public import ErdosOverlap.Certificate.Native6Grid.CoefficientSoundness015

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientRows_checked (j : ℕ) (hj : j < 1024) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  by_cases h0512 : j < 512
  · by_cases h0256 : j < 256
    · by_cases h0128 : j < 128
      · by_cases h0064 : j < 64
        · exact coefficients_chunk000 j (by omega) (by omega)
        · exact coefficients_chunk001 j (by omega) (by omega)
      · by_cases h0192 : j < 192
        · exact coefficients_chunk002 j (by omega) (by omega)
        · exact coefficients_chunk003 j (by omega) (by omega)
    · by_cases h0384 : j < 384
      · by_cases h0320 : j < 320
        · exact coefficients_chunk004 j (by omega) (by omega)
        · exact coefficients_chunk005 j (by omega) (by omega)
      · by_cases h0448 : j < 448
        · exact coefficients_chunk006 j (by omega) (by omega)
        · exact coefficients_chunk007 j (by omega) (by omega)
  · by_cases h0768 : j < 768
    · by_cases h0640 : j < 640
      · by_cases h0576 : j < 576
        · exact coefficients_chunk008 j (by omega) (by omega)
        · exact coefficients_chunk009 j (by omega) (by omega)
      · by_cases h0704 : j < 704
        · exact coefficients_chunk010 j (by omega) (by omega)
        · exact coefficients_chunk011 j (by omega) (by omega)
    · by_cases h0896 : j < 896
      · by_cases h0832 : j < 832
        · exact coefficients_chunk012 j (by omega) (by omega)
        · exact coefficients_chunk013 j (by omega) (by omega)
      · by_cases h0960 : j < 960
        · exact coefficients_chunk014 j (by omega) (by omega)
        · exact coefficients_chunk015 j (by omega) (by omega)

end
end ErdosOverlap.Native6Grid
