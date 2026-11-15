module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck013
public import ErdosOverlap.Certificate.Native6Grid.Coefficients01

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0104 :
    completeCoefficientRowCheck factorRow row0104 104 coefficients0104 = true := by
  have hlen : coefficients0104.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0104 oddDots0104
      641 104 0 coefficients0104 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0104_checked oddSum0104_checked hlen hs

theorem coefficientCheck0105 :
    completeCoefficientRowCheck factorRow row0105 105 coefficients0105 = true := by
  have hlen : coefficients0105.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0105 oddDots0105
      641 105 0 coefficients0105 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0105_checked oddSum0105_checked hlen hs

theorem coefficientCheck0106 :
    completeCoefficientRowCheck factorRow row0106 106 coefficients0106 = true := by
  have hlen : coefficients0106.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0106 oddDots0106
      641 106 0 coefficients0106 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0106_checked oddSum0106_checked hlen hs

theorem coefficientCheck0107 :
    completeCoefficientRowCheck factorRow row0107 107 coefficients0107 = true := by
  have hlen : coefficients0107.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0107 oddDots0107
      641 107 0 coefficients0107 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0107_checked oddSum0107_checked hlen hs

theorem coefficientCheck0108 :
    completeCoefficientRowCheck factorRow row0108 108 coefficients0108 = true := by
  have hlen : coefficients0108.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0108 oddDots0108
      641 108 0 coefficients0108 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0108_checked oddSum0108_checked hlen hs

theorem coefficientCheck0109 :
    completeCoefficientRowCheck factorRow row0109 109 coefficients0109 = true := by
  have hlen : coefficients0109.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0109 oddDots0109
      641 109 0 coefficients0109 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0109_checked oddSum0109_checked hlen hs

theorem coefficientCheck0110 :
    completeCoefficientRowCheck factorRow row0110 110 coefficients0110 = true := by
  have hlen : coefficients0110.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0110 oddDots0110
      641 110 0 coefficients0110 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0110_checked oddSum0110_checked hlen hs

theorem coefficientCheck0111 :
    completeCoefficientRowCheck factorRow row0111 111 coefficients0111 = true := by
  have hlen : coefficients0111.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0111 oddDots0111
      641 111 0 coefficients0111 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0111_checked oddSum0111_checked hlen hs


end
end ErdosOverlap.Native6Grid
