module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck017
public import ErdosOverlap.Certificate.Native6Grid.Coefficients02

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0136 :
    completeCoefficientRowCheck factorRow row0136 136 coefficients0136 = true := by
  have hlen : coefficients0136.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0136 oddDots0136
      641 136 0 coefficients0136 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0136_checked oddSum0136_checked hlen hs

theorem coefficientCheck0137 :
    completeCoefficientRowCheck factorRow row0137 137 coefficients0137 = true := by
  have hlen : coefficients0137.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0137 oddDots0137
      641 137 0 coefficients0137 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0137_checked oddSum0137_checked hlen hs

theorem coefficientCheck0138 :
    completeCoefficientRowCheck factorRow row0138 138 coefficients0138 = true := by
  have hlen : coefficients0138.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0138 oddDots0138
      641 138 0 coefficients0138 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0138_checked oddSum0138_checked hlen hs

theorem coefficientCheck0139 :
    completeCoefficientRowCheck factorRow row0139 139 coefficients0139 = true := by
  have hlen : coefficients0139.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0139 oddDots0139
      641 139 0 coefficients0139 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0139_checked oddSum0139_checked hlen hs

theorem coefficientCheck0140 :
    completeCoefficientRowCheck factorRow row0140 140 coefficients0140 = true := by
  have hlen : coefficients0140.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0140 oddDots0140
      641 140 0 coefficients0140 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0140_checked oddSum0140_checked hlen hs

theorem coefficientCheck0141 :
    completeCoefficientRowCheck factorRow row0141 141 coefficients0141 = true := by
  have hlen : coefficients0141.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0141 oddDots0141
      641 141 0 coefficients0141 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0141_checked oddSum0141_checked hlen hs

theorem coefficientCheck0142 :
    completeCoefficientRowCheck factorRow row0142 142 coefficients0142 = true := by
  have hlen : coefficients0142.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0142 oddDots0142
      641 142 0 coefficients0142 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0142_checked oddSum0142_checked hlen hs

theorem coefficientCheck0143 :
    completeCoefficientRowCheck factorRow row0143 143 coefficients0143 = true := by
  have hlen : coefficients0143.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0143 oddDots0143
      641 143 0 coefficients0143 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0143_checked oddSum0143_checked hlen hs


end
end ErdosOverlap.Native6Grid
