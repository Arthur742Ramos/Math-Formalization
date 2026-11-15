module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck019
public import ErdosOverlap.Certificate.Native6Grid.Coefficients02

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0152 :
    completeCoefficientRowCheck factorRow row0152 152 coefficients0152 = true := by
  have hlen : coefficients0152.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0152 oddDots0152
      641 152 0 coefficients0152 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0152_checked oddSum0152_checked hlen hs

theorem coefficientCheck0153 :
    completeCoefficientRowCheck factorRow row0153 153 coefficients0153 = true := by
  have hlen : coefficients0153.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0153 oddDots0153
      641 153 0 coefficients0153 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0153_checked oddSum0153_checked hlen hs

theorem coefficientCheck0154 :
    completeCoefficientRowCheck factorRow row0154 154 coefficients0154 = true := by
  have hlen : coefficients0154.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0154 oddDots0154
      641 154 0 coefficients0154 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0154_checked oddSum0154_checked hlen hs

theorem coefficientCheck0155 :
    completeCoefficientRowCheck factorRow row0155 155 coefficients0155 = true := by
  have hlen : coefficients0155.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0155 oddDots0155
      641 155 0 coefficients0155 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0155_checked oddSum0155_checked hlen hs

theorem coefficientCheck0156 :
    completeCoefficientRowCheck factorRow row0156 156 coefficients0156 = true := by
  have hlen : coefficients0156.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0156 oddDots0156
      641 156 0 coefficients0156 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0156_checked oddSum0156_checked hlen hs

theorem coefficientCheck0157 :
    completeCoefficientRowCheck factorRow row0157 157 coefficients0157 = true := by
  have hlen : coefficients0157.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0157 oddDots0157
      641 157 0 coefficients0157 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0157_checked oddSum0157_checked hlen hs

theorem coefficientCheck0158 :
    completeCoefficientRowCheck factorRow row0158 158 coefficients0158 = true := by
  have hlen : coefficients0158.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0158 oddDots0158
      641 158 0 coefficients0158 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0158_checked oddSum0158_checked hlen hs

theorem coefficientCheck0159 :
    completeCoefficientRowCheck factorRow row0159 159 coefficients0159 = true := by
  have hlen : coefficients0159.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0159 oddDots0159
      641 159 0 coefficients0159 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0159_checked oddSum0159_checked hlen hs


end
end ErdosOverlap.Native6Grid
