module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck030
public import ErdosOverlap.Certificate.Native6Grid.Coefficients03

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0240 :
    completeCoefficientRowCheck factorRow row0240 240 coefficients0240 = true := by
  have hlen : coefficients0240.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0240 oddDots0240
      641 240 0 coefficients0240 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0240_checked oddSum0240_checked hlen hs

theorem coefficientCheck0241 :
    completeCoefficientRowCheck factorRow row0241 241 coefficients0241 = true := by
  have hlen : coefficients0241.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0241 oddDots0241
      641 241 0 coefficients0241 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0241_checked oddSum0241_checked hlen hs

theorem coefficientCheck0242 :
    completeCoefficientRowCheck factorRow row0242 242 coefficients0242 = true := by
  have hlen : coefficients0242.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0242 oddDots0242
      641 242 0 coefficients0242 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0242_checked oddSum0242_checked hlen hs

theorem coefficientCheck0243 :
    completeCoefficientRowCheck factorRow row0243 243 coefficients0243 = true := by
  have hlen : coefficients0243.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0243 oddDots0243
      641 243 0 coefficients0243 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0243_checked oddSum0243_checked hlen hs

theorem coefficientCheck0244 :
    completeCoefficientRowCheck factorRow row0244 244 coefficients0244 = true := by
  have hlen : coefficients0244.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0244 oddDots0244
      641 244 0 coefficients0244 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0244_checked oddSum0244_checked hlen hs

theorem coefficientCheck0245 :
    completeCoefficientRowCheck factorRow row0245 245 coefficients0245 = true := by
  have hlen : coefficients0245.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0245 oddDots0245
      641 245 0 coefficients0245 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0245_checked oddSum0245_checked hlen hs

theorem coefficientCheck0246 :
    completeCoefficientRowCheck factorRow row0246 246 coefficients0246 = true := by
  have hlen : coefficients0246.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0246 oddDots0246
      641 246 0 coefficients0246 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0246_checked oddSum0246_checked hlen hs

theorem coefficientCheck0247 :
    completeCoefficientRowCheck factorRow row0247 247 coefficients0247 = true := by
  have hlen : coefficients0247.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0247 oddDots0247
      641 247 0 coefficients0247 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0247_checked oddSum0247_checked hlen hs


end
end ErdosOverlap.Native6Grid
