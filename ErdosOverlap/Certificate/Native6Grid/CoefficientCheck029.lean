module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck029
public import ErdosOverlap.Certificate.Native6Grid.Coefficients03

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0232 :
    completeCoefficientRowCheck factorRow row0232 232 coefficients0232 = true := by
  have hlen : coefficients0232.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0232 oddDots0232
      641 232 0 coefficients0232 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0232_checked oddSum0232_checked hlen hs

theorem coefficientCheck0233 :
    completeCoefficientRowCheck factorRow row0233 233 coefficients0233 = true := by
  have hlen : coefficients0233.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0233 oddDots0233
      641 233 0 coefficients0233 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0233_checked oddSum0233_checked hlen hs

theorem coefficientCheck0234 :
    completeCoefficientRowCheck factorRow row0234 234 coefficients0234 = true := by
  have hlen : coefficients0234.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0234 oddDots0234
      641 234 0 coefficients0234 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0234_checked oddSum0234_checked hlen hs

theorem coefficientCheck0235 :
    completeCoefficientRowCheck factorRow row0235 235 coefficients0235 = true := by
  have hlen : coefficients0235.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0235 oddDots0235
      641 235 0 coefficients0235 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0235_checked oddSum0235_checked hlen hs

theorem coefficientCheck0236 :
    completeCoefficientRowCheck factorRow row0236 236 coefficients0236 = true := by
  have hlen : coefficients0236.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0236 oddDots0236
      641 236 0 coefficients0236 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0236_checked oddSum0236_checked hlen hs

theorem coefficientCheck0237 :
    completeCoefficientRowCheck factorRow row0237 237 coefficients0237 = true := by
  have hlen : coefficients0237.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0237 oddDots0237
      641 237 0 coefficients0237 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0237_checked oddSum0237_checked hlen hs

theorem coefficientCheck0238 :
    completeCoefficientRowCheck factorRow row0238 238 coefficients0238 = true := by
  have hlen : coefficients0238.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0238 oddDots0238
      641 238 0 coefficients0238 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0238_checked oddSum0238_checked hlen hs

theorem coefficientCheck0239 :
    completeCoefficientRowCheck factorRow row0239 239 coefficients0239 = true := by
  have hlen : coefficients0239.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0239 oddDots0239
      641 239 0 coefficients0239 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0239_checked oddSum0239_checked hlen hs


end
end ErdosOverlap.Native6Grid
