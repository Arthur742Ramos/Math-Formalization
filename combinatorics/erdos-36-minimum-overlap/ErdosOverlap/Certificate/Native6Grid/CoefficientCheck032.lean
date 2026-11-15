module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck032
public import ErdosOverlap.Certificate.Native6Grid.Coefficients04

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0256 :
    completeCoefficientRowCheck factorRow row0256 256 coefficients0256 = true := by
  have hlen : coefficients0256.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0256 oddDots0256
      641 256 0 coefficients0256 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0256_checked oddSum0256_checked hlen hs

theorem coefficientCheck0257 :
    completeCoefficientRowCheck factorRow row0257 257 coefficients0257 = true := by
  have hlen : coefficients0257.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0257 oddDots0257
      641 257 0 coefficients0257 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0257_checked oddSum0257_checked hlen hs

theorem coefficientCheck0258 :
    completeCoefficientRowCheck factorRow row0258 258 coefficients0258 = true := by
  have hlen : coefficients0258.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0258 oddDots0258
      641 258 0 coefficients0258 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0258_checked oddSum0258_checked hlen hs

theorem coefficientCheck0259 :
    completeCoefficientRowCheck factorRow row0259 259 coefficients0259 = true := by
  have hlen : coefficients0259.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0259 oddDots0259
      641 259 0 coefficients0259 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0259_checked oddSum0259_checked hlen hs

theorem coefficientCheck0260 :
    completeCoefficientRowCheck factorRow row0260 260 coefficients0260 = true := by
  have hlen : coefficients0260.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0260 oddDots0260
      641 260 0 coefficients0260 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0260_checked oddSum0260_checked hlen hs

theorem coefficientCheck0261 :
    completeCoefficientRowCheck factorRow row0261 261 coefficients0261 = true := by
  have hlen : coefficients0261.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0261 oddDots0261
      641 261 0 coefficients0261 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0261_checked oddSum0261_checked hlen hs

theorem coefficientCheck0262 :
    completeCoefficientRowCheck factorRow row0262 262 coefficients0262 = true := by
  have hlen : coefficients0262.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0262 oddDots0262
      641 262 0 coefficients0262 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0262_checked oddSum0262_checked hlen hs

theorem coefficientCheck0263 :
    completeCoefficientRowCheck factorRow row0263 263 coefficients0263 = true := by
  have hlen : coefficients0263.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0263 oddDots0263
      641 263 0 coefficients0263 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0263_checked oddSum0263_checked hlen hs


end
end ErdosOverlap.Native6Grid
