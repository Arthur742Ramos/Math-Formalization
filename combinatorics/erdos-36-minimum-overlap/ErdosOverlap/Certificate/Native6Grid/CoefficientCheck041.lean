module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck041
public import ErdosOverlap.Certificate.Native6Grid.Coefficients05

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0328 :
    completeCoefficientRowCheck factorRow row0328 328 coefficients0328 = true := by
  have hlen : coefficients0328.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0328 oddDots0328
      641 328 0 coefficients0328 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0328_checked oddSum0328_checked hlen hs

theorem coefficientCheck0329 :
    completeCoefficientRowCheck factorRow row0329 329 coefficients0329 = true := by
  have hlen : coefficients0329.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0329 oddDots0329
      641 329 0 coefficients0329 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0329_checked oddSum0329_checked hlen hs

theorem coefficientCheck0330 :
    completeCoefficientRowCheck factorRow row0330 330 coefficients0330 = true := by
  have hlen : coefficients0330.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0330 oddDots0330
      641 330 0 coefficients0330 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0330_checked oddSum0330_checked hlen hs

theorem coefficientCheck0331 :
    completeCoefficientRowCheck factorRow row0331 331 coefficients0331 = true := by
  have hlen : coefficients0331.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0331 oddDots0331
      641 331 0 coefficients0331 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0331_checked oddSum0331_checked hlen hs

theorem coefficientCheck0332 :
    completeCoefficientRowCheck factorRow row0332 332 coefficients0332 = true := by
  have hlen : coefficients0332.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0332 oddDots0332
      641 332 0 coefficients0332 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0332_checked oddSum0332_checked hlen hs

theorem coefficientCheck0333 :
    completeCoefficientRowCheck factorRow row0333 333 coefficients0333 = true := by
  have hlen : coefficients0333.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0333 oddDots0333
      641 333 0 coefficients0333 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0333_checked oddSum0333_checked hlen hs

theorem coefficientCheck0334 :
    completeCoefficientRowCheck factorRow row0334 334 coefficients0334 = true := by
  have hlen : coefficients0334.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0334 oddDots0334
      641 334 0 coefficients0334 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0334_checked oddSum0334_checked hlen hs

theorem coefficientCheck0335 :
    completeCoefficientRowCheck factorRow row0335 335 coefficients0335 = true := by
  have hlen : coefficients0335.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0335 oddDots0335
      641 335 0 coefficients0335 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0335_checked oddSum0335_checked hlen hs


end
end ErdosOverlap.Native6Grid
