module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck040
public import ErdosOverlap.Certificate.Native6Grid.Coefficients05

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0320 :
    completeCoefficientRowCheck factorRow row0320 320 coefficients0320 = true := by
  have hlen : coefficients0320.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0320 oddDots0320
      641 320 0 coefficients0320 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0320_checked oddSum0320_checked hlen hs

theorem coefficientCheck0321 :
    completeCoefficientRowCheck factorRow row0321 321 coefficients0321 = true := by
  have hlen : coefficients0321.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0321 oddDots0321
      641 321 0 coefficients0321 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0321_checked oddSum0321_checked hlen hs

theorem coefficientCheck0322 :
    completeCoefficientRowCheck factorRow row0322 322 coefficients0322 = true := by
  have hlen : coefficients0322.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0322 oddDots0322
      641 322 0 coefficients0322 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0322_checked oddSum0322_checked hlen hs

theorem coefficientCheck0323 :
    completeCoefficientRowCheck factorRow row0323 323 coefficients0323 = true := by
  have hlen : coefficients0323.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0323 oddDots0323
      641 323 0 coefficients0323 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0323_checked oddSum0323_checked hlen hs

theorem coefficientCheck0324 :
    completeCoefficientRowCheck factorRow row0324 324 coefficients0324 = true := by
  have hlen : coefficients0324.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0324 oddDots0324
      641 324 0 coefficients0324 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0324_checked oddSum0324_checked hlen hs

theorem coefficientCheck0325 :
    completeCoefficientRowCheck factorRow row0325 325 coefficients0325 = true := by
  have hlen : coefficients0325.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0325 oddDots0325
      641 325 0 coefficients0325 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0325_checked oddSum0325_checked hlen hs

theorem coefficientCheck0326 :
    completeCoefficientRowCheck factorRow row0326 326 coefficients0326 = true := by
  have hlen : coefficients0326.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0326 oddDots0326
      641 326 0 coefficients0326 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0326_checked oddSum0326_checked hlen hs

theorem coefficientCheck0327 :
    completeCoefficientRowCheck factorRow row0327 327 coefficients0327 = true := by
  have hlen : coefficients0327.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0327 oddDots0327
      641 327 0 coefficients0327 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0327_checked oddSum0327_checked hlen hs


end
end ErdosOverlap.Native6Grid
