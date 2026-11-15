module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck065
public import ErdosOverlap.Certificate.Native6Grid.Coefficients08

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0520 :
    completeCoefficientRowCheck factorRow row0520 520 coefficients0520 = true := by
  have hlen : coefficients0520.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0520 oddDots0520
      641 520 0 coefficients0520 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0520_checked oddSum0520_checked hlen hs

theorem coefficientCheck0521 :
    completeCoefficientRowCheck factorRow row0521 521 coefficients0521 = true := by
  have hlen : coefficients0521.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0521 oddDots0521
      641 521 0 coefficients0521 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0521_checked oddSum0521_checked hlen hs

theorem coefficientCheck0522 :
    completeCoefficientRowCheck factorRow row0522 522 coefficients0522 = true := by
  have hlen : coefficients0522.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0522 oddDots0522
      641 522 0 coefficients0522 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0522_checked oddSum0522_checked hlen hs

theorem coefficientCheck0523 :
    completeCoefficientRowCheck factorRow row0523 523 coefficients0523 = true := by
  have hlen : coefficients0523.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0523 oddDots0523
      641 523 0 coefficients0523 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0523_checked oddSum0523_checked hlen hs

theorem coefficientCheck0524 :
    completeCoefficientRowCheck factorRow row0524 524 coefficients0524 = true := by
  have hlen : coefficients0524.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0524 oddDots0524
      641 524 0 coefficients0524 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0524_checked oddSum0524_checked hlen hs

theorem coefficientCheck0525 :
    completeCoefficientRowCheck factorRow row0525 525 coefficients0525 = true := by
  have hlen : coefficients0525.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0525 oddDots0525
      641 525 0 coefficients0525 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0525_checked oddSum0525_checked hlen hs

theorem coefficientCheck0526 :
    completeCoefficientRowCheck factorRow row0526 526 coefficients0526 = true := by
  have hlen : coefficients0526.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0526 oddDots0526
      641 526 0 coefficients0526 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0526_checked oddSum0526_checked hlen hs

theorem coefficientCheck0527 :
    completeCoefficientRowCheck factorRow row0527 527 coefficients0527 = true := by
  have hlen : coefficients0527.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0527 oddDots0527
      641 527 0 coefficients0527 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0527_checked oddSum0527_checked hlen hs


end
end ErdosOverlap.Native6Grid
