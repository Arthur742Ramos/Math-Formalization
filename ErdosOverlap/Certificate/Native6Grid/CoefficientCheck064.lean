module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck064
public import ErdosOverlap.Certificate.Native6Grid.Coefficients08

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0512 :
    completeCoefficientRowCheck factorRow row0512 512 coefficients0512 = true := by
  have hlen : coefficients0512.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0512 oddDots0512
      641 512 0 coefficients0512 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0512_checked oddSum0512_checked hlen hs

theorem coefficientCheck0513 :
    completeCoefficientRowCheck factorRow row0513 513 coefficients0513 = true := by
  have hlen : coefficients0513.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0513 oddDots0513
      641 513 0 coefficients0513 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0513_checked oddSum0513_checked hlen hs

theorem coefficientCheck0514 :
    completeCoefficientRowCheck factorRow row0514 514 coefficients0514 = true := by
  have hlen : coefficients0514.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0514 oddDots0514
      641 514 0 coefficients0514 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0514_checked oddSum0514_checked hlen hs

theorem coefficientCheck0515 :
    completeCoefficientRowCheck factorRow row0515 515 coefficients0515 = true := by
  have hlen : coefficients0515.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0515 oddDots0515
      641 515 0 coefficients0515 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0515_checked oddSum0515_checked hlen hs

theorem coefficientCheck0516 :
    completeCoefficientRowCheck factorRow row0516 516 coefficients0516 = true := by
  have hlen : coefficients0516.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0516 oddDots0516
      641 516 0 coefficients0516 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0516_checked oddSum0516_checked hlen hs

theorem coefficientCheck0517 :
    completeCoefficientRowCheck factorRow row0517 517 coefficients0517 = true := by
  have hlen : coefficients0517.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0517 oddDots0517
      641 517 0 coefficients0517 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0517_checked oddSum0517_checked hlen hs

theorem coefficientCheck0518 :
    completeCoefficientRowCheck factorRow row0518 518 coefficients0518 = true := by
  have hlen : coefficients0518.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0518 oddDots0518
      641 518 0 coefficients0518 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0518_checked oddSum0518_checked hlen hs

theorem coefficientCheck0519 :
    completeCoefficientRowCheck factorRow row0519 519 coefficients0519 = true := by
  have hlen : coefficients0519.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0519 oddDots0519
      641 519 0 coefficients0519 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0519_checked oddSum0519_checked hlen hs


end
end ErdosOverlap.Native6Grid
