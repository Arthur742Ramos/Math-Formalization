module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck074
public import ErdosOverlap.Certificate.Native6Grid.Coefficients09

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0592 :
    completeCoefficientRowCheck factorRow row0592 592 coefficients0592 = true := by
  have hlen : coefficients0592.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0592 oddDots0592
      641 592 0 coefficients0592 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0592_checked oddSum0592_checked hlen hs

theorem coefficientCheck0593 :
    completeCoefficientRowCheck factorRow row0593 593 coefficients0593 = true := by
  have hlen : coefficients0593.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0593 oddDots0593
      641 593 0 coefficients0593 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0593_checked oddSum0593_checked hlen hs

theorem coefficientCheck0594 :
    completeCoefficientRowCheck factorRow row0594 594 coefficients0594 = true := by
  have hlen : coefficients0594.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0594 oddDots0594
      641 594 0 coefficients0594 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0594_checked oddSum0594_checked hlen hs

theorem coefficientCheck0595 :
    completeCoefficientRowCheck factorRow row0595 595 coefficients0595 = true := by
  have hlen : coefficients0595.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0595 oddDots0595
      641 595 0 coefficients0595 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0595_checked oddSum0595_checked hlen hs

theorem coefficientCheck0596 :
    completeCoefficientRowCheck factorRow row0596 596 coefficients0596 = true := by
  have hlen : coefficients0596.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0596 oddDots0596
      641 596 0 coefficients0596 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0596_checked oddSum0596_checked hlen hs

theorem coefficientCheck0597 :
    completeCoefficientRowCheck factorRow row0597 597 coefficients0597 = true := by
  have hlen : coefficients0597.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0597 oddDots0597
      641 597 0 coefficients0597 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0597_checked oddSum0597_checked hlen hs

theorem coefficientCheck0598 :
    completeCoefficientRowCheck factorRow row0598 598 coefficients0598 = true := by
  have hlen : coefficients0598.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0598 oddDots0598
      641 598 0 coefficients0598 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0598_checked oddSum0598_checked hlen hs

theorem coefficientCheck0599 :
    completeCoefficientRowCheck factorRow row0599 599 coefficients0599 = true := by
  have hlen : coefficients0599.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0599 oddDots0599
      641 599 0 coefficients0599 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0599_checked oddSum0599_checked hlen hs


end
end ErdosOverlap.Native6Grid
