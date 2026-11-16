module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck078
public import ErdosOverlap.Certificate.Native6Grid.Coefficients09

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0624 :
    completeCoefficientRowCheck factorRow row0624 624 coefficients0624 = true := by
  have hlen : coefficients0624.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0624 oddDots0624
      641 624 0 coefficients0624 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0624_checked oddSum0624_checked hlen hs

theorem coefficientCheck0625 :
    completeCoefficientRowCheck factorRow row0625 625 coefficients0625 = true := by
  have hlen : coefficients0625.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0625 oddDots0625
      641 625 0 coefficients0625 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0625_checked oddSum0625_checked hlen hs

theorem coefficientCheck0626 :
    completeCoefficientRowCheck factorRow row0626 626 coefficients0626 = true := by
  have hlen : coefficients0626.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0626 oddDots0626
      641 626 0 coefficients0626 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0626_checked oddSum0626_checked hlen hs

theorem coefficientCheck0627 :
    completeCoefficientRowCheck factorRow row0627 627 coefficients0627 = true := by
  have hlen : coefficients0627.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0627 oddDots0627
      641 627 0 coefficients0627 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0627_checked oddSum0627_checked hlen hs

theorem coefficientCheck0628 :
    completeCoefficientRowCheck factorRow row0628 628 coefficients0628 = true := by
  have hlen : coefficients0628.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0628 oddDots0628
      641 628 0 coefficients0628 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0628_checked oddSum0628_checked hlen hs

theorem coefficientCheck0629 :
    completeCoefficientRowCheck factorRow row0629 629 coefficients0629 = true := by
  have hlen : coefficients0629.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0629 oddDots0629
      641 629 0 coefficients0629 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0629_checked oddSum0629_checked hlen hs

theorem coefficientCheck0630 :
    completeCoefficientRowCheck factorRow row0630 630 coefficients0630 = true := by
  have hlen : coefficients0630.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0630 oddDots0630
      641 630 0 coefficients0630 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0630_checked oddSum0630_checked hlen hs

theorem coefficientCheck0631 :
    completeCoefficientRowCheck factorRow row0631 631 coefficients0631 = true := by
  have hlen : coefficients0631.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0631 oddDots0631
      641 631 0 coefficients0631 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0631_checked oddSum0631_checked hlen hs


end
end ErdosOverlap.Native6Grid
