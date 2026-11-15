module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck087
public import ErdosOverlap.Certificate.Native6Grid.Coefficients10

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0696 :
    completeCoefficientRowCheck factorRow row0696 696 coefficients0696 = true := by
  have hlen : coefficients0696.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0696 oddDots0696
      641 696 0 coefficients0696 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0696_checked oddSum0696_checked hlen hs

theorem coefficientCheck0697 :
    completeCoefficientRowCheck factorRow row0697 697 coefficients0697 = true := by
  have hlen : coefficients0697.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0697 oddDots0697
      641 697 0 coefficients0697 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0697_checked oddSum0697_checked hlen hs

theorem coefficientCheck0698 :
    completeCoefficientRowCheck factorRow row0698 698 coefficients0698 = true := by
  have hlen : coefficients0698.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0698 oddDots0698
      641 698 0 coefficients0698 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0698_checked oddSum0698_checked hlen hs

theorem coefficientCheck0699 :
    completeCoefficientRowCheck factorRow row0699 699 coefficients0699 = true := by
  have hlen : coefficients0699.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0699 oddDots0699
      641 699 0 coefficients0699 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0699_checked oddSum0699_checked hlen hs

theorem coefficientCheck0700 :
    completeCoefficientRowCheck factorRow row0700 700 coefficients0700 = true := by
  have hlen : coefficients0700.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0700 oddDots0700
      641 700 0 coefficients0700 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0700_checked oddSum0700_checked hlen hs

theorem coefficientCheck0701 :
    completeCoefficientRowCheck factorRow row0701 701 coefficients0701 = true := by
  have hlen : coefficients0701.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0701 oddDots0701
      641 701 0 coefficients0701 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0701_checked oddSum0701_checked hlen hs

theorem coefficientCheck0702 :
    completeCoefficientRowCheck factorRow row0702 702 coefficients0702 = true := by
  have hlen : coefficients0702.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0702 oddDots0702
      641 702 0 coefficients0702 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0702_checked oddSum0702_checked hlen hs

theorem coefficientCheck0703 :
    completeCoefficientRowCheck factorRow row0703 703 coefficients0703 = true := by
  have hlen : coefficients0703.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0703 oddDots0703
      641 703 0 coefficients0703 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0703_checked oddSum0703_checked hlen hs


end
end ErdosOverlap.Native6Grid
