module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck081
public import ErdosOverlap.Certificate.Native6Grid.Coefficients10

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0648 :
    completeCoefficientRowCheck factorRow row0648 648 coefficients0648 = true := by
  have hlen : coefficients0648.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0648 oddDots0648
      641 648 0 coefficients0648 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0648_checked oddSum0648_checked hlen hs

theorem coefficientCheck0649 :
    completeCoefficientRowCheck factorRow row0649 649 coefficients0649 = true := by
  have hlen : coefficients0649.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0649 oddDots0649
      641 649 0 coefficients0649 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0649_checked oddSum0649_checked hlen hs

theorem coefficientCheck0650 :
    completeCoefficientRowCheck factorRow row0650 650 coefficients0650 = true := by
  have hlen : coefficients0650.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0650 oddDots0650
      641 650 0 coefficients0650 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0650_checked oddSum0650_checked hlen hs

theorem coefficientCheck0651 :
    completeCoefficientRowCheck factorRow row0651 651 coefficients0651 = true := by
  have hlen : coefficients0651.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0651 oddDots0651
      641 651 0 coefficients0651 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0651_checked oddSum0651_checked hlen hs

theorem coefficientCheck0652 :
    completeCoefficientRowCheck factorRow row0652 652 coefficients0652 = true := by
  have hlen : coefficients0652.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0652 oddDots0652
      641 652 0 coefficients0652 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0652_checked oddSum0652_checked hlen hs

theorem coefficientCheck0653 :
    completeCoefficientRowCheck factorRow row0653 653 coefficients0653 = true := by
  have hlen : coefficients0653.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0653 oddDots0653
      641 653 0 coefficients0653 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0653_checked oddSum0653_checked hlen hs

theorem coefficientCheck0654 :
    completeCoefficientRowCheck factorRow row0654 654 coefficients0654 = true := by
  have hlen : coefficients0654.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0654 oddDots0654
      641 654 0 coefficients0654 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0654_checked oddSum0654_checked hlen hs

theorem coefficientCheck0655 :
    completeCoefficientRowCheck factorRow row0655 655 coefficients0655 = true := by
  have hlen : coefficients0655.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0655 oddDots0655
      641 655 0 coefficients0655 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0655_checked oddSum0655_checked hlen hs


end
end ErdosOverlap.Native6Grid
