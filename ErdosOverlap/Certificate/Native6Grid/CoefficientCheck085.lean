module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck085
public import ErdosOverlap.Certificate.Native6Grid.Coefficients10

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0680 :
    completeCoefficientRowCheck factorRow row0680 680 coefficients0680 = true := by
  have hlen : coefficients0680.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0680 oddDots0680
      641 680 0 coefficients0680 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0680_checked oddSum0680_checked hlen hs

theorem coefficientCheck0681 :
    completeCoefficientRowCheck factorRow row0681 681 coefficients0681 = true := by
  have hlen : coefficients0681.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0681 oddDots0681
      641 681 0 coefficients0681 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0681_checked oddSum0681_checked hlen hs

theorem coefficientCheck0682 :
    completeCoefficientRowCheck factorRow row0682 682 coefficients0682 = true := by
  have hlen : coefficients0682.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0682 oddDots0682
      641 682 0 coefficients0682 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0682_checked oddSum0682_checked hlen hs

theorem coefficientCheck0683 :
    completeCoefficientRowCheck factorRow row0683 683 coefficients0683 = true := by
  have hlen : coefficients0683.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0683 oddDots0683
      641 683 0 coefficients0683 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0683_checked oddSum0683_checked hlen hs

theorem coefficientCheck0684 :
    completeCoefficientRowCheck factorRow row0684 684 coefficients0684 = true := by
  have hlen : coefficients0684.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0684 oddDots0684
      641 684 0 coefficients0684 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0684_checked oddSum0684_checked hlen hs

theorem coefficientCheck0685 :
    completeCoefficientRowCheck factorRow row0685 685 coefficients0685 = true := by
  have hlen : coefficients0685.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0685 oddDots0685
      641 685 0 coefficients0685 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0685_checked oddSum0685_checked hlen hs

theorem coefficientCheck0686 :
    completeCoefficientRowCheck factorRow row0686 686 coefficients0686 = true := by
  have hlen : coefficients0686.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0686 oddDots0686
      641 686 0 coefficients0686 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0686_checked oddSum0686_checked hlen hs

theorem coefficientCheck0687 :
    completeCoefficientRowCheck factorRow row0687 687 coefficients0687 = true := by
  have hlen : coefficients0687.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0687 oddDots0687
      641 687 0 coefficients0687 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0687_checked oddSum0687_checked hlen hs


end
end ErdosOverlap.Native6Grid
