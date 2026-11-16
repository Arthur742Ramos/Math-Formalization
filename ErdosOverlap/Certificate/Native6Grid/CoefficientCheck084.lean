module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck084
public import ErdosOverlap.Certificate.Native6Grid.Coefficients10

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0672 :
    completeCoefficientRowCheck factorRow row0672 672 coefficients0672 = true := by
  have hlen : coefficients0672.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0672 oddDots0672
      641 672 0 coefficients0672 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0672_checked oddSum0672_checked hlen hs

theorem coefficientCheck0673 :
    completeCoefficientRowCheck factorRow row0673 673 coefficients0673 = true := by
  have hlen : coefficients0673.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0673 oddDots0673
      641 673 0 coefficients0673 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0673_checked oddSum0673_checked hlen hs

theorem coefficientCheck0674 :
    completeCoefficientRowCheck factorRow row0674 674 coefficients0674 = true := by
  have hlen : coefficients0674.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0674 oddDots0674
      641 674 0 coefficients0674 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0674_checked oddSum0674_checked hlen hs

theorem coefficientCheck0675 :
    completeCoefficientRowCheck factorRow row0675 675 coefficients0675 = true := by
  have hlen : coefficients0675.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0675 oddDots0675
      641 675 0 coefficients0675 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0675_checked oddSum0675_checked hlen hs

theorem coefficientCheck0676 :
    completeCoefficientRowCheck factorRow row0676 676 coefficients0676 = true := by
  have hlen : coefficients0676.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0676 oddDots0676
      641 676 0 coefficients0676 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0676_checked oddSum0676_checked hlen hs

theorem coefficientCheck0677 :
    completeCoefficientRowCheck factorRow row0677 677 coefficients0677 = true := by
  have hlen : coefficients0677.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0677 oddDots0677
      641 677 0 coefficients0677 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0677_checked oddSum0677_checked hlen hs

theorem coefficientCheck0678 :
    completeCoefficientRowCheck factorRow row0678 678 coefficients0678 = true := by
  have hlen : coefficients0678.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0678 oddDots0678
      641 678 0 coefficients0678 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0678_checked oddSum0678_checked hlen hs

theorem coefficientCheck0679 :
    completeCoefficientRowCheck factorRow row0679 679 coefficients0679 = true := by
  have hlen : coefficients0679.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0679 oddDots0679
      641 679 0 coefficients0679 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0679_checked oddSum0679_checked hlen hs


end
end ErdosOverlap.Native6Grid
