module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck096
public import ErdosOverlap.Certificate.Native6Grid.Coefficients12

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0768 :
    completeCoefficientRowCheck factorRow row0768 768 coefficients0768 = true := by
  have hlen : coefficients0768.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0768 oddDots0768
      641 768 0 coefficients0768 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0768_checked oddSum0768_checked hlen hs

theorem coefficientCheck0769 :
    completeCoefficientRowCheck factorRow row0769 769 coefficients0769 = true := by
  have hlen : coefficients0769.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0769 oddDots0769
      641 769 0 coefficients0769 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0769_checked oddSum0769_checked hlen hs

theorem coefficientCheck0770 :
    completeCoefficientRowCheck factorRow row0770 770 coefficients0770 = true := by
  have hlen : coefficients0770.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0770 oddDots0770
      641 770 0 coefficients0770 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0770_checked oddSum0770_checked hlen hs

theorem coefficientCheck0771 :
    completeCoefficientRowCheck factorRow row0771 771 coefficients0771 = true := by
  have hlen : coefficients0771.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0771 oddDots0771
      641 771 0 coefficients0771 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0771_checked oddSum0771_checked hlen hs

theorem coefficientCheck0772 :
    completeCoefficientRowCheck factorRow row0772 772 coefficients0772 = true := by
  have hlen : coefficients0772.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0772 oddDots0772
      641 772 0 coefficients0772 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0772_checked oddSum0772_checked hlen hs

theorem coefficientCheck0773 :
    completeCoefficientRowCheck factorRow row0773 773 coefficients0773 = true := by
  have hlen : coefficients0773.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0773 oddDots0773
      641 773 0 coefficients0773 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0773_checked oddSum0773_checked hlen hs

theorem coefficientCheck0774 :
    completeCoefficientRowCheck factorRow row0774 774 coefficients0774 = true := by
  have hlen : coefficients0774.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0774 oddDots0774
      641 774 0 coefficients0774 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0774_checked oddSum0774_checked hlen hs

theorem coefficientCheck0775 :
    completeCoefficientRowCheck factorRow row0775 775 coefficients0775 = true := by
  have hlen : coefficients0775.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0775 oddDots0775
      641 775 0 coefficients0775 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0775_checked oddSum0775_checked hlen hs


end
end ErdosOverlap.Native6Grid
