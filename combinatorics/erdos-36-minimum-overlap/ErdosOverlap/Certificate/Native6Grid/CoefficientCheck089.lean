module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck089
public import ErdosOverlap.Certificate.Native6Grid.Coefficients11

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0712 :
    completeCoefficientRowCheck factorRow row0712 712 coefficients0712 = true := by
  have hlen : coefficients0712.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0712 oddDots0712
      641 712 0 coefficients0712 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0712_checked oddSum0712_checked hlen hs

theorem coefficientCheck0713 :
    completeCoefficientRowCheck factorRow row0713 713 coefficients0713 = true := by
  have hlen : coefficients0713.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0713 oddDots0713
      641 713 0 coefficients0713 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0713_checked oddSum0713_checked hlen hs

theorem coefficientCheck0714 :
    completeCoefficientRowCheck factorRow row0714 714 coefficients0714 = true := by
  have hlen : coefficients0714.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0714 oddDots0714
      641 714 0 coefficients0714 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0714_checked oddSum0714_checked hlen hs

theorem coefficientCheck0715 :
    completeCoefficientRowCheck factorRow row0715 715 coefficients0715 = true := by
  have hlen : coefficients0715.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0715 oddDots0715
      641 715 0 coefficients0715 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0715_checked oddSum0715_checked hlen hs

theorem coefficientCheck0716 :
    completeCoefficientRowCheck factorRow row0716 716 coefficients0716 = true := by
  have hlen : coefficients0716.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0716 oddDots0716
      641 716 0 coefficients0716 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0716_checked oddSum0716_checked hlen hs

theorem coefficientCheck0717 :
    completeCoefficientRowCheck factorRow row0717 717 coefficients0717 = true := by
  have hlen : coefficients0717.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0717 oddDots0717
      641 717 0 coefficients0717 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0717_checked oddSum0717_checked hlen hs

theorem coefficientCheck0718 :
    completeCoefficientRowCheck factorRow row0718 718 coefficients0718 = true := by
  have hlen : coefficients0718.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0718 oddDots0718
      641 718 0 coefficients0718 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0718_checked oddSum0718_checked hlen hs

theorem coefficientCheck0719 :
    completeCoefficientRowCheck factorRow row0719 719 coefficients0719 = true := by
  have hlen : coefficients0719.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0719 oddDots0719
      641 719 0 coefficients0719 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0719_checked oddSum0719_checked hlen hs


end
end ErdosOverlap.Native6Grid
