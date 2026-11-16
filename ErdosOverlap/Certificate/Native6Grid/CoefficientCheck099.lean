module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck099
public import ErdosOverlap.Certificate.Native6Grid.Coefficients12

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0792 :
    completeCoefficientRowCheck factorRow row0792 792 coefficients0792 = true := by
  have hlen : coefficients0792.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0792 oddDots0792
      641 792 0 coefficients0792 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0792_checked oddSum0792_checked hlen hs

theorem coefficientCheck0793 :
    completeCoefficientRowCheck factorRow row0793 793 coefficients0793 = true := by
  have hlen : coefficients0793.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0793 oddDots0793
      641 793 0 coefficients0793 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0793_checked oddSum0793_checked hlen hs

theorem coefficientCheck0794 :
    completeCoefficientRowCheck factorRow row0794 794 coefficients0794 = true := by
  have hlen : coefficients0794.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0794 oddDots0794
      641 794 0 coefficients0794 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0794_checked oddSum0794_checked hlen hs

theorem coefficientCheck0795 :
    completeCoefficientRowCheck factorRow row0795 795 coefficients0795 = true := by
  have hlen : coefficients0795.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0795 oddDots0795
      641 795 0 coefficients0795 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0795_checked oddSum0795_checked hlen hs

theorem coefficientCheck0796 :
    completeCoefficientRowCheck factorRow row0796 796 coefficients0796 = true := by
  have hlen : coefficients0796.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0796 oddDots0796
      641 796 0 coefficients0796 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0796_checked oddSum0796_checked hlen hs

theorem coefficientCheck0797 :
    completeCoefficientRowCheck factorRow row0797 797 coefficients0797 = true := by
  have hlen : coefficients0797.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0797 oddDots0797
      641 797 0 coefficients0797 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0797_checked oddSum0797_checked hlen hs

theorem coefficientCheck0798 :
    completeCoefficientRowCheck factorRow row0798 798 coefficients0798 = true := by
  have hlen : coefficients0798.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0798 oddDots0798
      641 798 0 coefficients0798 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0798_checked oddSum0798_checked hlen hs

theorem coefficientCheck0799 :
    completeCoefficientRowCheck factorRow row0799 799 coefficients0799 = true := by
  have hlen : coefficients0799.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0799 oddDots0799
      641 799 0 coefficients0799 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0799_checked oddSum0799_checked hlen hs


end
end ErdosOverlap.Native6Grid
