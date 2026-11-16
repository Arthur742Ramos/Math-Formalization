module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck102
public import ErdosOverlap.Certificate.Native6Grid.Coefficients12

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0816 :
    completeCoefficientRowCheck factorRow row0816 816 coefficients0816 = true := by
  have hlen : coefficients0816.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0816 oddDots0816
      641 816 0 coefficients0816 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0816_checked oddSum0816_checked hlen hs

theorem coefficientCheck0817 :
    completeCoefficientRowCheck factorRow row0817 817 coefficients0817 = true := by
  have hlen : coefficients0817.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0817 oddDots0817
      641 817 0 coefficients0817 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0817_checked oddSum0817_checked hlen hs

theorem coefficientCheck0818 :
    completeCoefficientRowCheck factorRow row0818 818 coefficients0818 = true := by
  have hlen : coefficients0818.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0818 oddDots0818
      641 818 0 coefficients0818 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0818_checked oddSum0818_checked hlen hs

theorem coefficientCheck0819 :
    completeCoefficientRowCheck factorRow row0819 819 coefficients0819 = true := by
  have hlen : coefficients0819.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0819 oddDots0819
      641 819 0 coefficients0819 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0819_checked oddSum0819_checked hlen hs

theorem coefficientCheck0820 :
    completeCoefficientRowCheck factorRow row0820 820 coefficients0820 = true := by
  have hlen : coefficients0820.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0820 oddDots0820
      641 820 0 coefficients0820 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0820_checked oddSum0820_checked hlen hs

theorem coefficientCheck0821 :
    completeCoefficientRowCheck factorRow row0821 821 coefficients0821 = true := by
  have hlen : coefficients0821.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0821 oddDots0821
      641 821 0 coefficients0821 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0821_checked oddSum0821_checked hlen hs

theorem coefficientCheck0822 :
    completeCoefficientRowCheck factorRow row0822 822 coefficients0822 = true := by
  have hlen : coefficients0822.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0822 oddDots0822
      641 822 0 coefficients0822 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0822_checked oddSum0822_checked hlen hs

theorem coefficientCheck0823 :
    completeCoefficientRowCheck factorRow row0823 823 coefficients0823 = true := by
  have hlen : coefficients0823.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0823 oddDots0823
      641 823 0 coefficients0823 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0823_checked oddSum0823_checked hlen hs


end
end ErdosOverlap.Native6Grid
