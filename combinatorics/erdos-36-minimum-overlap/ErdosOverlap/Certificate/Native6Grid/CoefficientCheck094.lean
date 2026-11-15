module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck094
public import ErdosOverlap.Certificate.Native6Grid.Coefficients11

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0752 :
    completeCoefficientRowCheck factorRow row0752 752 coefficients0752 = true := by
  have hlen : coefficients0752.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0752 oddDots0752
      641 752 0 coefficients0752 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0752_checked oddSum0752_checked hlen hs

theorem coefficientCheck0753 :
    completeCoefficientRowCheck factorRow row0753 753 coefficients0753 = true := by
  have hlen : coefficients0753.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0753 oddDots0753
      641 753 0 coefficients0753 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0753_checked oddSum0753_checked hlen hs

theorem coefficientCheck0754 :
    completeCoefficientRowCheck factorRow row0754 754 coefficients0754 = true := by
  have hlen : coefficients0754.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0754 oddDots0754
      641 754 0 coefficients0754 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0754_checked oddSum0754_checked hlen hs

theorem coefficientCheck0755 :
    completeCoefficientRowCheck factorRow row0755 755 coefficients0755 = true := by
  have hlen : coefficients0755.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0755 oddDots0755
      641 755 0 coefficients0755 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0755_checked oddSum0755_checked hlen hs

theorem coefficientCheck0756 :
    completeCoefficientRowCheck factorRow row0756 756 coefficients0756 = true := by
  have hlen : coefficients0756.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0756 oddDots0756
      641 756 0 coefficients0756 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0756_checked oddSum0756_checked hlen hs

theorem coefficientCheck0757 :
    completeCoefficientRowCheck factorRow row0757 757 coefficients0757 = true := by
  have hlen : coefficients0757.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0757 oddDots0757
      641 757 0 coefficients0757 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0757_checked oddSum0757_checked hlen hs

theorem coefficientCheck0758 :
    completeCoefficientRowCheck factorRow row0758 758 coefficients0758 = true := by
  have hlen : coefficients0758.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0758 oddDots0758
      641 758 0 coefficients0758 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0758_checked oddSum0758_checked hlen hs

theorem coefficientCheck0759 :
    completeCoefficientRowCheck factorRow row0759 759 coefficients0759 = true := by
  have hlen : coefficients0759.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0759 oddDots0759
      641 759 0 coefficients0759 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0759_checked oddSum0759_checked hlen hs


end
end ErdosOverlap.Native6Grid
