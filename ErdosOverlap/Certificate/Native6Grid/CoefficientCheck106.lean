module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck106
public import ErdosOverlap.Certificate.Native6Grid.Coefficients13

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0848 :
    completeCoefficientRowCheck factorRow row0848 848 coefficients0848 = true := by
  have hlen : coefficients0848.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0848 oddDots0848
      641 848 0 coefficients0848 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0848_checked oddSum0848_checked hlen hs

theorem coefficientCheck0849 :
    completeCoefficientRowCheck factorRow row0849 849 coefficients0849 = true := by
  have hlen : coefficients0849.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0849 oddDots0849
      641 849 0 coefficients0849 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0849_checked oddSum0849_checked hlen hs

theorem coefficientCheck0850 :
    completeCoefficientRowCheck factorRow row0850 850 coefficients0850 = true := by
  have hlen : coefficients0850.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0850 oddDots0850
      641 850 0 coefficients0850 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0850_checked oddSum0850_checked hlen hs

theorem coefficientCheck0851 :
    completeCoefficientRowCheck factorRow row0851 851 coefficients0851 = true := by
  have hlen : coefficients0851.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0851 oddDots0851
      641 851 0 coefficients0851 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0851_checked oddSum0851_checked hlen hs

theorem coefficientCheck0852 :
    completeCoefficientRowCheck factorRow row0852 852 coefficients0852 = true := by
  have hlen : coefficients0852.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0852 oddDots0852
      641 852 0 coefficients0852 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0852_checked oddSum0852_checked hlen hs

theorem coefficientCheck0853 :
    completeCoefficientRowCheck factorRow row0853 853 coefficients0853 = true := by
  have hlen : coefficients0853.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0853 oddDots0853
      641 853 0 coefficients0853 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0853_checked oddSum0853_checked hlen hs

theorem coefficientCheck0854 :
    completeCoefficientRowCheck factorRow row0854 854 coefficients0854 = true := by
  have hlen : coefficients0854.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0854 oddDots0854
      641 854 0 coefficients0854 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0854_checked oddSum0854_checked hlen hs

theorem coefficientCheck0855 :
    completeCoefficientRowCheck factorRow row0855 855 coefficients0855 = true := by
  have hlen : coefficients0855.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0855 oddDots0855
      641 855 0 coefficients0855 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0855_checked oddSum0855_checked hlen hs


end
end ErdosOverlap.Native6Grid
