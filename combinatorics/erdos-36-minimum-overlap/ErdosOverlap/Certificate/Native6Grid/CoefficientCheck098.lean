module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck098
public import ErdosOverlap.Certificate.Native6Grid.Coefficients12

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0784 :
    completeCoefficientRowCheck factorRow row0784 784 coefficients0784 = true := by
  have hlen : coefficients0784.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0784 oddDots0784
      641 784 0 coefficients0784 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0784_checked oddSum0784_checked hlen hs

theorem coefficientCheck0785 :
    completeCoefficientRowCheck factorRow row0785 785 coefficients0785 = true := by
  have hlen : coefficients0785.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0785 oddDots0785
      641 785 0 coefficients0785 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0785_checked oddSum0785_checked hlen hs

theorem coefficientCheck0786 :
    completeCoefficientRowCheck factorRow row0786 786 coefficients0786 = true := by
  have hlen : coefficients0786.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0786 oddDots0786
      641 786 0 coefficients0786 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0786_checked oddSum0786_checked hlen hs

theorem coefficientCheck0787 :
    completeCoefficientRowCheck factorRow row0787 787 coefficients0787 = true := by
  have hlen : coefficients0787.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0787 oddDots0787
      641 787 0 coefficients0787 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0787_checked oddSum0787_checked hlen hs

theorem coefficientCheck0788 :
    completeCoefficientRowCheck factorRow row0788 788 coefficients0788 = true := by
  have hlen : coefficients0788.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0788 oddDots0788
      641 788 0 coefficients0788 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0788_checked oddSum0788_checked hlen hs

theorem coefficientCheck0789 :
    completeCoefficientRowCheck factorRow row0789 789 coefficients0789 = true := by
  have hlen : coefficients0789.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0789 oddDots0789
      641 789 0 coefficients0789 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0789_checked oddSum0789_checked hlen hs

theorem coefficientCheck0790 :
    completeCoefficientRowCheck factorRow row0790 790 coefficients0790 = true := by
  have hlen : coefficients0790.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0790 oddDots0790
      641 790 0 coefficients0790 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0790_checked oddSum0790_checked hlen hs

theorem coefficientCheck0791 :
    completeCoefficientRowCheck factorRow row0791 791 coefficients0791 = true := by
  have hlen : coefficients0791.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0791 oddDots0791
      641 791 0 coefficients0791 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0791_checked oddSum0791_checked hlen hs


end
end ErdosOverlap.Native6Grid
