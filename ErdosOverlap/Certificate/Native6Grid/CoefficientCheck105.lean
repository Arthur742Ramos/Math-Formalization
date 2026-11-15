module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck105
public import ErdosOverlap.Certificate.Native6Grid.Coefficients13

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0840 :
    completeCoefficientRowCheck factorRow row0840 840 coefficients0840 = true := by
  have hlen : coefficients0840.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0840 oddDots0840
      641 840 0 coefficients0840 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0840_checked oddSum0840_checked hlen hs

theorem coefficientCheck0841 :
    completeCoefficientRowCheck factorRow row0841 841 coefficients0841 = true := by
  have hlen : coefficients0841.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0841 oddDots0841
      641 841 0 coefficients0841 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0841_checked oddSum0841_checked hlen hs

theorem coefficientCheck0842 :
    completeCoefficientRowCheck factorRow row0842 842 coefficients0842 = true := by
  have hlen : coefficients0842.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0842 oddDots0842
      641 842 0 coefficients0842 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0842_checked oddSum0842_checked hlen hs

theorem coefficientCheck0843 :
    completeCoefficientRowCheck factorRow row0843 843 coefficients0843 = true := by
  have hlen : coefficients0843.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0843 oddDots0843
      641 843 0 coefficients0843 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0843_checked oddSum0843_checked hlen hs

theorem coefficientCheck0844 :
    completeCoefficientRowCheck factorRow row0844 844 coefficients0844 = true := by
  have hlen : coefficients0844.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0844 oddDots0844
      641 844 0 coefficients0844 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0844_checked oddSum0844_checked hlen hs

theorem coefficientCheck0845 :
    completeCoefficientRowCheck factorRow row0845 845 coefficients0845 = true := by
  have hlen : coefficients0845.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0845 oddDots0845
      641 845 0 coefficients0845 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0845_checked oddSum0845_checked hlen hs

theorem coefficientCheck0846 :
    completeCoefficientRowCheck factorRow row0846 846 coefficients0846 = true := by
  have hlen : coefficients0846.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0846 oddDots0846
      641 846 0 coefficients0846 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0846_checked oddSum0846_checked hlen hs

theorem coefficientCheck0847 :
    completeCoefficientRowCheck factorRow row0847 847 coefficients0847 = true := by
  have hlen : coefficients0847.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0847 oddDots0847
      641 847 0 coefficients0847 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0847_checked oddSum0847_checked hlen hs


end
end ErdosOverlap.Native6Grid
