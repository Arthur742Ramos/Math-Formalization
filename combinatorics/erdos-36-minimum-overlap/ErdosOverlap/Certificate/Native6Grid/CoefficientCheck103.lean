module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck103
public import ErdosOverlap.Certificate.Native6Grid.Coefficients12

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0824 :
    completeCoefficientRowCheck factorRow row0824 824 coefficients0824 = true := by
  have hlen : coefficients0824.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0824 oddDots0824
      641 824 0 coefficients0824 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0824_checked oddSum0824_checked hlen hs

theorem coefficientCheck0825 :
    completeCoefficientRowCheck factorRow row0825 825 coefficients0825 = true := by
  have hlen : coefficients0825.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0825 oddDots0825
      641 825 0 coefficients0825 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0825_checked oddSum0825_checked hlen hs

theorem coefficientCheck0826 :
    completeCoefficientRowCheck factorRow row0826 826 coefficients0826 = true := by
  have hlen : coefficients0826.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0826 oddDots0826
      641 826 0 coefficients0826 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0826_checked oddSum0826_checked hlen hs

theorem coefficientCheck0827 :
    completeCoefficientRowCheck factorRow row0827 827 coefficients0827 = true := by
  have hlen : coefficients0827.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0827 oddDots0827
      641 827 0 coefficients0827 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0827_checked oddSum0827_checked hlen hs

theorem coefficientCheck0828 :
    completeCoefficientRowCheck factorRow row0828 828 coefficients0828 = true := by
  have hlen : coefficients0828.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0828 oddDots0828
      641 828 0 coefficients0828 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0828_checked oddSum0828_checked hlen hs

theorem coefficientCheck0829 :
    completeCoefficientRowCheck factorRow row0829 829 coefficients0829 = true := by
  have hlen : coefficients0829.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0829 oddDots0829
      641 829 0 coefficients0829 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0829_checked oddSum0829_checked hlen hs

theorem coefficientCheck0830 :
    completeCoefficientRowCheck factorRow row0830 830 coefficients0830 = true := by
  have hlen : coefficients0830.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0830 oddDots0830
      641 830 0 coefficients0830 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0830_checked oddSum0830_checked hlen hs

theorem coefficientCheck0831 :
    completeCoefficientRowCheck factorRow row0831 831 coefficients0831 = true := by
  have hlen : coefficients0831.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0831 oddDots0831
      641 831 0 coefficients0831 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0831_checked oddSum0831_checked hlen hs


end
end ErdosOverlap.Native6Grid
