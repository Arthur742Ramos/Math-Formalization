module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck114
public import ErdosOverlap.Certificate.Native6Grid.Coefficients14

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0912 :
    completeCoefficientRowCheck factorRow row0912 912 coefficients0912 = true := by
  have hlen : coefficients0912.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0912 oddDots0912
      641 912 0 coefficients0912 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0912_checked oddSum0912_checked hlen hs

theorem coefficientCheck0913 :
    completeCoefficientRowCheck factorRow row0913 913 coefficients0913 = true := by
  have hlen : coefficients0913.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0913 oddDots0913
      641 913 0 coefficients0913 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0913_checked oddSum0913_checked hlen hs

theorem coefficientCheck0914 :
    completeCoefficientRowCheck factorRow row0914 914 coefficients0914 = true := by
  have hlen : coefficients0914.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0914 oddDots0914
      641 914 0 coefficients0914 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0914_checked oddSum0914_checked hlen hs

theorem coefficientCheck0915 :
    completeCoefficientRowCheck factorRow row0915 915 coefficients0915 = true := by
  have hlen : coefficients0915.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0915 oddDots0915
      641 915 0 coefficients0915 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0915_checked oddSum0915_checked hlen hs

theorem coefficientCheck0916 :
    completeCoefficientRowCheck factorRow row0916 916 coefficients0916 = true := by
  have hlen : coefficients0916.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0916 oddDots0916
      641 916 0 coefficients0916 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0916_checked oddSum0916_checked hlen hs

theorem coefficientCheck0917 :
    completeCoefficientRowCheck factorRow row0917 917 coefficients0917 = true := by
  have hlen : coefficients0917.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0917 oddDots0917
      641 917 0 coefficients0917 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0917_checked oddSum0917_checked hlen hs

theorem coefficientCheck0918 :
    completeCoefficientRowCheck factorRow row0918 918 coefficients0918 = true := by
  have hlen : coefficients0918.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0918 oddDots0918
      641 918 0 coefficients0918 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0918_checked oddSum0918_checked hlen hs

theorem coefficientCheck0919 :
    completeCoefficientRowCheck factorRow row0919 919 coefficients0919 = true := by
  have hlen : coefficients0919.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0919 oddDots0919
      641 919 0 coefficients0919 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0919_checked oddSum0919_checked hlen hs


end
end ErdosOverlap.Native6Grid
