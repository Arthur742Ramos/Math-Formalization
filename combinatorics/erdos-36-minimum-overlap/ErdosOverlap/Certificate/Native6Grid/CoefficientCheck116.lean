module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck116
public import ErdosOverlap.Certificate.Native6Grid.Coefficients14

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0928 :
    completeCoefficientRowCheck factorRow row0928 928 coefficients0928 = true := by
  have hlen : coefficients0928.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0928 oddDots0928
      641 928 0 coefficients0928 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0928_checked oddSum0928_checked hlen hs

theorem coefficientCheck0929 :
    completeCoefficientRowCheck factorRow row0929 929 coefficients0929 = true := by
  have hlen : coefficients0929.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0929 oddDots0929
      641 929 0 coefficients0929 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0929_checked oddSum0929_checked hlen hs

theorem coefficientCheck0930 :
    completeCoefficientRowCheck factorRow row0930 930 coefficients0930 = true := by
  have hlen : coefficients0930.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0930 oddDots0930
      641 930 0 coefficients0930 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0930_checked oddSum0930_checked hlen hs

theorem coefficientCheck0931 :
    completeCoefficientRowCheck factorRow row0931 931 coefficients0931 = true := by
  have hlen : coefficients0931.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0931 oddDots0931
      641 931 0 coefficients0931 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0931_checked oddSum0931_checked hlen hs

theorem coefficientCheck0932 :
    completeCoefficientRowCheck factorRow row0932 932 coefficients0932 = true := by
  have hlen : coefficients0932.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0932 oddDots0932
      641 932 0 coefficients0932 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0932_checked oddSum0932_checked hlen hs

theorem coefficientCheck0933 :
    completeCoefficientRowCheck factorRow row0933 933 coefficients0933 = true := by
  have hlen : coefficients0933.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0933 oddDots0933
      641 933 0 coefficients0933 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0933_checked oddSum0933_checked hlen hs

theorem coefficientCheck0934 :
    completeCoefficientRowCheck factorRow row0934 934 coefficients0934 = true := by
  have hlen : coefficients0934.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0934 oddDots0934
      641 934 0 coefficients0934 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0934_checked oddSum0934_checked hlen hs

theorem coefficientCheck0935 :
    completeCoefficientRowCheck factorRow row0935 935 coefficients0935 = true := by
  have hlen : coefficients0935.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0935 oddDots0935
      641 935 0 coefficients0935 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0935_checked oddSum0935_checked hlen hs


end
end ErdosOverlap.Native6Grid
