module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck126
public import ErdosOverlap.Certificate.Native6Grid.Coefficients15

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck1008 :
    completeCoefficientRowCheck factorRow row1008 1008 coefficients1008 = true := by
  have hlen : coefficients1008.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1008 oddDots1008
      641 1008 0 coefficients1008 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1008_checked oddSum1008_checked hlen hs

theorem coefficientCheck1009 :
    completeCoefficientRowCheck factorRow row1009 1009 coefficients1009 = true := by
  have hlen : coefficients1009.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1009 oddDots1009
      641 1009 0 coefficients1009 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1009_checked oddSum1009_checked hlen hs

theorem coefficientCheck1010 :
    completeCoefficientRowCheck factorRow row1010 1010 coefficients1010 = true := by
  have hlen : coefficients1010.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1010 oddDots1010
      641 1010 0 coefficients1010 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1010_checked oddSum1010_checked hlen hs

theorem coefficientCheck1011 :
    completeCoefficientRowCheck factorRow row1011 1011 coefficients1011 = true := by
  have hlen : coefficients1011.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1011 oddDots1011
      641 1011 0 coefficients1011 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1011_checked oddSum1011_checked hlen hs

theorem coefficientCheck1012 :
    completeCoefficientRowCheck factorRow row1012 1012 coefficients1012 = true := by
  have hlen : coefficients1012.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1012 oddDots1012
      641 1012 0 coefficients1012 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1012_checked oddSum1012_checked hlen hs

theorem coefficientCheck1013 :
    completeCoefficientRowCheck factorRow row1013 1013 coefficients1013 = true := by
  have hlen : coefficients1013.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1013 oddDots1013
      641 1013 0 coefficients1013 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1013_checked oddSum1013_checked hlen hs

theorem coefficientCheck1014 :
    completeCoefficientRowCheck factorRow row1014 1014 coefficients1014 = true := by
  have hlen : coefficients1014.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1014 oddDots1014
      641 1014 0 coefficients1014 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1014_checked oddSum1014_checked hlen hs

theorem coefficientCheck1015 :
    completeCoefficientRowCheck factorRow row1015 1015 coefficients1015 = true := by
  have hlen : coefficients1015.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1015 oddDots1015
      641 1015 0 coefficients1015 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1015_checked oddSum1015_checked hlen hs


end
end ErdosOverlap.Native6Grid
