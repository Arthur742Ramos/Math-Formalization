module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck125
public import ErdosOverlap.Certificate.Native6Grid.Coefficients15

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck1000 :
    completeCoefficientRowCheck factorRow row1000 1000 coefficients1000 = true := by
  have hlen : coefficients1000.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1000 oddDots1000
      641 1000 0 coefficients1000 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1000_checked oddSum1000_checked hlen hs

theorem coefficientCheck1001 :
    completeCoefficientRowCheck factorRow row1001 1001 coefficients1001 = true := by
  have hlen : coefficients1001.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1001 oddDots1001
      641 1001 0 coefficients1001 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1001_checked oddSum1001_checked hlen hs

theorem coefficientCheck1002 :
    completeCoefficientRowCheck factorRow row1002 1002 coefficients1002 = true := by
  have hlen : coefficients1002.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1002 oddDots1002
      641 1002 0 coefficients1002 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1002_checked oddSum1002_checked hlen hs

theorem coefficientCheck1003 :
    completeCoefficientRowCheck factorRow row1003 1003 coefficients1003 = true := by
  have hlen : coefficients1003.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1003 oddDots1003
      641 1003 0 coefficients1003 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1003_checked oddSum1003_checked hlen hs

theorem coefficientCheck1004 :
    completeCoefficientRowCheck factorRow row1004 1004 coefficients1004 = true := by
  have hlen : coefficients1004.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1004 oddDots1004
      641 1004 0 coefficients1004 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1004_checked oddSum1004_checked hlen hs

theorem coefficientCheck1005 :
    completeCoefficientRowCheck factorRow row1005 1005 coefficients1005 = true := by
  have hlen : coefficients1005.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1005 oddDots1005
      641 1005 0 coefficients1005 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1005_checked oddSum1005_checked hlen hs

theorem coefficientCheck1006 :
    completeCoefficientRowCheck factorRow row1006 1006 coefficients1006 = true := by
  have hlen : coefficients1006.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1006 oddDots1006
      641 1006 0 coefficients1006 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1006_checked oddSum1006_checked hlen hs

theorem coefficientCheck1007 :
    completeCoefficientRowCheck factorRow row1007 1007 coefficients1007 = true := by
  have hlen : coefficients1007.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1007 oddDots1007
      641 1007 0 coefficients1007 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1007_checked oddSum1007_checked hlen hs


end
end ErdosOverlap.Native6Grid
