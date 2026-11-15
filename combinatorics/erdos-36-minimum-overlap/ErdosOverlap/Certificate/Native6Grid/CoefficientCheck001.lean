module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck001
public import ErdosOverlap.Certificate.Native6Grid.Coefficients00

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0008 :
    completeCoefficientRowCheck factorRow row0008 8 coefficients0008 = true := by
  have hlen : coefficients0008.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0008 oddDots0008
      641 8 0 coefficients0008 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0008_checked oddSum0008_checked hlen hs

theorem coefficientCheck0009 :
    completeCoefficientRowCheck factorRow row0009 9 coefficients0009 = true := by
  have hlen : coefficients0009.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0009 oddDots0009
      641 9 0 coefficients0009 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0009_checked oddSum0009_checked hlen hs

theorem coefficientCheck0010 :
    completeCoefficientRowCheck factorRow row0010 10 coefficients0010 = true := by
  have hlen : coefficients0010.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0010 oddDots0010
      641 10 0 coefficients0010 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0010_checked oddSum0010_checked hlen hs

theorem coefficientCheck0011 :
    completeCoefficientRowCheck factorRow row0011 11 coefficients0011 = true := by
  have hlen : coefficients0011.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0011 oddDots0011
      641 11 0 coefficients0011 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0011_checked oddSum0011_checked hlen hs

theorem coefficientCheck0012 :
    completeCoefficientRowCheck factorRow row0012 12 coefficients0012 = true := by
  have hlen : coefficients0012.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0012 oddDots0012
      641 12 0 coefficients0012 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0012_checked oddSum0012_checked hlen hs

theorem coefficientCheck0013 :
    completeCoefficientRowCheck factorRow row0013 13 coefficients0013 = true := by
  have hlen : coefficients0013.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0013 oddDots0013
      641 13 0 coefficients0013 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0013_checked oddSum0013_checked hlen hs

theorem coefficientCheck0014 :
    completeCoefficientRowCheck factorRow row0014 14 coefficients0014 = true := by
  have hlen : coefficients0014.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0014 oddDots0014
      641 14 0 coefficients0014 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0014_checked oddSum0014_checked hlen hs

theorem coefficientCheck0015 :
    completeCoefficientRowCheck factorRow row0015 15 coefficients0015 = true := by
  have hlen : coefficients0015.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0015 oddDots0015
      641 15 0 coefficients0015 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0015_checked oddSum0015_checked hlen hs


end
end ErdosOverlap.Native6Grid
