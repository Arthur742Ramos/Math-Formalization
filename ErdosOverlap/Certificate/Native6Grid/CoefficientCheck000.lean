module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck000
public import ErdosOverlap.Certificate.Native6Grid.Coefficients00

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0000 :
    completeCoefficientRowCheck factorRow row0000 0 coefficients0000 = true := by
  have hlen : coefficients0000.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0000 oddDots0000
      641 0 0 coefficients0000 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0000_checked oddSum0000_checked hlen hs

theorem coefficientCheck0001 :
    completeCoefficientRowCheck factorRow row0001 1 coefficients0001 = true := by
  have hlen : coefficients0001.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0001 oddDots0001
      641 1 0 coefficients0001 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0001_checked oddSum0001_checked hlen hs

theorem coefficientCheck0002 :
    completeCoefficientRowCheck factorRow row0002 2 coefficients0002 = true := by
  have hlen : coefficients0002.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0002 oddDots0002
      641 2 0 coefficients0002 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0002_checked oddSum0002_checked hlen hs

theorem coefficientCheck0003 :
    completeCoefficientRowCheck factorRow row0003 3 coefficients0003 = true := by
  have hlen : coefficients0003.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0003 oddDots0003
      641 3 0 coefficients0003 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0003_checked oddSum0003_checked hlen hs

theorem coefficientCheck0004 :
    completeCoefficientRowCheck factorRow row0004 4 coefficients0004 = true := by
  have hlen : coefficients0004.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0004 oddDots0004
      641 4 0 coefficients0004 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0004_checked oddSum0004_checked hlen hs

theorem coefficientCheck0005 :
    completeCoefficientRowCheck factorRow row0005 5 coefficients0005 = true := by
  have hlen : coefficients0005.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0005 oddDots0005
      641 5 0 coefficients0005 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0005_checked oddSum0005_checked hlen hs

theorem coefficientCheck0006 :
    completeCoefficientRowCheck factorRow row0006 6 coefficients0006 = true := by
  have hlen : coefficients0006.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0006 oddDots0006
      641 6 0 coefficients0006 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0006_checked oddSum0006_checked hlen hs

theorem coefficientCheck0007 :
    completeCoefficientRowCheck factorRow row0007 7 coefficients0007 = true := by
  have hlen : coefficients0007.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0007 oddDots0007
      641 7 0 coefficients0007 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0007_checked oddSum0007_checked hlen hs


end
end ErdosOverlap.Native6Grid
