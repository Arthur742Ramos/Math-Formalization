module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck025
public import ErdosOverlap.Certificate.Native6Grid.Coefficients03

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0200 :
    completeCoefficientRowCheck factorRow row0200 200 coefficients0200 = true := by
  have hlen : coefficients0200.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0200 oddDots0200
      641 200 0 coefficients0200 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0200_checked oddSum0200_checked hlen hs

theorem coefficientCheck0201 :
    completeCoefficientRowCheck factorRow row0201 201 coefficients0201 = true := by
  have hlen : coefficients0201.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0201 oddDots0201
      641 201 0 coefficients0201 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0201_checked oddSum0201_checked hlen hs

theorem coefficientCheck0202 :
    completeCoefficientRowCheck factorRow row0202 202 coefficients0202 = true := by
  have hlen : coefficients0202.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0202 oddDots0202
      641 202 0 coefficients0202 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0202_checked oddSum0202_checked hlen hs

theorem coefficientCheck0203 :
    completeCoefficientRowCheck factorRow row0203 203 coefficients0203 = true := by
  have hlen : coefficients0203.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0203 oddDots0203
      641 203 0 coefficients0203 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0203_checked oddSum0203_checked hlen hs

theorem coefficientCheck0204 :
    completeCoefficientRowCheck factorRow row0204 204 coefficients0204 = true := by
  have hlen : coefficients0204.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0204 oddDots0204
      641 204 0 coefficients0204 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0204_checked oddSum0204_checked hlen hs

theorem coefficientCheck0205 :
    completeCoefficientRowCheck factorRow row0205 205 coefficients0205 = true := by
  have hlen : coefficients0205.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0205 oddDots0205
      641 205 0 coefficients0205 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0205_checked oddSum0205_checked hlen hs

theorem coefficientCheck0206 :
    completeCoefficientRowCheck factorRow row0206 206 coefficients0206 = true := by
  have hlen : coefficients0206.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0206 oddDots0206
      641 206 0 coefficients0206 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0206_checked oddSum0206_checked hlen hs

theorem coefficientCheck0207 :
    completeCoefficientRowCheck factorRow row0207 207 coefficients0207 = true := by
  have hlen : coefficients0207.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0207 oddDots0207
      641 207 0 coefficients0207 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0207_checked oddSum0207_checked hlen hs


end
end ErdosOverlap.Native6Grid
