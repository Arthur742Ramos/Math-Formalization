module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck020
public import ErdosOverlap.Certificate.Native6Grid.Coefficients02

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0160 :
    completeCoefficientRowCheck factorRow row0160 160 coefficients0160 = true := by
  have hlen : coefficients0160.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0160 oddDots0160
      641 160 0 coefficients0160 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0160_checked oddSum0160_checked hlen hs

theorem coefficientCheck0161 :
    completeCoefficientRowCheck factorRow row0161 161 coefficients0161 = true := by
  have hlen : coefficients0161.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0161 oddDots0161
      641 161 0 coefficients0161 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0161_checked oddSum0161_checked hlen hs

theorem coefficientCheck0162 :
    completeCoefficientRowCheck factorRow row0162 162 coefficients0162 = true := by
  have hlen : coefficients0162.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0162 oddDots0162
      641 162 0 coefficients0162 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0162_checked oddSum0162_checked hlen hs

theorem coefficientCheck0163 :
    completeCoefficientRowCheck factorRow row0163 163 coefficients0163 = true := by
  have hlen : coefficients0163.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0163 oddDots0163
      641 163 0 coefficients0163 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0163_checked oddSum0163_checked hlen hs

theorem coefficientCheck0164 :
    completeCoefficientRowCheck factorRow row0164 164 coefficients0164 = true := by
  have hlen : coefficients0164.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0164 oddDots0164
      641 164 0 coefficients0164 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0164_checked oddSum0164_checked hlen hs

theorem coefficientCheck0165 :
    completeCoefficientRowCheck factorRow row0165 165 coefficients0165 = true := by
  have hlen : coefficients0165.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0165 oddDots0165
      641 165 0 coefficients0165 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0165_checked oddSum0165_checked hlen hs

theorem coefficientCheck0166 :
    completeCoefficientRowCheck factorRow row0166 166 coefficients0166 = true := by
  have hlen : coefficients0166.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0166 oddDots0166
      641 166 0 coefficients0166 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0166_checked oddSum0166_checked hlen hs

theorem coefficientCheck0167 :
    completeCoefficientRowCheck factorRow row0167 167 coefficients0167 = true := by
  have hlen : coefficients0167.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0167 oddDots0167
      641 167 0 coefficients0167 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0167_checked oddSum0167_checked hlen hs


end
end ErdosOverlap.Native6Grid
