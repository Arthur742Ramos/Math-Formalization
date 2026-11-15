module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck023
public import ErdosOverlap.Certificate.Native6Grid.Coefficients02

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0184 :
    completeCoefficientRowCheck factorRow row0184 184 coefficients0184 = true := by
  have hlen : coefficients0184.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0184 oddDots0184
      641 184 0 coefficients0184 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0184_checked oddSum0184_checked hlen hs

theorem coefficientCheck0185 :
    completeCoefficientRowCheck factorRow row0185 185 coefficients0185 = true := by
  have hlen : coefficients0185.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0185 oddDots0185
      641 185 0 coefficients0185 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0185_checked oddSum0185_checked hlen hs

theorem coefficientCheck0186 :
    completeCoefficientRowCheck factorRow row0186 186 coefficients0186 = true := by
  have hlen : coefficients0186.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0186 oddDots0186
      641 186 0 coefficients0186 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0186_checked oddSum0186_checked hlen hs

theorem coefficientCheck0187 :
    completeCoefficientRowCheck factorRow row0187 187 coefficients0187 = true := by
  have hlen : coefficients0187.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0187 oddDots0187
      641 187 0 coefficients0187 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0187_checked oddSum0187_checked hlen hs

theorem coefficientCheck0188 :
    completeCoefficientRowCheck factorRow row0188 188 coefficients0188 = true := by
  have hlen : coefficients0188.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0188 oddDots0188
      641 188 0 coefficients0188 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0188_checked oddSum0188_checked hlen hs

theorem coefficientCheck0189 :
    completeCoefficientRowCheck factorRow row0189 189 coefficients0189 = true := by
  have hlen : coefficients0189.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0189 oddDots0189
      641 189 0 coefficients0189 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0189_checked oddSum0189_checked hlen hs

theorem coefficientCheck0190 :
    completeCoefficientRowCheck factorRow row0190 190 coefficients0190 = true := by
  have hlen : coefficients0190.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0190 oddDots0190
      641 190 0 coefficients0190 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0190_checked oddSum0190_checked hlen hs

theorem coefficientCheck0191 :
    completeCoefficientRowCheck factorRow row0191 191 coefficients0191 = true := by
  have hlen : coefficients0191.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0191 oddDots0191
      641 191 0 coefficients0191 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0191_checked oddSum0191_checked hlen hs


end
end ErdosOverlap.Native6Grid
