module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck026
public import ErdosOverlap.Certificate.Native6Grid.Coefficients03

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0208 :
    completeCoefficientRowCheck factorRow row0208 208 coefficients0208 = true := by
  have hlen : coefficients0208.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0208 oddDots0208
      641 208 0 coefficients0208 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0208_checked oddSum0208_checked hlen hs

theorem coefficientCheck0209 :
    completeCoefficientRowCheck factorRow row0209 209 coefficients0209 = true := by
  have hlen : coefficients0209.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0209 oddDots0209
      641 209 0 coefficients0209 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0209_checked oddSum0209_checked hlen hs

theorem coefficientCheck0210 :
    completeCoefficientRowCheck factorRow row0210 210 coefficients0210 = true := by
  have hlen : coefficients0210.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0210 oddDots0210
      641 210 0 coefficients0210 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0210_checked oddSum0210_checked hlen hs

theorem coefficientCheck0211 :
    completeCoefficientRowCheck factorRow row0211 211 coefficients0211 = true := by
  have hlen : coefficients0211.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0211 oddDots0211
      641 211 0 coefficients0211 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0211_checked oddSum0211_checked hlen hs

theorem coefficientCheck0212 :
    completeCoefficientRowCheck factorRow row0212 212 coefficients0212 = true := by
  have hlen : coefficients0212.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0212 oddDots0212
      641 212 0 coefficients0212 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0212_checked oddSum0212_checked hlen hs

theorem coefficientCheck0213 :
    completeCoefficientRowCheck factorRow row0213 213 coefficients0213 = true := by
  have hlen : coefficients0213.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0213 oddDots0213
      641 213 0 coefficients0213 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0213_checked oddSum0213_checked hlen hs

theorem coefficientCheck0214 :
    completeCoefficientRowCheck factorRow row0214 214 coefficients0214 = true := by
  have hlen : coefficients0214.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0214 oddDots0214
      641 214 0 coefficients0214 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0214_checked oddSum0214_checked hlen hs

theorem coefficientCheck0215 :
    completeCoefficientRowCheck factorRow row0215 215 coefficients0215 = true := by
  have hlen : coefficients0215.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0215 oddDots0215
      641 215 0 coefficients0215 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0215_checked oddSum0215_checked hlen hs


end
end ErdosOverlap.Native6Grid
