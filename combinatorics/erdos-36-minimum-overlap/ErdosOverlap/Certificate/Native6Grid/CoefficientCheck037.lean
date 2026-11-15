module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck037
public import ErdosOverlap.Certificate.Native6Grid.Coefficients04

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0296 :
    completeCoefficientRowCheck factorRow row0296 296 coefficients0296 = true := by
  have hlen : coefficients0296.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0296 oddDots0296
      641 296 0 coefficients0296 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0296_checked oddSum0296_checked hlen hs

theorem coefficientCheck0297 :
    completeCoefficientRowCheck factorRow row0297 297 coefficients0297 = true := by
  have hlen : coefficients0297.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0297 oddDots0297
      641 297 0 coefficients0297 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0297_checked oddSum0297_checked hlen hs

theorem coefficientCheck0298 :
    completeCoefficientRowCheck factorRow row0298 298 coefficients0298 = true := by
  have hlen : coefficients0298.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0298 oddDots0298
      641 298 0 coefficients0298 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0298_checked oddSum0298_checked hlen hs

theorem coefficientCheck0299 :
    completeCoefficientRowCheck factorRow row0299 299 coefficients0299 = true := by
  have hlen : coefficients0299.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0299 oddDots0299
      641 299 0 coefficients0299 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0299_checked oddSum0299_checked hlen hs

theorem coefficientCheck0300 :
    completeCoefficientRowCheck factorRow row0300 300 coefficients0300 = true := by
  have hlen : coefficients0300.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0300 oddDots0300
      641 300 0 coefficients0300 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0300_checked oddSum0300_checked hlen hs

theorem coefficientCheck0301 :
    completeCoefficientRowCheck factorRow row0301 301 coefficients0301 = true := by
  have hlen : coefficients0301.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0301 oddDots0301
      641 301 0 coefficients0301 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0301_checked oddSum0301_checked hlen hs

theorem coefficientCheck0302 :
    completeCoefficientRowCheck factorRow row0302 302 coefficients0302 = true := by
  have hlen : coefficients0302.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0302 oddDots0302
      641 302 0 coefficients0302 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0302_checked oddSum0302_checked hlen hs

theorem coefficientCheck0303 :
    completeCoefficientRowCheck factorRow row0303 303 coefficients0303 = true := by
  have hlen : coefficients0303.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0303 oddDots0303
      641 303 0 coefficients0303 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0303_checked oddSum0303_checked hlen hs


end
end ErdosOverlap.Native6Grid
