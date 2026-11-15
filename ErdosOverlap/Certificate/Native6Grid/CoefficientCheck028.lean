module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck028
public import ErdosOverlap.Certificate.Native6Grid.Coefficients03

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0224 :
    completeCoefficientRowCheck factorRow row0224 224 coefficients0224 = true := by
  have hlen : coefficients0224.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0224 oddDots0224
      641 224 0 coefficients0224 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0224_checked oddSum0224_checked hlen hs

theorem coefficientCheck0225 :
    completeCoefficientRowCheck factorRow row0225 225 coefficients0225 = true := by
  have hlen : coefficients0225.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0225 oddDots0225
      641 225 0 coefficients0225 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0225_checked oddSum0225_checked hlen hs

theorem coefficientCheck0226 :
    completeCoefficientRowCheck factorRow row0226 226 coefficients0226 = true := by
  have hlen : coefficients0226.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0226 oddDots0226
      641 226 0 coefficients0226 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0226_checked oddSum0226_checked hlen hs

theorem coefficientCheck0227 :
    completeCoefficientRowCheck factorRow row0227 227 coefficients0227 = true := by
  have hlen : coefficients0227.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0227 oddDots0227
      641 227 0 coefficients0227 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0227_checked oddSum0227_checked hlen hs

theorem coefficientCheck0228 :
    completeCoefficientRowCheck factorRow row0228 228 coefficients0228 = true := by
  have hlen : coefficients0228.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0228 oddDots0228
      641 228 0 coefficients0228 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0228_checked oddSum0228_checked hlen hs

theorem coefficientCheck0229 :
    completeCoefficientRowCheck factorRow row0229 229 coefficients0229 = true := by
  have hlen : coefficients0229.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0229 oddDots0229
      641 229 0 coefficients0229 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0229_checked oddSum0229_checked hlen hs

theorem coefficientCheck0230 :
    completeCoefficientRowCheck factorRow row0230 230 coefficients0230 = true := by
  have hlen : coefficients0230.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0230 oddDots0230
      641 230 0 coefficients0230 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0230_checked oddSum0230_checked hlen hs

theorem coefficientCheck0231 :
    completeCoefficientRowCheck factorRow row0231 231 coefficients0231 = true := by
  have hlen : coefficients0231.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0231 oddDots0231
      641 231 0 coefficients0231 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0231_checked oddSum0231_checked hlen hs


end
end ErdosOverlap.Native6Grid
