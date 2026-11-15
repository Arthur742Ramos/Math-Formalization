module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck022
public import ErdosOverlap.Certificate.Native6Grid.Coefficients02

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0176 :
    completeCoefficientRowCheck factorRow row0176 176 coefficients0176 = true := by
  have hlen : coefficients0176.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0176 oddDots0176
      641 176 0 coefficients0176 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0176_checked oddSum0176_checked hlen hs

theorem coefficientCheck0177 :
    completeCoefficientRowCheck factorRow row0177 177 coefficients0177 = true := by
  have hlen : coefficients0177.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0177 oddDots0177
      641 177 0 coefficients0177 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0177_checked oddSum0177_checked hlen hs

theorem coefficientCheck0178 :
    completeCoefficientRowCheck factorRow row0178 178 coefficients0178 = true := by
  have hlen : coefficients0178.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0178 oddDots0178
      641 178 0 coefficients0178 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0178_checked oddSum0178_checked hlen hs

theorem coefficientCheck0179 :
    completeCoefficientRowCheck factorRow row0179 179 coefficients0179 = true := by
  have hlen : coefficients0179.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0179 oddDots0179
      641 179 0 coefficients0179 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0179_checked oddSum0179_checked hlen hs

theorem coefficientCheck0180 :
    completeCoefficientRowCheck factorRow row0180 180 coefficients0180 = true := by
  have hlen : coefficients0180.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0180 oddDots0180
      641 180 0 coefficients0180 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0180_checked oddSum0180_checked hlen hs

theorem coefficientCheck0181 :
    completeCoefficientRowCheck factorRow row0181 181 coefficients0181 = true := by
  have hlen : coefficients0181.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0181 oddDots0181
      641 181 0 coefficients0181 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0181_checked oddSum0181_checked hlen hs

theorem coefficientCheck0182 :
    completeCoefficientRowCheck factorRow row0182 182 coefficients0182 = true := by
  have hlen : coefficients0182.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0182 oddDots0182
      641 182 0 coefficients0182 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0182_checked oddSum0182_checked hlen hs

theorem coefficientCheck0183 :
    completeCoefficientRowCheck factorRow row0183 183 coefficients0183 = true := by
  have hlen : coefficients0183.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0183 oddDots0183
      641 183 0 coefficients0183 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0183_checked oddSum0183_checked hlen hs


end
end ErdosOverlap.Native6Grid
