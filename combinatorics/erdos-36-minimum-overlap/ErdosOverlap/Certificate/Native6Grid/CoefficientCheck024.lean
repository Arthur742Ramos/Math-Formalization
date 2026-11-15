module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck024
public import ErdosOverlap.Certificate.Native6Grid.Coefficients03

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0192 :
    completeCoefficientRowCheck factorRow row0192 192 coefficients0192 = true := by
  have hlen : coefficients0192.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0192 oddDots0192
      641 192 0 coefficients0192 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0192_checked oddSum0192_checked hlen hs

theorem coefficientCheck0193 :
    completeCoefficientRowCheck factorRow row0193 193 coefficients0193 = true := by
  have hlen : coefficients0193.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0193 oddDots0193
      641 193 0 coefficients0193 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0193_checked oddSum0193_checked hlen hs

theorem coefficientCheck0194 :
    completeCoefficientRowCheck factorRow row0194 194 coefficients0194 = true := by
  have hlen : coefficients0194.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0194 oddDots0194
      641 194 0 coefficients0194 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0194_checked oddSum0194_checked hlen hs

theorem coefficientCheck0195 :
    completeCoefficientRowCheck factorRow row0195 195 coefficients0195 = true := by
  have hlen : coefficients0195.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0195 oddDots0195
      641 195 0 coefficients0195 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0195_checked oddSum0195_checked hlen hs

theorem coefficientCheck0196 :
    completeCoefficientRowCheck factorRow row0196 196 coefficients0196 = true := by
  have hlen : coefficients0196.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0196 oddDots0196
      641 196 0 coefficients0196 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0196_checked oddSum0196_checked hlen hs

theorem coefficientCheck0197 :
    completeCoefficientRowCheck factorRow row0197 197 coefficients0197 = true := by
  have hlen : coefficients0197.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0197 oddDots0197
      641 197 0 coefficients0197 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0197_checked oddSum0197_checked hlen hs

theorem coefficientCheck0198 :
    completeCoefficientRowCheck factorRow row0198 198 coefficients0198 = true := by
  have hlen : coefficients0198.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0198 oddDots0198
      641 198 0 coefficients0198 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0198_checked oddSum0198_checked hlen hs

theorem coefficientCheck0199 :
    completeCoefficientRowCheck factorRow row0199 199 coefficients0199 = true := by
  have hlen : coefficients0199.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0199 oddDots0199
      641 199 0 coefficients0199 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0199_checked oddSum0199_checked hlen hs


end
end ErdosOverlap.Native6Grid
