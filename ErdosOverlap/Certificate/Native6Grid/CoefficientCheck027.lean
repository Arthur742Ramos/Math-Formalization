module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck027
public import ErdosOverlap.Certificate.Native6Grid.Coefficients03

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0216 :
    completeCoefficientRowCheck factorRow row0216 216 coefficients0216 = true := by
  have hlen : coefficients0216.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0216 oddDots0216
      641 216 0 coefficients0216 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0216_checked oddSum0216_checked hlen hs

theorem coefficientCheck0217 :
    completeCoefficientRowCheck factorRow row0217 217 coefficients0217 = true := by
  have hlen : coefficients0217.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0217 oddDots0217
      641 217 0 coefficients0217 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0217_checked oddSum0217_checked hlen hs

theorem coefficientCheck0218 :
    completeCoefficientRowCheck factorRow row0218 218 coefficients0218 = true := by
  have hlen : coefficients0218.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0218 oddDots0218
      641 218 0 coefficients0218 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0218_checked oddSum0218_checked hlen hs

theorem coefficientCheck0219 :
    completeCoefficientRowCheck factorRow row0219 219 coefficients0219 = true := by
  have hlen : coefficients0219.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0219 oddDots0219
      641 219 0 coefficients0219 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0219_checked oddSum0219_checked hlen hs

theorem coefficientCheck0220 :
    completeCoefficientRowCheck factorRow row0220 220 coefficients0220 = true := by
  have hlen : coefficients0220.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0220 oddDots0220
      641 220 0 coefficients0220 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0220_checked oddSum0220_checked hlen hs

theorem coefficientCheck0221 :
    completeCoefficientRowCheck factorRow row0221 221 coefficients0221 = true := by
  have hlen : coefficients0221.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0221 oddDots0221
      641 221 0 coefficients0221 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0221_checked oddSum0221_checked hlen hs

theorem coefficientCheck0222 :
    completeCoefficientRowCheck factorRow row0222 222 coefficients0222 = true := by
  have hlen : coefficients0222.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0222 oddDots0222
      641 222 0 coefficients0222 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0222_checked oddSum0222_checked hlen hs

theorem coefficientCheck0223 :
    completeCoefficientRowCheck factorRow row0223 223 coefficients0223 = true := by
  have hlen : coefficients0223.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0223 oddDots0223
      641 223 0 coefficients0223 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0223_checked oddSum0223_checked hlen hs


end
end ErdosOverlap.Native6Grid
