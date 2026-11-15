module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck055
public import ErdosOverlap.Certificate.Native6Grid.Coefficients06

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0440 :
    completeCoefficientRowCheck factorRow row0440 440 coefficients0440 = true := by
  have hlen : coefficients0440.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0440 oddDots0440
      641 440 0 coefficients0440 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0440_checked oddSum0440_checked hlen hs

theorem coefficientCheck0441 :
    completeCoefficientRowCheck factorRow row0441 441 coefficients0441 = true := by
  have hlen : coefficients0441.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0441 oddDots0441
      641 441 0 coefficients0441 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0441_checked oddSum0441_checked hlen hs

theorem coefficientCheck0442 :
    completeCoefficientRowCheck factorRow row0442 442 coefficients0442 = true := by
  have hlen : coefficients0442.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0442 oddDots0442
      641 442 0 coefficients0442 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0442_checked oddSum0442_checked hlen hs

theorem coefficientCheck0443 :
    completeCoefficientRowCheck factorRow row0443 443 coefficients0443 = true := by
  have hlen : coefficients0443.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0443 oddDots0443
      641 443 0 coefficients0443 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0443_checked oddSum0443_checked hlen hs

theorem coefficientCheck0444 :
    completeCoefficientRowCheck factorRow row0444 444 coefficients0444 = true := by
  have hlen : coefficients0444.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0444 oddDots0444
      641 444 0 coefficients0444 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0444_checked oddSum0444_checked hlen hs

theorem coefficientCheck0445 :
    completeCoefficientRowCheck factorRow row0445 445 coefficients0445 = true := by
  have hlen : coefficients0445.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0445 oddDots0445
      641 445 0 coefficients0445 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0445_checked oddSum0445_checked hlen hs

theorem coefficientCheck0446 :
    completeCoefficientRowCheck factorRow row0446 446 coefficients0446 = true := by
  have hlen : coefficients0446.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0446 oddDots0446
      641 446 0 coefficients0446 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0446_checked oddSum0446_checked hlen hs

theorem coefficientCheck0447 :
    completeCoefficientRowCheck factorRow row0447 447 coefficients0447 = true := by
  have hlen : coefficients0447.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0447 oddDots0447
      641 447 0 coefficients0447 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0447_checked oddSum0447_checked hlen hs


end
end ErdosOverlap.Native6Grid
