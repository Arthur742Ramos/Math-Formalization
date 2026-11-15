module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck058
public import ErdosOverlap.Certificate.Native6Grid.Coefficients07

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0464 :
    completeCoefficientRowCheck factorRow row0464 464 coefficients0464 = true := by
  have hlen : coefficients0464.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0464 oddDots0464
      641 464 0 coefficients0464 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0464_checked oddSum0464_checked hlen hs

theorem coefficientCheck0465 :
    completeCoefficientRowCheck factorRow row0465 465 coefficients0465 = true := by
  have hlen : coefficients0465.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0465 oddDots0465
      641 465 0 coefficients0465 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0465_checked oddSum0465_checked hlen hs

theorem coefficientCheck0466 :
    completeCoefficientRowCheck factorRow row0466 466 coefficients0466 = true := by
  have hlen : coefficients0466.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0466 oddDots0466
      641 466 0 coefficients0466 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0466_checked oddSum0466_checked hlen hs

theorem coefficientCheck0467 :
    completeCoefficientRowCheck factorRow row0467 467 coefficients0467 = true := by
  have hlen : coefficients0467.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0467 oddDots0467
      641 467 0 coefficients0467 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0467_checked oddSum0467_checked hlen hs

theorem coefficientCheck0468 :
    completeCoefficientRowCheck factorRow row0468 468 coefficients0468 = true := by
  have hlen : coefficients0468.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0468 oddDots0468
      641 468 0 coefficients0468 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0468_checked oddSum0468_checked hlen hs

theorem coefficientCheck0469 :
    completeCoefficientRowCheck factorRow row0469 469 coefficients0469 = true := by
  have hlen : coefficients0469.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0469 oddDots0469
      641 469 0 coefficients0469 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0469_checked oddSum0469_checked hlen hs

theorem coefficientCheck0470 :
    completeCoefficientRowCheck factorRow row0470 470 coefficients0470 = true := by
  have hlen : coefficients0470.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0470 oddDots0470
      641 470 0 coefficients0470 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0470_checked oddSum0470_checked hlen hs

theorem coefficientCheck0471 :
    completeCoefficientRowCheck factorRow row0471 471 coefficients0471 = true := by
  have hlen : coefficients0471.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0471 oddDots0471
      641 471 0 coefficients0471 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0471_checked oddSum0471_checked hlen hs


end
end ErdosOverlap.Native6Grid
