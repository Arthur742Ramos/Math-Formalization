module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck059
public import ErdosOverlap.Certificate.Native6Grid.Coefficients07

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0472 :
    completeCoefficientRowCheck factorRow row0472 472 coefficients0472 = true := by
  have hlen : coefficients0472.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0472 oddDots0472
      641 472 0 coefficients0472 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0472_checked oddSum0472_checked hlen hs

theorem coefficientCheck0473 :
    completeCoefficientRowCheck factorRow row0473 473 coefficients0473 = true := by
  have hlen : coefficients0473.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0473 oddDots0473
      641 473 0 coefficients0473 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0473_checked oddSum0473_checked hlen hs

theorem coefficientCheck0474 :
    completeCoefficientRowCheck factorRow row0474 474 coefficients0474 = true := by
  have hlen : coefficients0474.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0474 oddDots0474
      641 474 0 coefficients0474 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0474_checked oddSum0474_checked hlen hs

theorem coefficientCheck0475 :
    completeCoefficientRowCheck factorRow row0475 475 coefficients0475 = true := by
  have hlen : coefficients0475.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0475 oddDots0475
      641 475 0 coefficients0475 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0475_checked oddSum0475_checked hlen hs

theorem coefficientCheck0476 :
    completeCoefficientRowCheck factorRow row0476 476 coefficients0476 = true := by
  have hlen : coefficients0476.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0476 oddDots0476
      641 476 0 coefficients0476 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0476_checked oddSum0476_checked hlen hs

theorem coefficientCheck0477 :
    completeCoefficientRowCheck factorRow row0477 477 coefficients0477 = true := by
  have hlen : coefficients0477.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0477 oddDots0477
      641 477 0 coefficients0477 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0477_checked oddSum0477_checked hlen hs

theorem coefficientCheck0478 :
    completeCoefficientRowCheck factorRow row0478 478 coefficients0478 = true := by
  have hlen : coefficients0478.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0478 oddDots0478
      641 478 0 coefficients0478 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0478_checked oddSum0478_checked hlen hs

theorem coefficientCheck0479 :
    completeCoefficientRowCheck factorRow row0479 479 coefficients0479 = true := by
  have hlen : coefficients0479.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0479 oddDots0479
      641 479 0 coefficients0479 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0479_checked oddSum0479_checked hlen hs


end
end ErdosOverlap.Native6Grid
