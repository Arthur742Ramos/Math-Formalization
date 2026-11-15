module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck068
public import ErdosOverlap.Certificate.Native6Grid.Coefficients08

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0544 :
    completeCoefficientRowCheck factorRow row0544 544 coefficients0544 = true := by
  have hlen : coefficients0544.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0544 oddDots0544
      641 544 0 coefficients0544 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0544_checked oddSum0544_checked hlen hs

theorem coefficientCheck0545 :
    completeCoefficientRowCheck factorRow row0545 545 coefficients0545 = true := by
  have hlen : coefficients0545.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0545 oddDots0545
      641 545 0 coefficients0545 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0545_checked oddSum0545_checked hlen hs

theorem coefficientCheck0546 :
    completeCoefficientRowCheck factorRow row0546 546 coefficients0546 = true := by
  have hlen : coefficients0546.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0546 oddDots0546
      641 546 0 coefficients0546 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0546_checked oddSum0546_checked hlen hs

theorem coefficientCheck0547 :
    completeCoefficientRowCheck factorRow row0547 547 coefficients0547 = true := by
  have hlen : coefficients0547.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0547 oddDots0547
      641 547 0 coefficients0547 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0547_checked oddSum0547_checked hlen hs

theorem coefficientCheck0548 :
    completeCoefficientRowCheck factorRow row0548 548 coefficients0548 = true := by
  have hlen : coefficients0548.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0548 oddDots0548
      641 548 0 coefficients0548 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0548_checked oddSum0548_checked hlen hs

theorem coefficientCheck0549 :
    completeCoefficientRowCheck factorRow row0549 549 coefficients0549 = true := by
  have hlen : coefficients0549.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0549 oddDots0549
      641 549 0 coefficients0549 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0549_checked oddSum0549_checked hlen hs

theorem coefficientCheck0550 :
    completeCoefficientRowCheck factorRow row0550 550 coefficients0550 = true := by
  have hlen : coefficients0550.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0550 oddDots0550
      641 550 0 coefficients0550 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0550_checked oddSum0550_checked hlen hs

theorem coefficientCheck0551 :
    completeCoefficientRowCheck factorRow row0551 551 coefficients0551 = true := by
  have hlen : coefficients0551.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0551 oddDots0551
      641 551 0 coefficients0551 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0551_checked oddSum0551_checked hlen hs


end
end ErdosOverlap.Native6Grid
