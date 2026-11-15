module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck072
public import ErdosOverlap.Certificate.Native6Grid.Coefficients09

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0576 :
    completeCoefficientRowCheck factorRow row0576 576 coefficients0576 = true := by
  have hlen : coefficients0576.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0576 oddDots0576
      641 576 0 coefficients0576 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0576_checked oddSum0576_checked hlen hs

theorem coefficientCheck0577 :
    completeCoefficientRowCheck factorRow row0577 577 coefficients0577 = true := by
  have hlen : coefficients0577.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0577 oddDots0577
      641 577 0 coefficients0577 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0577_checked oddSum0577_checked hlen hs

theorem coefficientCheck0578 :
    completeCoefficientRowCheck factorRow row0578 578 coefficients0578 = true := by
  have hlen : coefficients0578.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0578 oddDots0578
      641 578 0 coefficients0578 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0578_checked oddSum0578_checked hlen hs

theorem coefficientCheck0579 :
    completeCoefficientRowCheck factorRow row0579 579 coefficients0579 = true := by
  have hlen : coefficients0579.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0579 oddDots0579
      641 579 0 coefficients0579 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0579_checked oddSum0579_checked hlen hs

theorem coefficientCheck0580 :
    completeCoefficientRowCheck factorRow row0580 580 coefficients0580 = true := by
  have hlen : coefficients0580.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0580 oddDots0580
      641 580 0 coefficients0580 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0580_checked oddSum0580_checked hlen hs

theorem coefficientCheck0581 :
    completeCoefficientRowCheck factorRow row0581 581 coefficients0581 = true := by
  have hlen : coefficients0581.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0581 oddDots0581
      641 581 0 coefficients0581 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0581_checked oddSum0581_checked hlen hs

theorem coefficientCheck0582 :
    completeCoefficientRowCheck factorRow row0582 582 coefficients0582 = true := by
  have hlen : coefficients0582.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0582 oddDots0582
      641 582 0 coefficients0582 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0582_checked oddSum0582_checked hlen hs

theorem coefficientCheck0583 :
    completeCoefficientRowCheck factorRow row0583 583 coefficients0583 = true := by
  have hlen : coefficients0583.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0583 oddDots0583
      641 583 0 coefficients0583 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0583_checked oddSum0583_checked hlen hs


end
end ErdosOverlap.Native6Grid
