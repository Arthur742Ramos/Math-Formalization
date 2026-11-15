module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck080
public import ErdosOverlap.Certificate.Native6Grid.Coefficients10

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0640 :
    completeCoefficientRowCheck factorRow row0640 640 coefficients0640 = true := by
  have hlen : coefficients0640.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0640 oddDots0640
      641 640 0 coefficients0640 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0640_checked oddSum0640_checked hlen hs

theorem coefficientCheck0641 :
    completeCoefficientRowCheck factorRow row0641 641 coefficients0641 = true := by
  have hlen : coefficients0641.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0641 oddDots0641
      641 641 0 coefficients0641 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0641_checked oddSum0641_checked hlen hs

theorem coefficientCheck0642 :
    completeCoefficientRowCheck factorRow row0642 642 coefficients0642 = true := by
  have hlen : coefficients0642.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0642 oddDots0642
      641 642 0 coefficients0642 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0642_checked oddSum0642_checked hlen hs

theorem coefficientCheck0643 :
    completeCoefficientRowCheck factorRow row0643 643 coefficients0643 = true := by
  have hlen : coefficients0643.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0643 oddDots0643
      641 643 0 coefficients0643 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0643_checked oddSum0643_checked hlen hs

theorem coefficientCheck0644 :
    completeCoefficientRowCheck factorRow row0644 644 coefficients0644 = true := by
  have hlen : coefficients0644.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0644 oddDots0644
      641 644 0 coefficients0644 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0644_checked oddSum0644_checked hlen hs

theorem coefficientCheck0645 :
    completeCoefficientRowCheck factorRow row0645 645 coefficients0645 = true := by
  have hlen : coefficients0645.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0645 oddDots0645
      641 645 0 coefficients0645 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0645_checked oddSum0645_checked hlen hs

theorem coefficientCheck0646 :
    completeCoefficientRowCheck factorRow row0646 646 coefficients0646 = true := by
  have hlen : coefficients0646.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0646 oddDots0646
      641 646 0 coefficients0646 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0646_checked oddSum0646_checked hlen hs

theorem coefficientCheck0647 :
    completeCoefficientRowCheck factorRow row0647 647 coefficients0647 = true := by
  have hlen : coefficients0647.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0647 oddDots0647
      641 647 0 coefficients0647 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0647_checked oddSum0647_checked hlen hs


end
end ErdosOverlap.Native6Grid
