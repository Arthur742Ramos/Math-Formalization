module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck086
public import ErdosOverlap.Certificate.Native6Grid.Coefficients10

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0688 :
    completeCoefficientRowCheck factorRow row0688 688 coefficients0688 = true := by
  have hlen : coefficients0688.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0688 oddDots0688
      641 688 0 coefficients0688 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0688_checked oddSum0688_checked hlen hs

theorem coefficientCheck0689 :
    completeCoefficientRowCheck factorRow row0689 689 coefficients0689 = true := by
  have hlen : coefficients0689.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0689 oddDots0689
      641 689 0 coefficients0689 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0689_checked oddSum0689_checked hlen hs

theorem coefficientCheck0690 :
    completeCoefficientRowCheck factorRow row0690 690 coefficients0690 = true := by
  have hlen : coefficients0690.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0690 oddDots0690
      641 690 0 coefficients0690 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0690_checked oddSum0690_checked hlen hs

theorem coefficientCheck0691 :
    completeCoefficientRowCheck factorRow row0691 691 coefficients0691 = true := by
  have hlen : coefficients0691.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0691 oddDots0691
      641 691 0 coefficients0691 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0691_checked oddSum0691_checked hlen hs

theorem coefficientCheck0692 :
    completeCoefficientRowCheck factorRow row0692 692 coefficients0692 = true := by
  have hlen : coefficients0692.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0692 oddDots0692
      641 692 0 coefficients0692 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0692_checked oddSum0692_checked hlen hs

theorem coefficientCheck0693 :
    completeCoefficientRowCheck factorRow row0693 693 coefficients0693 = true := by
  have hlen : coefficients0693.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0693 oddDots0693
      641 693 0 coefficients0693 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0693_checked oddSum0693_checked hlen hs

theorem coefficientCheck0694 :
    completeCoefficientRowCheck factorRow row0694 694 coefficients0694 = true := by
  have hlen : coefficients0694.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0694 oddDots0694
      641 694 0 coefficients0694 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0694_checked oddSum0694_checked hlen hs

theorem coefficientCheck0695 :
    completeCoefficientRowCheck factorRow row0695 695 coefficients0695 = true := by
  have hlen : coefficients0695.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0695 oddDots0695
      641 695 0 coefficients0695 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0695_checked oddSum0695_checked hlen hs


end
end ErdosOverlap.Native6Grid
