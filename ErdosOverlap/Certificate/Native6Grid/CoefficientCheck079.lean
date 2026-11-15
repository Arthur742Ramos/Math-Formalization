module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck079
public import ErdosOverlap.Certificate.Native6Grid.Coefficients09

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0632 :
    completeCoefficientRowCheck factorRow row0632 632 coefficients0632 = true := by
  have hlen : coefficients0632.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0632 oddDots0632
      641 632 0 coefficients0632 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0632_checked oddSum0632_checked hlen hs

theorem coefficientCheck0633 :
    completeCoefficientRowCheck factorRow row0633 633 coefficients0633 = true := by
  have hlen : coefficients0633.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0633 oddDots0633
      641 633 0 coefficients0633 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0633_checked oddSum0633_checked hlen hs

theorem coefficientCheck0634 :
    completeCoefficientRowCheck factorRow row0634 634 coefficients0634 = true := by
  have hlen : coefficients0634.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0634 oddDots0634
      641 634 0 coefficients0634 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0634_checked oddSum0634_checked hlen hs

theorem coefficientCheck0635 :
    completeCoefficientRowCheck factorRow row0635 635 coefficients0635 = true := by
  have hlen : coefficients0635.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0635 oddDots0635
      641 635 0 coefficients0635 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0635_checked oddSum0635_checked hlen hs

theorem coefficientCheck0636 :
    completeCoefficientRowCheck factorRow row0636 636 coefficients0636 = true := by
  have hlen : coefficients0636.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0636 oddDots0636
      641 636 0 coefficients0636 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0636_checked oddSum0636_checked hlen hs

theorem coefficientCheck0637 :
    completeCoefficientRowCheck factorRow row0637 637 coefficients0637 = true := by
  have hlen : coefficients0637.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0637 oddDots0637
      641 637 0 coefficients0637 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0637_checked oddSum0637_checked hlen hs

theorem coefficientCheck0638 :
    completeCoefficientRowCheck factorRow row0638 638 coefficients0638 = true := by
  have hlen : coefficients0638.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0638 oddDots0638
      641 638 0 coefficients0638 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0638_checked oddSum0638_checked hlen hs

theorem coefficientCheck0639 :
    completeCoefficientRowCheck factorRow row0639 639 coefficients0639 = true := by
  have hlen : coefficients0639.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0639 oddDots0639
      641 639 0 coefficients0639 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0639_checked oddSum0639_checked hlen hs


end
end ErdosOverlap.Native6Grid
