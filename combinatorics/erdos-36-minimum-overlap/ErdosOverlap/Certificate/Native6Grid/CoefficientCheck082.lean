module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck082
public import ErdosOverlap.Certificate.Native6Grid.Coefficients10

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0656 :
    completeCoefficientRowCheck factorRow row0656 656 coefficients0656 = true := by
  have hlen : coefficients0656.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0656 oddDots0656
      641 656 0 coefficients0656 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0656_checked oddSum0656_checked hlen hs

theorem coefficientCheck0657 :
    completeCoefficientRowCheck factorRow row0657 657 coefficients0657 = true := by
  have hlen : coefficients0657.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0657 oddDots0657
      641 657 0 coefficients0657 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0657_checked oddSum0657_checked hlen hs

theorem coefficientCheck0658 :
    completeCoefficientRowCheck factorRow row0658 658 coefficients0658 = true := by
  have hlen : coefficients0658.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0658 oddDots0658
      641 658 0 coefficients0658 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0658_checked oddSum0658_checked hlen hs

theorem coefficientCheck0659 :
    completeCoefficientRowCheck factorRow row0659 659 coefficients0659 = true := by
  have hlen : coefficients0659.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0659 oddDots0659
      641 659 0 coefficients0659 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0659_checked oddSum0659_checked hlen hs

theorem coefficientCheck0660 :
    completeCoefficientRowCheck factorRow row0660 660 coefficients0660 = true := by
  have hlen : coefficients0660.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0660 oddDots0660
      641 660 0 coefficients0660 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0660_checked oddSum0660_checked hlen hs

theorem coefficientCheck0661 :
    completeCoefficientRowCheck factorRow row0661 661 coefficients0661 = true := by
  have hlen : coefficients0661.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0661 oddDots0661
      641 661 0 coefficients0661 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0661_checked oddSum0661_checked hlen hs

theorem coefficientCheck0662 :
    completeCoefficientRowCheck factorRow row0662 662 coefficients0662 = true := by
  have hlen : coefficients0662.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0662 oddDots0662
      641 662 0 coefficients0662 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0662_checked oddSum0662_checked hlen hs

theorem coefficientCheck0663 :
    completeCoefficientRowCheck factorRow row0663 663 coefficients0663 = true := by
  have hlen : coefficients0663.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0663 oddDots0663
      641 663 0 coefficients0663 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0663_checked oddSum0663_checked hlen hs


end
end ErdosOverlap.Native6Grid
