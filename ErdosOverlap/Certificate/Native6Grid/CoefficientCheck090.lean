module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck090
public import ErdosOverlap.Certificate.Native6Grid.Coefficients11

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0720 :
    completeCoefficientRowCheck factorRow row0720 720 coefficients0720 = true := by
  have hlen : coefficients0720.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0720 oddDots0720
      641 720 0 coefficients0720 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0720_checked oddSum0720_checked hlen hs

theorem coefficientCheck0721 :
    completeCoefficientRowCheck factorRow row0721 721 coefficients0721 = true := by
  have hlen : coefficients0721.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0721 oddDots0721
      641 721 0 coefficients0721 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0721_checked oddSum0721_checked hlen hs

theorem coefficientCheck0722 :
    completeCoefficientRowCheck factorRow row0722 722 coefficients0722 = true := by
  have hlen : coefficients0722.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0722 oddDots0722
      641 722 0 coefficients0722 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0722_checked oddSum0722_checked hlen hs

theorem coefficientCheck0723 :
    completeCoefficientRowCheck factorRow row0723 723 coefficients0723 = true := by
  have hlen : coefficients0723.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0723 oddDots0723
      641 723 0 coefficients0723 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0723_checked oddSum0723_checked hlen hs

theorem coefficientCheck0724 :
    completeCoefficientRowCheck factorRow row0724 724 coefficients0724 = true := by
  have hlen : coefficients0724.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0724 oddDots0724
      641 724 0 coefficients0724 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0724_checked oddSum0724_checked hlen hs

theorem coefficientCheck0725 :
    completeCoefficientRowCheck factorRow row0725 725 coefficients0725 = true := by
  have hlen : coefficients0725.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0725 oddDots0725
      641 725 0 coefficients0725 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0725_checked oddSum0725_checked hlen hs

theorem coefficientCheck0726 :
    completeCoefficientRowCheck factorRow row0726 726 coefficients0726 = true := by
  have hlen : coefficients0726.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0726 oddDots0726
      641 726 0 coefficients0726 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0726_checked oddSum0726_checked hlen hs

theorem coefficientCheck0727 :
    completeCoefficientRowCheck factorRow row0727 727 coefficients0727 = true := by
  have hlen : coefficients0727.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0727 oddDots0727
      641 727 0 coefficients0727 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0727_checked oddSum0727_checked hlen hs


end
end ErdosOverlap.Native6Grid
