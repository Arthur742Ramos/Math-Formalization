module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck101
public import ErdosOverlap.Certificate.Native6Grid.Coefficients12

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0808 :
    completeCoefficientRowCheck factorRow row0808 808 coefficients0808 = true := by
  have hlen : coefficients0808.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0808 oddDots0808
      641 808 0 coefficients0808 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0808_checked oddSum0808_checked hlen hs

theorem coefficientCheck0809 :
    completeCoefficientRowCheck factorRow row0809 809 coefficients0809 = true := by
  have hlen : coefficients0809.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0809 oddDots0809
      641 809 0 coefficients0809 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0809_checked oddSum0809_checked hlen hs

theorem coefficientCheck0810 :
    completeCoefficientRowCheck factorRow row0810 810 coefficients0810 = true := by
  have hlen : coefficients0810.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0810 oddDots0810
      641 810 0 coefficients0810 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0810_checked oddSum0810_checked hlen hs

theorem coefficientCheck0811 :
    completeCoefficientRowCheck factorRow row0811 811 coefficients0811 = true := by
  have hlen : coefficients0811.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0811 oddDots0811
      641 811 0 coefficients0811 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0811_checked oddSum0811_checked hlen hs

theorem coefficientCheck0812 :
    completeCoefficientRowCheck factorRow row0812 812 coefficients0812 = true := by
  have hlen : coefficients0812.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0812 oddDots0812
      641 812 0 coefficients0812 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0812_checked oddSum0812_checked hlen hs

theorem coefficientCheck0813 :
    completeCoefficientRowCheck factorRow row0813 813 coefficients0813 = true := by
  have hlen : coefficients0813.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0813 oddDots0813
      641 813 0 coefficients0813 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0813_checked oddSum0813_checked hlen hs

theorem coefficientCheck0814 :
    completeCoefficientRowCheck factorRow row0814 814 coefficients0814 = true := by
  have hlen : coefficients0814.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0814 oddDots0814
      641 814 0 coefficients0814 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0814_checked oddSum0814_checked hlen hs

theorem coefficientCheck0815 :
    completeCoefficientRowCheck factorRow row0815 815 coefficients0815 = true := by
  have hlen : coefficients0815.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0815 oddDots0815
      641 815 0 coefficients0815 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0815_checked oddSum0815_checked hlen hs


end
end ErdosOverlap.Native6Grid
