module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck088
public import ErdosOverlap.Certificate.Native6Grid.Coefficients11

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0704 :
    completeCoefficientRowCheck factorRow row0704 704 coefficients0704 = true := by
  have hlen : coefficients0704.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0704 oddDots0704
      641 704 0 coefficients0704 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0704_checked oddSum0704_checked hlen hs

theorem coefficientCheck0705 :
    completeCoefficientRowCheck factorRow row0705 705 coefficients0705 = true := by
  have hlen : coefficients0705.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0705 oddDots0705
      641 705 0 coefficients0705 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0705_checked oddSum0705_checked hlen hs

theorem coefficientCheck0706 :
    completeCoefficientRowCheck factorRow row0706 706 coefficients0706 = true := by
  have hlen : coefficients0706.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0706 oddDots0706
      641 706 0 coefficients0706 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0706_checked oddSum0706_checked hlen hs

theorem coefficientCheck0707 :
    completeCoefficientRowCheck factorRow row0707 707 coefficients0707 = true := by
  have hlen : coefficients0707.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0707 oddDots0707
      641 707 0 coefficients0707 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0707_checked oddSum0707_checked hlen hs

theorem coefficientCheck0708 :
    completeCoefficientRowCheck factorRow row0708 708 coefficients0708 = true := by
  have hlen : coefficients0708.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0708 oddDots0708
      641 708 0 coefficients0708 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0708_checked oddSum0708_checked hlen hs

theorem coefficientCheck0709 :
    completeCoefficientRowCheck factorRow row0709 709 coefficients0709 = true := by
  have hlen : coefficients0709.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0709 oddDots0709
      641 709 0 coefficients0709 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0709_checked oddSum0709_checked hlen hs

theorem coefficientCheck0710 :
    completeCoefficientRowCheck factorRow row0710 710 coefficients0710 = true := by
  have hlen : coefficients0710.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0710 oddDots0710
      641 710 0 coefficients0710 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0710_checked oddSum0710_checked hlen hs

theorem coefficientCheck0711 :
    completeCoefficientRowCheck factorRow row0711 711 coefficients0711 = true := by
  have hlen : coefficients0711.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0711 oddDots0711
      641 711 0 coefficients0711 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0711_checked oddSum0711_checked hlen hs


end
end ErdosOverlap.Native6Grid
