module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck076
public import ErdosOverlap.Certificate.Native6Grid.Coefficients09

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0608 :
    completeCoefficientRowCheck factorRow row0608 608 coefficients0608 = true := by
  have hlen : coefficients0608.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0608 oddDots0608
      641 608 0 coefficients0608 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0608_checked oddSum0608_checked hlen hs

theorem coefficientCheck0609 :
    completeCoefficientRowCheck factorRow row0609 609 coefficients0609 = true := by
  have hlen : coefficients0609.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0609 oddDots0609
      641 609 0 coefficients0609 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0609_checked oddSum0609_checked hlen hs

theorem coefficientCheck0610 :
    completeCoefficientRowCheck factorRow row0610 610 coefficients0610 = true := by
  have hlen : coefficients0610.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0610 oddDots0610
      641 610 0 coefficients0610 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0610_checked oddSum0610_checked hlen hs

theorem coefficientCheck0611 :
    completeCoefficientRowCheck factorRow row0611 611 coefficients0611 = true := by
  have hlen : coefficients0611.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0611 oddDots0611
      641 611 0 coefficients0611 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0611_checked oddSum0611_checked hlen hs

theorem coefficientCheck0612 :
    completeCoefficientRowCheck factorRow row0612 612 coefficients0612 = true := by
  have hlen : coefficients0612.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0612 oddDots0612
      641 612 0 coefficients0612 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0612_checked oddSum0612_checked hlen hs

theorem coefficientCheck0613 :
    completeCoefficientRowCheck factorRow row0613 613 coefficients0613 = true := by
  have hlen : coefficients0613.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0613 oddDots0613
      641 613 0 coefficients0613 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0613_checked oddSum0613_checked hlen hs

theorem coefficientCheck0614 :
    completeCoefficientRowCheck factorRow row0614 614 coefficients0614 = true := by
  have hlen : coefficients0614.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0614 oddDots0614
      641 614 0 coefficients0614 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0614_checked oddSum0614_checked hlen hs

theorem coefficientCheck0615 :
    completeCoefficientRowCheck factorRow row0615 615 coefficients0615 = true := by
  have hlen : coefficients0615.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0615 oddDots0615
      641 615 0 coefficients0615 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0615_checked oddSum0615_checked hlen hs


end
end ErdosOverlap.Native6Grid
