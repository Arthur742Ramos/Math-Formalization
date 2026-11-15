module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck097
public import ErdosOverlap.Certificate.Native6Grid.Coefficients12

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0776 :
    completeCoefficientRowCheck factorRow row0776 776 coefficients0776 = true := by
  have hlen : coefficients0776.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0776 oddDots0776
      641 776 0 coefficients0776 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0776_checked oddSum0776_checked hlen hs

theorem coefficientCheck0777 :
    completeCoefficientRowCheck factorRow row0777 777 coefficients0777 = true := by
  have hlen : coefficients0777.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0777 oddDots0777
      641 777 0 coefficients0777 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0777_checked oddSum0777_checked hlen hs

theorem coefficientCheck0778 :
    completeCoefficientRowCheck factorRow row0778 778 coefficients0778 = true := by
  have hlen : coefficients0778.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0778 oddDots0778
      641 778 0 coefficients0778 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0778_checked oddSum0778_checked hlen hs

theorem coefficientCheck0779 :
    completeCoefficientRowCheck factorRow row0779 779 coefficients0779 = true := by
  have hlen : coefficients0779.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0779 oddDots0779
      641 779 0 coefficients0779 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0779_checked oddSum0779_checked hlen hs

theorem coefficientCheck0780 :
    completeCoefficientRowCheck factorRow row0780 780 coefficients0780 = true := by
  have hlen : coefficients0780.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0780 oddDots0780
      641 780 0 coefficients0780 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0780_checked oddSum0780_checked hlen hs

theorem coefficientCheck0781 :
    completeCoefficientRowCheck factorRow row0781 781 coefficients0781 = true := by
  have hlen : coefficients0781.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0781 oddDots0781
      641 781 0 coefficients0781 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0781_checked oddSum0781_checked hlen hs

theorem coefficientCheck0782 :
    completeCoefficientRowCheck factorRow row0782 782 coefficients0782 = true := by
  have hlen : coefficients0782.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0782 oddDots0782
      641 782 0 coefficients0782 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0782_checked oddSum0782_checked hlen hs

theorem coefficientCheck0783 :
    completeCoefficientRowCheck factorRow row0783 783 coefficients0783 = true := by
  have hlen : coefficients0783.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0783 oddDots0783
      641 783 0 coefficients0783 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0783_checked oddSum0783_checked hlen hs


end
end ErdosOverlap.Native6Grid
