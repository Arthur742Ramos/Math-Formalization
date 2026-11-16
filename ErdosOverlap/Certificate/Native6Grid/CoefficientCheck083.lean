module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck083
public import ErdosOverlap.Certificate.Native6Grid.Coefficients10

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0664 :
    completeCoefficientRowCheck factorRow row0664 664 coefficients0664 = true := by
  have hlen : coefficients0664.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0664 oddDots0664
      641 664 0 coefficients0664 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0664_checked oddSum0664_checked hlen hs

theorem coefficientCheck0665 :
    completeCoefficientRowCheck factorRow row0665 665 coefficients0665 = true := by
  have hlen : coefficients0665.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0665 oddDots0665
      641 665 0 coefficients0665 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0665_checked oddSum0665_checked hlen hs

theorem coefficientCheck0666 :
    completeCoefficientRowCheck factorRow row0666 666 coefficients0666 = true := by
  have hlen : coefficients0666.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0666 oddDots0666
      641 666 0 coefficients0666 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0666_checked oddSum0666_checked hlen hs

theorem coefficientCheck0667 :
    completeCoefficientRowCheck factorRow row0667 667 coefficients0667 = true := by
  have hlen : coefficients0667.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0667 oddDots0667
      641 667 0 coefficients0667 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0667_checked oddSum0667_checked hlen hs

theorem coefficientCheck0668 :
    completeCoefficientRowCheck factorRow row0668 668 coefficients0668 = true := by
  have hlen : coefficients0668.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0668 oddDots0668
      641 668 0 coefficients0668 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0668_checked oddSum0668_checked hlen hs

theorem coefficientCheck0669 :
    completeCoefficientRowCheck factorRow row0669 669 coefficients0669 = true := by
  have hlen : coefficients0669.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0669 oddDots0669
      641 669 0 coefficients0669 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0669_checked oddSum0669_checked hlen hs

theorem coefficientCheck0670 :
    completeCoefficientRowCheck factorRow row0670 670 coefficients0670 = true := by
  have hlen : coefficients0670.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0670 oddDots0670
      641 670 0 coefficients0670 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0670_checked oddSum0670_checked hlen hs

theorem coefficientCheck0671 :
    completeCoefficientRowCheck factorRow row0671 671 coefficients0671 = true := by
  have hlen : coefficients0671.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0671 oddDots0671
      641 671 0 coefficients0671 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0671_checked oddSum0671_checked hlen hs


end
end ErdosOverlap.Native6Grid
