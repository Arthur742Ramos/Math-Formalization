module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck077
public import ErdosOverlap.Certificate.Native6Grid.Coefficients09

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0616 :
    completeCoefficientRowCheck factorRow row0616 616 coefficients0616 = true := by
  have hlen : coefficients0616.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0616 oddDots0616
      641 616 0 coefficients0616 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0616_checked oddSum0616_checked hlen hs

theorem coefficientCheck0617 :
    completeCoefficientRowCheck factorRow row0617 617 coefficients0617 = true := by
  have hlen : coefficients0617.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0617 oddDots0617
      641 617 0 coefficients0617 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0617_checked oddSum0617_checked hlen hs

theorem coefficientCheck0618 :
    completeCoefficientRowCheck factorRow row0618 618 coefficients0618 = true := by
  have hlen : coefficients0618.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0618 oddDots0618
      641 618 0 coefficients0618 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0618_checked oddSum0618_checked hlen hs

theorem coefficientCheck0619 :
    completeCoefficientRowCheck factorRow row0619 619 coefficients0619 = true := by
  have hlen : coefficients0619.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0619 oddDots0619
      641 619 0 coefficients0619 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0619_checked oddSum0619_checked hlen hs

theorem coefficientCheck0620 :
    completeCoefficientRowCheck factorRow row0620 620 coefficients0620 = true := by
  have hlen : coefficients0620.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0620 oddDots0620
      641 620 0 coefficients0620 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0620_checked oddSum0620_checked hlen hs

theorem coefficientCheck0621 :
    completeCoefficientRowCheck factorRow row0621 621 coefficients0621 = true := by
  have hlen : coefficients0621.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0621 oddDots0621
      641 621 0 coefficients0621 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0621_checked oddSum0621_checked hlen hs

theorem coefficientCheck0622 :
    completeCoefficientRowCheck factorRow row0622 622 coefficients0622 = true := by
  have hlen : coefficients0622.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0622 oddDots0622
      641 622 0 coefficients0622 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0622_checked oddSum0622_checked hlen hs

theorem coefficientCheck0623 :
    completeCoefficientRowCheck factorRow row0623 623 coefficients0623 = true := by
  have hlen : coefficients0623.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0623 oddDots0623
      641 623 0 coefficients0623 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0623_checked oddSum0623_checked hlen hs


end
end ErdosOverlap.Native6Grid
