module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck073
public import ErdosOverlap.Certificate.Native6Grid.Coefficients09

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0584 :
    completeCoefficientRowCheck factorRow row0584 584 coefficients0584 = true := by
  have hlen : coefficients0584.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0584 oddDots0584
      641 584 0 coefficients0584 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0584_checked oddSum0584_checked hlen hs

theorem coefficientCheck0585 :
    completeCoefficientRowCheck factorRow row0585 585 coefficients0585 = true := by
  have hlen : coefficients0585.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0585 oddDots0585
      641 585 0 coefficients0585 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0585_checked oddSum0585_checked hlen hs

theorem coefficientCheck0586 :
    completeCoefficientRowCheck factorRow row0586 586 coefficients0586 = true := by
  have hlen : coefficients0586.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0586 oddDots0586
      641 586 0 coefficients0586 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0586_checked oddSum0586_checked hlen hs

theorem coefficientCheck0587 :
    completeCoefficientRowCheck factorRow row0587 587 coefficients0587 = true := by
  have hlen : coefficients0587.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0587 oddDots0587
      641 587 0 coefficients0587 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0587_checked oddSum0587_checked hlen hs

theorem coefficientCheck0588 :
    completeCoefficientRowCheck factorRow row0588 588 coefficients0588 = true := by
  have hlen : coefficients0588.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0588 oddDots0588
      641 588 0 coefficients0588 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0588_checked oddSum0588_checked hlen hs

theorem coefficientCheck0589 :
    completeCoefficientRowCheck factorRow row0589 589 coefficients0589 = true := by
  have hlen : coefficients0589.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0589 oddDots0589
      641 589 0 coefficients0589 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0589_checked oddSum0589_checked hlen hs

theorem coefficientCheck0590 :
    completeCoefficientRowCheck factorRow row0590 590 coefficients0590 = true := by
  have hlen : coefficients0590.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0590 oddDots0590
      641 590 0 coefficients0590 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0590_checked oddSum0590_checked hlen hs

theorem coefficientCheck0591 :
    completeCoefficientRowCheck factorRow row0591 591 coefficients0591 = true := by
  have hlen : coefficients0591.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0591 oddDots0591
      641 591 0 coefficients0591 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0591_checked oddSum0591_checked hlen hs


end
end ErdosOverlap.Native6Grid
