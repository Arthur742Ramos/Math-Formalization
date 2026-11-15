module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck048
public import ErdosOverlap.Certificate.Native6Grid.Coefficients06

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0384 :
    completeCoefficientRowCheck factorRow row0384 384 coefficients0384 = true := by
  have hlen : coefficients0384.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0384 oddDots0384
      641 384 0 coefficients0384 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0384_checked oddSum0384_checked hlen hs

theorem coefficientCheck0385 :
    completeCoefficientRowCheck factorRow row0385 385 coefficients0385 = true := by
  have hlen : coefficients0385.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0385 oddDots0385
      641 385 0 coefficients0385 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0385_checked oddSum0385_checked hlen hs

theorem coefficientCheck0386 :
    completeCoefficientRowCheck factorRow row0386 386 coefficients0386 = true := by
  have hlen : coefficients0386.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0386 oddDots0386
      641 386 0 coefficients0386 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0386_checked oddSum0386_checked hlen hs

theorem coefficientCheck0387 :
    completeCoefficientRowCheck factorRow row0387 387 coefficients0387 = true := by
  have hlen : coefficients0387.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0387 oddDots0387
      641 387 0 coefficients0387 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0387_checked oddSum0387_checked hlen hs

theorem coefficientCheck0388 :
    completeCoefficientRowCheck factorRow row0388 388 coefficients0388 = true := by
  have hlen : coefficients0388.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0388 oddDots0388
      641 388 0 coefficients0388 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0388_checked oddSum0388_checked hlen hs

theorem coefficientCheck0389 :
    completeCoefficientRowCheck factorRow row0389 389 coefficients0389 = true := by
  have hlen : coefficients0389.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0389 oddDots0389
      641 389 0 coefficients0389 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0389_checked oddSum0389_checked hlen hs

theorem coefficientCheck0390 :
    completeCoefficientRowCheck factorRow row0390 390 coefficients0390 = true := by
  have hlen : coefficients0390.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0390 oddDots0390
      641 390 0 coefficients0390 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0390_checked oddSum0390_checked hlen hs

theorem coefficientCheck0391 :
    completeCoefficientRowCheck factorRow row0391 391 coefficients0391 = true := by
  have hlen : coefficients0391.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0391 oddDots0391
      641 391 0 coefficients0391 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0391_checked oddSum0391_checked hlen hs


end
end ErdosOverlap.Native6Grid
