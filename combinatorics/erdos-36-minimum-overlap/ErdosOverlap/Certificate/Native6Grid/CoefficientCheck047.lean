module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck047
public import ErdosOverlap.Certificate.Native6Grid.Coefficients05

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0376 :
    completeCoefficientRowCheck factorRow row0376 376 coefficients0376 = true := by
  have hlen : coefficients0376.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0376 oddDots0376
      641 376 0 coefficients0376 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0376_checked oddSum0376_checked hlen hs

theorem coefficientCheck0377 :
    completeCoefficientRowCheck factorRow row0377 377 coefficients0377 = true := by
  have hlen : coefficients0377.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0377 oddDots0377
      641 377 0 coefficients0377 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0377_checked oddSum0377_checked hlen hs

theorem coefficientCheck0378 :
    completeCoefficientRowCheck factorRow row0378 378 coefficients0378 = true := by
  have hlen : coefficients0378.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0378 oddDots0378
      641 378 0 coefficients0378 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0378_checked oddSum0378_checked hlen hs

theorem coefficientCheck0379 :
    completeCoefficientRowCheck factorRow row0379 379 coefficients0379 = true := by
  have hlen : coefficients0379.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0379 oddDots0379
      641 379 0 coefficients0379 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0379_checked oddSum0379_checked hlen hs

theorem coefficientCheck0380 :
    completeCoefficientRowCheck factorRow row0380 380 coefficients0380 = true := by
  have hlen : coefficients0380.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0380 oddDots0380
      641 380 0 coefficients0380 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0380_checked oddSum0380_checked hlen hs

theorem coefficientCheck0381 :
    completeCoefficientRowCheck factorRow row0381 381 coefficients0381 = true := by
  have hlen : coefficients0381.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0381 oddDots0381
      641 381 0 coefficients0381 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0381_checked oddSum0381_checked hlen hs

theorem coefficientCheck0382 :
    completeCoefficientRowCheck factorRow row0382 382 coefficients0382 = true := by
  have hlen : coefficients0382.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0382 oddDots0382
      641 382 0 coefficients0382 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0382_checked oddSum0382_checked hlen hs

theorem coefficientCheck0383 :
    completeCoefficientRowCheck factorRow row0383 383 coefficients0383 = true := by
  have hlen : coefficients0383.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0383 oddDots0383
      641 383 0 coefficients0383 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0383_checked oddSum0383_checked hlen hs


end
end ErdosOverlap.Native6Grid
