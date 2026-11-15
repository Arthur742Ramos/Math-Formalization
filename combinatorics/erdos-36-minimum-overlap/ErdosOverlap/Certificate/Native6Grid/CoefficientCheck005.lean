module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck005
public import ErdosOverlap.Certificate.Native6Grid.Coefficients00

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0040 :
    completeCoefficientRowCheck factorRow row0040 40 coefficients0040 = true := by
  have hlen : coefficients0040.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0040 oddDots0040
      641 40 0 coefficients0040 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0040_checked oddSum0040_checked hlen hs

theorem coefficientCheck0041 :
    completeCoefficientRowCheck factorRow row0041 41 coefficients0041 = true := by
  have hlen : coefficients0041.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0041 oddDots0041
      641 41 0 coefficients0041 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0041_checked oddSum0041_checked hlen hs

theorem coefficientCheck0042 :
    completeCoefficientRowCheck factorRow row0042 42 coefficients0042 = true := by
  have hlen : coefficients0042.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0042 oddDots0042
      641 42 0 coefficients0042 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0042_checked oddSum0042_checked hlen hs

theorem coefficientCheck0043 :
    completeCoefficientRowCheck factorRow row0043 43 coefficients0043 = true := by
  have hlen : coefficients0043.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0043 oddDots0043
      641 43 0 coefficients0043 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0043_checked oddSum0043_checked hlen hs

theorem coefficientCheck0044 :
    completeCoefficientRowCheck factorRow row0044 44 coefficients0044 = true := by
  have hlen : coefficients0044.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0044 oddDots0044
      641 44 0 coefficients0044 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0044_checked oddSum0044_checked hlen hs

theorem coefficientCheck0045 :
    completeCoefficientRowCheck factorRow row0045 45 coefficients0045 = true := by
  have hlen : coefficients0045.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0045 oddDots0045
      641 45 0 coefficients0045 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0045_checked oddSum0045_checked hlen hs

theorem coefficientCheck0046 :
    completeCoefficientRowCheck factorRow row0046 46 coefficients0046 = true := by
  have hlen : coefficients0046.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0046 oddDots0046
      641 46 0 coefficients0046 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0046_checked oddSum0046_checked hlen hs

theorem coefficientCheck0047 :
    completeCoefficientRowCheck factorRow row0047 47 coefficients0047 = true := by
  have hlen : coefficients0047.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0047 oddDots0047
      641 47 0 coefficients0047 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0047_checked oddSum0047_checked hlen hs


end
end ErdosOverlap.Native6Grid
