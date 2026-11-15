module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck007
public import ErdosOverlap.Certificate.Native6Grid.Coefficients00

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0056 :
    completeCoefficientRowCheck factorRow row0056 56 coefficients0056 = true := by
  have hlen : coefficients0056.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0056 oddDots0056
      641 56 0 coefficients0056 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0056_checked oddSum0056_checked hlen hs

theorem coefficientCheck0057 :
    completeCoefficientRowCheck factorRow row0057 57 coefficients0057 = true := by
  have hlen : coefficients0057.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0057 oddDots0057
      641 57 0 coefficients0057 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0057_checked oddSum0057_checked hlen hs

theorem coefficientCheck0058 :
    completeCoefficientRowCheck factorRow row0058 58 coefficients0058 = true := by
  have hlen : coefficients0058.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0058 oddDots0058
      641 58 0 coefficients0058 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0058_checked oddSum0058_checked hlen hs

theorem coefficientCheck0059 :
    completeCoefficientRowCheck factorRow row0059 59 coefficients0059 = true := by
  have hlen : coefficients0059.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0059 oddDots0059
      641 59 0 coefficients0059 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0059_checked oddSum0059_checked hlen hs

theorem coefficientCheck0060 :
    completeCoefficientRowCheck factorRow row0060 60 coefficients0060 = true := by
  have hlen : coefficients0060.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0060 oddDots0060
      641 60 0 coefficients0060 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0060_checked oddSum0060_checked hlen hs

theorem coefficientCheck0061 :
    completeCoefficientRowCheck factorRow row0061 61 coefficients0061 = true := by
  have hlen : coefficients0061.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0061 oddDots0061
      641 61 0 coefficients0061 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0061_checked oddSum0061_checked hlen hs

theorem coefficientCheck0062 :
    completeCoefficientRowCheck factorRow row0062 62 coefficients0062 = true := by
  have hlen : coefficients0062.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0062 oddDots0062
      641 62 0 coefficients0062 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0062_checked oddSum0062_checked hlen hs

theorem coefficientCheck0063 :
    completeCoefficientRowCheck factorRow row0063 63 coefficients0063 = true := by
  have hlen : coefficients0063.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0063 oddDots0063
      641 63 0 coefficients0063 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0063_checked oddSum0063_checked hlen hs


end
end ErdosOverlap.Native6Grid
