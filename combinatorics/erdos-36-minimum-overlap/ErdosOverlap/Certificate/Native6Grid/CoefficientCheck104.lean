module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck104
public import ErdosOverlap.Certificate.Native6Grid.Coefficients13

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0832 :
    completeCoefficientRowCheck factorRow row0832 832 coefficients0832 = true := by
  have hlen : coefficients0832.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0832 oddDots0832
      641 832 0 coefficients0832 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0832_checked oddSum0832_checked hlen hs

theorem coefficientCheck0833 :
    completeCoefficientRowCheck factorRow row0833 833 coefficients0833 = true := by
  have hlen : coefficients0833.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0833 oddDots0833
      641 833 0 coefficients0833 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0833_checked oddSum0833_checked hlen hs

theorem coefficientCheck0834 :
    completeCoefficientRowCheck factorRow row0834 834 coefficients0834 = true := by
  have hlen : coefficients0834.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0834 oddDots0834
      641 834 0 coefficients0834 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0834_checked oddSum0834_checked hlen hs

theorem coefficientCheck0835 :
    completeCoefficientRowCheck factorRow row0835 835 coefficients0835 = true := by
  have hlen : coefficients0835.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0835 oddDots0835
      641 835 0 coefficients0835 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0835_checked oddSum0835_checked hlen hs

theorem coefficientCheck0836 :
    completeCoefficientRowCheck factorRow row0836 836 coefficients0836 = true := by
  have hlen : coefficients0836.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0836 oddDots0836
      641 836 0 coefficients0836 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0836_checked oddSum0836_checked hlen hs

theorem coefficientCheck0837 :
    completeCoefficientRowCheck factorRow row0837 837 coefficients0837 = true := by
  have hlen : coefficients0837.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0837 oddDots0837
      641 837 0 coefficients0837 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0837_checked oddSum0837_checked hlen hs

theorem coefficientCheck0838 :
    completeCoefficientRowCheck factorRow row0838 838 coefficients0838 = true := by
  have hlen : coefficients0838.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0838 oddDots0838
      641 838 0 coefficients0838 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0838_checked oddSum0838_checked hlen hs

theorem coefficientCheck0839 :
    completeCoefficientRowCheck factorRow row0839 839 coefficients0839 = true := by
  have hlen : coefficients0839.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0839 oddDots0839
      641 839 0 coefficients0839 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0839_checked oddSum0839_checked hlen hs


end
end ErdosOverlap.Native6Grid
