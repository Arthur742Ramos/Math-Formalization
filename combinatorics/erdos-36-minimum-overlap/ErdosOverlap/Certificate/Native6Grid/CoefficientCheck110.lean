module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck110
public import ErdosOverlap.Certificate.Native6Grid.Coefficients13

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0880 :
    completeCoefficientRowCheck factorRow row0880 880 coefficients0880 = true := by
  have hlen : coefficients0880.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0880 oddDots0880
      641 880 0 coefficients0880 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0880_checked oddSum0880_checked hlen hs

theorem coefficientCheck0881 :
    completeCoefficientRowCheck factorRow row0881 881 coefficients0881 = true := by
  have hlen : coefficients0881.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0881 oddDots0881
      641 881 0 coefficients0881 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0881_checked oddSum0881_checked hlen hs

theorem coefficientCheck0882 :
    completeCoefficientRowCheck factorRow row0882 882 coefficients0882 = true := by
  have hlen : coefficients0882.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0882 oddDots0882
      641 882 0 coefficients0882 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0882_checked oddSum0882_checked hlen hs

theorem coefficientCheck0883 :
    completeCoefficientRowCheck factorRow row0883 883 coefficients0883 = true := by
  have hlen : coefficients0883.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0883 oddDots0883
      641 883 0 coefficients0883 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0883_checked oddSum0883_checked hlen hs

theorem coefficientCheck0884 :
    completeCoefficientRowCheck factorRow row0884 884 coefficients0884 = true := by
  have hlen : coefficients0884.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0884 oddDots0884
      641 884 0 coefficients0884 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0884_checked oddSum0884_checked hlen hs

theorem coefficientCheck0885 :
    completeCoefficientRowCheck factorRow row0885 885 coefficients0885 = true := by
  have hlen : coefficients0885.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0885 oddDots0885
      641 885 0 coefficients0885 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0885_checked oddSum0885_checked hlen hs

theorem coefficientCheck0886 :
    completeCoefficientRowCheck factorRow row0886 886 coefficients0886 = true := by
  have hlen : coefficients0886.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0886 oddDots0886
      641 886 0 coefficients0886 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0886_checked oddSum0886_checked hlen hs

theorem coefficientCheck0887 :
    completeCoefficientRowCheck factorRow row0887 887 coefficients0887 = true := by
  have hlen : coefficients0887.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0887 oddDots0887
      641 887 0 coefficients0887 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0887_checked oddSum0887_checked hlen hs


end
end ErdosOverlap.Native6Grid
