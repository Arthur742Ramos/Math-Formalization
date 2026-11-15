module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck107
public import ErdosOverlap.Certificate.Native6Grid.Coefficients13

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0856 :
    completeCoefficientRowCheck factorRow row0856 856 coefficients0856 = true := by
  have hlen : coefficients0856.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0856 oddDots0856
      641 856 0 coefficients0856 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0856_checked oddSum0856_checked hlen hs

theorem coefficientCheck0857 :
    completeCoefficientRowCheck factorRow row0857 857 coefficients0857 = true := by
  have hlen : coefficients0857.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0857 oddDots0857
      641 857 0 coefficients0857 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0857_checked oddSum0857_checked hlen hs

theorem coefficientCheck0858 :
    completeCoefficientRowCheck factorRow row0858 858 coefficients0858 = true := by
  have hlen : coefficients0858.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0858 oddDots0858
      641 858 0 coefficients0858 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0858_checked oddSum0858_checked hlen hs

theorem coefficientCheck0859 :
    completeCoefficientRowCheck factorRow row0859 859 coefficients0859 = true := by
  have hlen : coefficients0859.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0859 oddDots0859
      641 859 0 coefficients0859 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0859_checked oddSum0859_checked hlen hs

theorem coefficientCheck0860 :
    completeCoefficientRowCheck factorRow row0860 860 coefficients0860 = true := by
  have hlen : coefficients0860.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0860 oddDots0860
      641 860 0 coefficients0860 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0860_checked oddSum0860_checked hlen hs

theorem coefficientCheck0861 :
    completeCoefficientRowCheck factorRow row0861 861 coefficients0861 = true := by
  have hlen : coefficients0861.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0861 oddDots0861
      641 861 0 coefficients0861 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0861_checked oddSum0861_checked hlen hs

theorem coefficientCheck0862 :
    completeCoefficientRowCheck factorRow row0862 862 coefficients0862 = true := by
  have hlen : coefficients0862.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0862 oddDots0862
      641 862 0 coefficients0862 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0862_checked oddSum0862_checked hlen hs

theorem coefficientCheck0863 :
    completeCoefficientRowCheck factorRow row0863 863 coefficients0863 = true := by
  have hlen : coefficients0863.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0863 oddDots0863
      641 863 0 coefficients0863 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0863_checked oddSum0863_checked hlen hs


end
end ErdosOverlap.Native6Grid
