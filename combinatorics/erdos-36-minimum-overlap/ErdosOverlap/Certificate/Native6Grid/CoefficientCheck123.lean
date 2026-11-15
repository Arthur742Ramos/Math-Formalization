module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck123
public import ErdosOverlap.Certificate.Native6Grid.Coefficients15

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0984 :
    completeCoefficientRowCheck factorRow row0984 984 coefficients0984 = true := by
  have hlen : coefficients0984.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0984 oddDots0984
      641 984 0 coefficients0984 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0984_checked oddSum0984_checked hlen hs

theorem coefficientCheck0985 :
    completeCoefficientRowCheck factorRow row0985 985 coefficients0985 = true := by
  have hlen : coefficients0985.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0985 oddDots0985
      641 985 0 coefficients0985 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0985_checked oddSum0985_checked hlen hs

theorem coefficientCheck0986 :
    completeCoefficientRowCheck factorRow row0986 986 coefficients0986 = true := by
  have hlen : coefficients0986.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0986 oddDots0986
      641 986 0 coefficients0986 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0986_checked oddSum0986_checked hlen hs

theorem coefficientCheck0987 :
    completeCoefficientRowCheck factorRow row0987 987 coefficients0987 = true := by
  have hlen : coefficients0987.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0987 oddDots0987
      641 987 0 coefficients0987 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0987_checked oddSum0987_checked hlen hs

theorem coefficientCheck0988 :
    completeCoefficientRowCheck factorRow row0988 988 coefficients0988 = true := by
  have hlen : coefficients0988.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0988 oddDots0988
      641 988 0 coefficients0988 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0988_checked oddSum0988_checked hlen hs

theorem coefficientCheck0989 :
    completeCoefficientRowCheck factorRow row0989 989 coefficients0989 = true := by
  have hlen : coefficients0989.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0989 oddDots0989
      641 989 0 coefficients0989 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0989_checked oddSum0989_checked hlen hs

theorem coefficientCheck0990 :
    completeCoefficientRowCheck factorRow row0990 990 coefficients0990 = true := by
  have hlen : coefficients0990.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0990 oddDots0990
      641 990 0 coefficients0990 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0990_checked oddSum0990_checked hlen hs

theorem coefficientCheck0991 :
    completeCoefficientRowCheck factorRow row0991 991 coefficients0991 = true := by
  have hlen : coefficients0991.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0991 oddDots0991
      641 991 0 coefficients0991 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0991_checked oddSum0991_checked hlen hs


end
end ErdosOverlap.Native6Grid
