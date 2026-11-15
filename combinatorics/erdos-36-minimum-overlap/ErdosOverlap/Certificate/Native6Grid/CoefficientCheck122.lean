module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck122
public import ErdosOverlap.Certificate.Native6Grid.Coefficients15

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0976 :
    completeCoefficientRowCheck factorRow row0976 976 coefficients0976 = true := by
  have hlen : coefficients0976.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0976 oddDots0976
      641 976 0 coefficients0976 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0976_checked oddSum0976_checked hlen hs

theorem coefficientCheck0977 :
    completeCoefficientRowCheck factorRow row0977 977 coefficients0977 = true := by
  have hlen : coefficients0977.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0977 oddDots0977
      641 977 0 coefficients0977 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0977_checked oddSum0977_checked hlen hs

theorem coefficientCheck0978 :
    completeCoefficientRowCheck factorRow row0978 978 coefficients0978 = true := by
  have hlen : coefficients0978.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0978 oddDots0978
      641 978 0 coefficients0978 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0978_checked oddSum0978_checked hlen hs

theorem coefficientCheck0979 :
    completeCoefficientRowCheck factorRow row0979 979 coefficients0979 = true := by
  have hlen : coefficients0979.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0979 oddDots0979
      641 979 0 coefficients0979 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0979_checked oddSum0979_checked hlen hs

theorem coefficientCheck0980 :
    completeCoefficientRowCheck factorRow row0980 980 coefficients0980 = true := by
  have hlen : coefficients0980.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0980 oddDots0980
      641 980 0 coefficients0980 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0980_checked oddSum0980_checked hlen hs

theorem coefficientCheck0981 :
    completeCoefficientRowCheck factorRow row0981 981 coefficients0981 = true := by
  have hlen : coefficients0981.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0981 oddDots0981
      641 981 0 coefficients0981 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0981_checked oddSum0981_checked hlen hs

theorem coefficientCheck0982 :
    completeCoefficientRowCheck factorRow row0982 982 coefficients0982 = true := by
  have hlen : coefficients0982.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0982 oddDots0982
      641 982 0 coefficients0982 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0982_checked oddSum0982_checked hlen hs

theorem coefficientCheck0983 :
    completeCoefficientRowCheck factorRow row0983 983 coefficients0983 = true := by
  have hlen : coefficients0983.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0983 oddDots0983
      641 983 0 coefficients0983 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0983_checked oddSum0983_checked hlen hs


end
end ErdosOverlap.Native6Grid
