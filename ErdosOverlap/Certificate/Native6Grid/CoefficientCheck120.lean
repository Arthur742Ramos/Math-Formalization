module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck120
public import ErdosOverlap.Certificate.Native6Grid.Coefficients15

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0960 :
    completeCoefficientRowCheck factorRow row0960 960 coefficients0960 = true := by
  have hlen : coefficients0960.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0960 oddDots0960
      641 960 0 coefficients0960 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0960_checked oddSum0960_checked hlen hs

theorem coefficientCheck0961 :
    completeCoefficientRowCheck factorRow row0961 961 coefficients0961 = true := by
  have hlen : coefficients0961.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0961 oddDots0961
      641 961 0 coefficients0961 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0961_checked oddSum0961_checked hlen hs

theorem coefficientCheck0962 :
    completeCoefficientRowCheck factorRow row0962 962 coefficients0962 = true := by
  have hlen : coefficients0962.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0962 oddDots0962
      641 962 0 coefficients0962 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0962_checked oddSum0962_checked hlen hs

theorem coefficientCheck0963 :
    completeCoefficientRowCheck factorRow row0963 963 coefficients0963 = true := by
  have hlen : coefficients0963.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0963 oddDots0963
      641 963 0 coefficients0963 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0963_checked oddSum0963_checked hlen hs

theorem coefficientCheck0964 :
    completeCoefficientRowCheck factorRow row0964 964 coefficients0964 = true := by
  have hlen : coefficients0964.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0964 oddDots0964
      641 964 0 coefficients0964 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0964_checked oddSum0964_checked hlen hs

theorem coefficientCheck0965 :
    completeCoefficientRowCheck factorRow row0965 965 coefficients0965 = true := by
  have hlen : coefficients0965.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0965 oddDots0965
      641 965 0 coefficients0965 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0965_checked oddSum0965_checked hlen hs

theorem coefficientCheck0966 :
    completeCoefficientRowCheck factorRow row0966 966 coefficients0966 = true := by
  have hlen : coefficients0966.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0966 oddDots0966
      641 966 0 coefficients0966 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0966_checked oddSum0966_checked hlen hs

theorem coefficientCheck0967 :
    completeCoefficientRowCheck factorRow row0967 967 coefficients0967 = true := by
  have hlen : coefficients0967.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0967 oddDots0967
      641 967 0 coefficients0967 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0967_checked oddSum0967_checked hlen hs


end
end ErdosOverlap.Native6Grid
