module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck124
public import ErdosOverlap.Certificate.Native6Grid.Coefficients15

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0992 :
    completeCoefficientRowCheck factorRow row0992 992 coefficients0992 = true := by
  have hlen : coefficients0992.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0992 oddDots0992
      641 992 0 coefficients0992 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0992_checked oddSum0992_checked hlen hs

theorem coefficientCheck0993 :
    completeCoefficientRowCheck factorRow row0993 993 coefficients0993 = true := by
  have hlen : coefficients0993.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0993 oddDots0993
      641 993 0 coefficients0993 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0993_checked oddSum0993_checked hlen hs

theorem coefficientCheck0994 :
    completeCoefficientRowCheck factorRow row0994 994 coefficients0994 = true := by
  have hlen : coefficients0994.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0994 oddDots0994
      641 994 0 coefficients0994 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0994_checked oddSum0994_checked hlen hs

theorem coefficientCheck0995 :
    completeCoefficientRowCheck factorRow row0995 995 coefficients0995 = true := by
  have hlen : coefficients0995.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0995 oddDots0995
      641 995 0 coefficients0995 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0995_checked oddSum0995_checked hlen hs

theorem coefficientCheck0996 :
    completeCoefficientRowCheck factorRow row0996 996 coefficients0996 = true := by
  have hlen : coefficients0996.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0996 oddDots0996
      641 996 0 coefficients0996 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0996_checked oddSum0996_checked hlen hs

theorem coefficientCheck0997 :
    completeCoefficientRowCheck factorRow row0997 997 coefficients0997 = true := by
  have hlen : coefficients0997.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0997 oddDots0997
      641 997 0 coefficients0997 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0997_checked oddSum0997_checked hlen hs

theorem coefficientCheck0998 :
    completeCoefficientRowCheck factorRow row0998 998 coefficients0998 = true := by
  have hlen : coefficients0998.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0998 oddDots0998
      641 998 0 coefficients0998 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0998_checked oddSum0998_checked hlen hs

theorem coefficientCheck0999 :
    completeCoefficientRowCheck factorRow row0999 999 coefficients0999 = true := by
  have hlen : coefficients0999.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0999 oddDots0999
      641 999 0 coefficients0999 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0999_checked oddSum0999_checked hlen hs


end
end ErdosOverlap.Native6Grid
