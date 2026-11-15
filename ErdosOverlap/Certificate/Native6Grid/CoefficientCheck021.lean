module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck021
public import ErdosOverlap.Certificate.Native6Grid.Coefficients02

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0168 :
    completeCoefficientRowCheck factorRow row0168 168 coefficients0168 = true := by
  have hlen : coefficients0168.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0168 oddDots0168
      641 168 0 coefficients0168 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0168_checked oddSum0168_checked hlen hs

theorem coefficientCheck0169 :
    completeCoefficientRowCheck factorRow row0169 169 coefficients0169 = true := by
  have hlen : coefficients0169.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0169 oddDots0169
      641 169 0 coefficients0169 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0169_checked oddSum0169_checked hlen hs

theorem coefficientCheck0170 :
    completeCoefficientRowCheck factorRow row0170 170 coefficients0170 = true := by
  have hlen : coefficients0170.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0170 oddDots0170
      641 170 0 coefficients0170 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0170_checked oddSum0170_checked hlen hs

theorem coefficientCheck0171 :
    completeCoefficientRowCheck factorRow row0171 171 coefficients0171 = true := by
  have hlen : coefficients0171.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0171 oddDots0171
      641 171 0 coefficients0171 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0171_checked oddSum0171_checked hlen hs

theorem coefficientCheck0172 :
    completeCoefficientRowCheck factorRow row0172 172 coefficients0172 = true := by
  have hlen : coefficients0172.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0172 oddDots0172
      641 172 0 coefficients0172 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0172_checked oddSum0172_checked hlen hs

theorem coefficientCheck0173 :
    completeCoefficientRowCheck factorRow row0173 173 coefficients0173 = true := by
  have hlen : coefficients0173.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0173 oddDots0173
      641 173 0 coefficients0173 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0173_checked oddSum0173_checked hlen hs

theorem coefficientCheck0174 :
    completeCoefficientRowCheck factorRow row0174 174 coefficients0174 = true := by
  have hlen : coefficients0174.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0174 oddDots0174
      641 174 0 coefficients0174 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0174_checked oddSum0174_checked hlen hs

theorem coefficientCheck0175 :
    completeCoefficientRowCheck factorRow row0175 175 coefficients0175 = true := by
  have hlen : coefficients0175.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0175 oddDots0175
      641 175 0 coefficients0175 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0175_checked oddSum0175_checked hlen hs


end
end ErdosOverlap.Native6Grid
