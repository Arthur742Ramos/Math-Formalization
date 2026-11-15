module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck018
public import ErdosOverlap.Certificate.Native6Grid.Coefficients02

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0144 :
    completeCoefficientRowCheck factorRow row0144 144 coefficients0144 = true := by
  have hlen : coefficients0144.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0144 oddDots0144
      641 144 0 coefficients0144 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0144_checked oddSum0144_checked hlen hs

theorem coefficientCheck0145 :
    completeCoefficientRowCheck factorRow row0145 145 coefficients0145 = true := by
  have hlen : coefficients0145.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0145 oddDots0145
      641 145 0 coefficients0145 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0145_checked oddSum0145_checked hlen hs

theorem coefficientCheck0146 :
    completeCoefficientRowCheck factorRow row0146 146 coefficients0146 = true := by
  have hlen : coefficients0146.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0146 oddDots0146
      641 146 0 coefficients0146 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0146_checked oddSum0146_checked hlen hs

theorem coefficientCheck0147 :
    completeCoefficientRowCheck factorRow row0147 147 coefficients0147 = true := by
  have hlen : coefficients0147.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0147 oddDots0147
      641 147 0 coefficients0147 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0147_checked oddSum0147_checked hlen hs

theorem coefficientCheck0148 :
    completeCoefficientRowCheck factorRow row0148 148 coefficients0148 = true := by
  have hlen : coefficients0148.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0148 oddDots0148
      641 148 0 coefficients0148 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0148_checked oddSum0148_checked hlen hs

theorem coefficientCheck0149 :
    completeCoefficientRowCheck factorRow row0149 149 coefficients0149 = true := by
  have hlen : coefficients0149.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0149 oddDots0149
      641 149 0 coefficients0149 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0149_checked oddSum0149_checked hlen hs

theorem coefficientCheck0150 :
    completeCoefficientRowCheck factorRow row0150 150 coefficients0150 = true := by
  have hlen : coefficients0150.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0150 oddDots0150
      641 150 0 coefficients0150 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0150_checked oddSum0150_checked hlen hs

theorem coefficientCheck0151 :
    completeCoefficientRowCheck factorRow row0151 151 coefficients0151 = true := by
  have hlen : coefficients0151.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0151 oddDots0151
      641 151 0 coefficients0151 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0151_checked oddSum0151_checked hlen hs


end
end ErdosOverlap.Native6Grid
