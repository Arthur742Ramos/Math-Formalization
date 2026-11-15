module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck108
public import ErdosOverlap.Certificate.Native6Grid.Coefficients13

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0864 :
    completeCoefficientRowCheck factorRow row0864 864 coefficients0864 = true := by
  have hlen : coefficients0864.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0864 oddDots0864
      641 864 0 coefficients0864 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0864_checked oddSum0864_checked hlen hs

theorem coefficientCheck0865 :
    completeCoefficientRowCheck factorRow row0865 865 coefficients0865 = true := by
  have hlen : coefficients0865.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0865 oddDots0865
      641 865 0 coefficients0865 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0865_checked oddSum0865_checked hlen hs

theorem coefficientCheck0866 :
    completeCoefficientRowCheck factorRow row0866 866 coefficients0866 = true := by
  have hlen : coefficients0866.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0866 oddDots0866
      641 866 0 coefficients0866 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0866_checked oddSum0866_checked hlen hs

theorem coefficientCheck0867 :
    completeCoefficientRowCheck factorRow row0867 867 coefficients0867 = true := by
  have hlen : coefficients0867.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0867 oddDots0867
      641 867 0 coefficients0867 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0867_checked oddSum0867_checked hlen hs

theorem coefficientCheck0868 :
    completeCoefficientRowCheck factorRow row0868 868 coefficients0868 = true := by
  have hlen : coefficients0868.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0868 oddDots0868
      641 868 0 coefficients0868 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0868_checked oddSum0868_checked hlen hs

theorem coefficientCheck0869 :
    completeCoefficientRowCheck factorRow row0869 869 coefficients0869 = true := by
  have hlen : coefficients0869.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0869 oddDots0869
      641 869 0 coefficients0869 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0869_checked oddSum0869_checked hlen hs

theorem coefficientCheck0870 :
    completeCoefficientRowCheck factorRow row0870 870 coefficients0870 = true := by
  have hlen : coefficients0870.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0870 oddDots0870
      641 870 0 coefficients0870 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0870_checked oddSum0870_checked hlen hs

theorem coefficientCheck0871 :
    completeCoefficientRowCheck factorRow row0871 871 coefficients0871 = true := by
  have hlen : coefficients0871.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0871 oddDots0871
      641 871 0 coefficients0871 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0871_checked oddSum0871_checked hlen hs


end
end ErdosOverlap.Native6Grid
