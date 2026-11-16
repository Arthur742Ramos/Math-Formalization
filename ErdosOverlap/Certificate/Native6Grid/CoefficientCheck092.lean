module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck092
public import ErdosOverlap.Certificate.Native6Grid.Coefficients11

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0736 :
    completeCoefficientRowCheck factorRow row0736 736 coefficients0736 = true := by
  have hlen : coefficients0736.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0736 oddDots0736
      641 736 0 coefficients0736 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0736_checked oddSum0736_checked hlen hs

theorem coefficientCheck0737 :
    completeCoefficientRowCheck factorRow row0737 737 coefficients0737 = true := by
  have hlen : coefficients0737.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0737 oddDots0737
      641 737 0 coefficients0737 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0737_checked oddSum0737_checked hlen hs

theorem coefficientCheck0738 :
    completeCoefficientRowCheck factorRow row0738 738 coefficients0738 = true := by
  have hlen : coefficients0738.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0738 oddDots0738
      641 738 0 coefficients0738 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0738_checked oddSum0738_checked hlen hs

theorem coefficientCheck0739 :
    completeCoefficientRowCheck factorRow row0739 739 coefficients0739 = true := by
  have hlen : coefficients0739.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0739 oddDots0739
      641 739 0 coefficients0739 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0739_checked oddSum0739_checked hlen hs

theorem coefficientCheck0740 :
    completeCoefficientRowCheck factorRow row0740 740 coefficients0740 = true := by
  have hlen : coefficients0740.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0740 oddDots0740
      641 740 0 coefficients0740 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0740_checked oddSum0740_checked hlen hs

theorem coefficientCheck0741 :
    completeCoefficientRowCheck factorRow row0741 741 coefficients0741 = true := by
  have hlen : coefficients0741.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0741 oddDots0741
      641 741 0 coefficients0741 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0741_checked oddSum0741_checked hlen hs

theorem coefficientCheck0742 :
    completeCoefficientRowCheck factorRow row0742 742 coefficients0742 = true := by
  have hlen : coefficients0742.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0742 oddDots0742
      641 742 0 coefficients0742 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0742_checked oddSum0742_checked hlen hs

theorem coefficientCheck0743 :
    completeCoefficientRowCheck factorRow row0743 743 coefficients0743 = true := by
  have hlen : coefficients0743.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0743 oddDots0743
      641 743 0 coefficients0743 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0743_checked oddSum0743_checked hlen hs


end
end ErdosOverlap.Native6Grid
