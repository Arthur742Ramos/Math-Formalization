module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck111
public import ErdosOverlap.Certificate.Native6Grid.Coefficients13

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0888 :
    completeCoefficientRowCheck factorRow row0888 888 coefficients0888 = true := by
  have hlen : coefficients0888.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0888 oddDots0888
      641 888 0 coefficients0888 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0888_checked oddSum0888_checked hlen hs

theorem coefficientCheck0889 :
    completeCoefficientRowCheck factorRow row0889 889 coefficients0889 = true := by
  have hlen : coefficients0889.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0889 oddDots0889
      641 889 0 coefficients0889 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0889_checked oddSum0889_checked hlen hs

theorem coefficientCheck0890 :
    completeCoefficientRowCheck factorRow row0890 890 coefficients0890 = true := by
  have hlen : coefficients0890.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0890 oddDots0890
      641 890 0 coefficients0890 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0890_checked oddSum0890_checked hlen hs

theorem coefficientCheck0891 :
    completeCoefficientRowCheck factorRow row0891 891 coefficients0891 = true := by
  have hlen : coefficients0891.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0891 oddDots0891
      641 891 0 coefficients0891 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0891_checked oddSum0891_checked hlen hs

theorem coefficientCheck0892 :
    completeCoefficientRowCheck factorRow row0892 892 coefficients0892 = true := by
  have hlen : coefficients0892.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0892 oddDots0892
      641 892 0 coefficients0892 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0892_checked oddSum0892_checked hlen hs

theorem coefficientCheck0893 :
    completeCoefficientRowCheck factorRow row0893 893 coefficients0893 = true := by
  have hlen : coefficients0893.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0893 oddDots0893
      641 893 0 coefficients0893 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0893_checked oddSum0893_checked hlen hs

theorem coefficientCheck0894 :
    completeCoefficientRowCheck factorRow row0894 894 coefficients0894 = true := by
  have hlen : coefficients0894.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0894 oddDots0894
      641 894 0 coefficients0894 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0894_checked oddSum0894_checked hlen hs

theorem coefficientCheck0895 :
    completeCoefficientRowCheck factorRow row0895 895 coefficients0895 = true := by
  have hlen : coefficients0895.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0895 oddDots0895
      641 895 0 coefficients0895 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0895_checked oddSum0895_checked hlen hs


end
end ErdosOverlap.Native6Grid
