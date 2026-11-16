/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.FrontierGrid.Check00
public import ErdosOverlap.Certificate.FrontierGrid.Check01
public import ErdosOverlap.Certificate.FrontierGrid.Check02
public import ErdosOverlap.Certificate.FrontierGrid.Check03
public import ErdosOverlap.Certificate.FrontierGrid.Check04
public import ErdosOverlap.Certificate.FrontierGrid.Check05
public import ErdosOverlap.Certificate.FrontierGrid.Check06
public import ErdosOverlap.Certificate.FrontierGrid.Check07
public import ErdosOverlap.Certificate.FrontierGrid.Check08
public import ErdosOverlap.Certificate.FrontierGrid.Check09
public import ErdosOverlap.Certificate.FrontierGrid.Check10
public import ErdosOverlap.Certificate.FrontierGrid.Check11
public import ErdosOverlap.Certificate.FrontierGrid.Check12
public import ErdosOverlap.Certificate.FrontierGrid.Check13
public import ErdosOverlap.Certificate.FrontierGrid.Check14
public import ErdosOverlap.Certificate.FrontierGrid.Check15
public import ErdosOverlap.Certificate.FrontierGrid.Check16
public import ErdosOverlap.Certificate.FrontierGrid.Check17
public import ErdosOverlap.Certificate.FrontierGrid.Check18
public import ErdosOverlap.Certificate.FrontierGrid.Check19
public import ErdosOverlap.Certificate.FrontierGrid.Check20
public import ErdosOverlap.Certificate.FrontierGrid.Check21
public import ErdosOverlap.Certificate.FrontierGrid.Check22
public import ErdosOverlap.Certificate.FrontierGrid.Check23
public import ErdosOverlap.Certificate.FrontierGrid.Check24
public import ErdosOverlap.Certificate.FrontierGrid.Check25
public import ErdosOverlap.Certificate.FrontierGrid.Check26
public import ErdosOverlap.Certificate.FrontierGrid.Check27
public import ErdosOverlap.Certificate.FrontierGrid.Check28
public import ErdosOverlap.Certificate.FrontierGrid.Check29
public import ErdosOverlap.Certificate.FrontierGrid.Check30
public import ErdosOverlap.Certificate.FrontierGrid.Check31
public import ErdosOverlap.Certificate.FrontierGrid.Check32
public import ErdosOverlap.Certificate.FrontierGrid.Check33
public import ErdosOverlap.Certificate.FrontierGrid.Check34
public import ErdosOverlap.Certificate.FrontierGrid.Check35
public import ErdosOverlap.Certificate.FrontierGrid.Check36
public import ErdosOverlap.Certificate.FrontierGrid.Check37
public import ErdosOverlap.Certificate.FrontierGrid.Check38
public import ErdosOverlap.Certificate.FrontierGrid.Check39
public import ErdosOverlap.Certificate.FrontierGrid.Check40
public import ErdosOverlap.Certificate.FrontierGrid.Check41
public import ErdosOverlap.Certificate.FrontierGrid.Check42
public import ErdosOverlap.Certificate.FrontierGrid.Check43
public import ErdosOverlap.Certificate.FrontierGrid.Check44
public import ErdosOverlap.Certificate.FrontierGrid.Check45
public import ErdosOverlap.Certificate.FrontierGrid.Check46
public import ErdosOverlap.Certificate.FrontierGrid.Check47
public import ErdosOverlap.Certificate.FrontierGrid.Check48
public import ErdosOverlap.Certificate.FrontierGrid.Check49
public import ErdosOverlap.Certificate.FrontierGrid.Check50
public import ErdosOverlap.Certificate.FrontierGrid.Check51
public import ErdosOverlap.Certificate.FrontierGrid.Check52
public import ErdosOverlap.Certificate.FrontierGrid.Check53
public import ErdosOverlap.Certificate.FrontierGrid.Check54
public import ErdosOverlap.Certificate.FrontierGrid.Check55
public import ErdosOverlap.Certificate.FrontierGrid.Check56
public import ErdosOverlap.Certificate.FrontierGrid.Check57
public import ErdosOverlap.Certificate.FrontierGrid.Check58
public import ErdosOverlap.Certificate.FrontierGrid.Check59
public import ErdosOverlap.Certificate.FrontierGrid.Check60
public import ErdosOverlap.Certificate.FrontierGrid.Check61
public import ErdosOverlap.Certificate.FrontierGrid.Check62
public import ErdosOverlap.Certificate.FrontierGrid.Check63

namespace ErdosOverlap.FrontierGrid
open Numerics
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem initial_checked : initialRowCheck seeds (stateRow 0) = true := by
  decide +kernel

theorem transitions_checked (j : ℕ) (hj : j+1 < 1024) :
    transitionRowCheck seeds (stateRow j) (stateRow (j+1)) = true := by
  by_cases h032 : j < 512
  · by_cases h016 : j < 256
    · by_cases h008 : j < 128
      · by_cases h004 : j < 64
        · by_cases h002 : j < 32
          · by_cases h001 : j < 16
            · exact transitions_chunk00 j hj (by omega) (by omega)
            · exact transitions_chunk01 j hj (by omega) (by omega)
          · by_cases h003 : j < 48
            · exact transitions_chunk02 j hj (by omega) (by omega)
            · exact transitions_chunk03 j hj (by omega) (by omega)
        · by_cases h006 : j < 96
          · by_cases h005 : j < 80
            · exact transitions_chunk04 j hj (by omega) (by omega)
            · exact transitions_chunk05 j hj (by omega) (by omega)
          · by_cases h007 : j < 112
            · exact transitions_chunk06 j hj (by omega) (by omega)
            · exact transitions_chunk07 j hj (by omega) (by omega)
      · by_cases h012 : j < 192
        · by_cases h010 : j < 160
          · by_cases h009 : j < 144
            · exact transitions_chunk08 j hj (by omega) (by omega)
            · exact transitions_chunk09 j hj (by omega) (by omega)
          · by_cases h011 : j < 176
            · exact transitions_chunk10 j hj (by omega) (by omega)
            · exact transitions_chunk11 j hj (by omega) (by omega)
        · by_cases h014 : j < 224
          · by_cases h013 : j < 208
            · exact transitions_chunk12 j hj (by omega) (by omega)
            · exact transitions_chunk13 j hj (by omega) (by omega)
          · by_cases h015 : j < 240
            · exact transitions_chunk14 j hj (by omega) (by omega)
            · exact transitions_chunk15 j hj (by omega) (by omega)
    · by_cases h024 : j < 384
      · by_cases h020 : j < 320
        · by_cases h018 : j < 288
          · by_cases h017 : j < 272
            · exact transitions_chunk16 j hj (by omega) (by omega)
            · exact transitions_chunk17 j hj (by omega) (by omega)
          · by_cases h019 : j < 304
            · exact transitions_chunk18 j hj (by omega) (by omega)
            · exact transitions_chunk19 j hj (by omega) (by omega)
        · by_cases h022 : j < 352
          · by_cases h021 : j < 336
            · exact transitions_chunk20 j hj (by omega) (by omega)
            · exact transitions_chunk21 j hj (by omega) (by omega)
          · by_cases h023 : j < 368
            · exact transitions_chunk22 j hj (by omega) (by omega)
            · exact transitions_chunk23 j hj (by omega) (by omega)
      · by_cases h028 : j < 448
        · by_cases h026 : j < 416
          · by_cases h025 : j < 400
            · exact transitions_chunk24 j hj (by omega) (by omega)
            · exact transitions_chunk25 j hj (by omega) (by omega)
          · by_cases h027 : j < 432
            · exact transitions_chunk26 j hj (by omega) (by omega)
            · exact transitions_chunk27 j hj (by omega) (by omega)
        · by_cases h030 : j < 480
          · by_cases h029 : j < 464
            · exact transitions_chunk28 j hj (by omega) (by omega)
            · exact transitions_chunk29 j hj (by omega) (by omega)
          · by_cases h031 : j < 496
            · exact transitions_chunk30 j hj (by omega) (by omega)
            · exact transitions_chunk31 j hj (by omega) (by omega)
  · by_cases h048 : j < 768
    · by_cases h040 : j < 640
      · by_cases h036 : j < 576
        · by_cases h034 : j < 544
          · by_cases h033 : j < 528
            · exact transitions_chunk32 j hj (by omega) (by omega)
            · exact transitions_chunk33 j hj (by omega) (by omega)
          · by_cases h035 : j < 560
            · exact transitions_chunk34 j hj (by omega) (by omega)
            · exact transitions_chunk35 j hj (by omega) (by omega)
        · by_cases h038 : j < 608
          · by_cases h037 : j < 592
            · exact transitions_chunk36 j hj (by omega) (by omega)
            · exact transitions_chunk37 j hj (by omega) (by omega)
          · by_cases h039 : j < 624
            · exact transitions_chunk38 j hj (by omega) (by omega)
            · exact transitions_chunk39 j hj (by omega) (by omega)
      · by_cases h044 : j < 704
        · by_cases h042 : j < 672
          · by_cases h041 : j < 656
            · exact transitions_chunk40 j hj (by omega) (by omega)
            · exact transitions_chunk41 j hj (by omega) (by omega)
          · by_cases h043 : j < 688
            · exact transitions_chunk42 j hj (by omega) (by omega)
            · exact transitions_chunk43 j hj (by omega) (by omega)
        · by_cases h046 : j < 736
          · by_cases h045 : j < 720
            · exact transitions_chunk44 j hj (by omega) (by omega)
            · exact transitions_chunk45 j hj (by omega) (by omega)
          · by_cases h047 : j < 752
            · exact transitions_chunk46 j hj (by omega) (by omega)
            · exact transitions_chunk47 j hj (by omega) (by omega)
    · by_cases h056 : j < 896
      · by_cases h052 : j < 832
        · by_cases h050 : j < 800
          · by_cases h049 : j < 784
            · exact transitions_chunk48 j hj (by omega) (by omega)
            · exact transitions_chunk49 j hj (by omega) (by omega)
          · by_cases h051 : j < 816
            · exact transitions_chunk50 j hj (by omega) (by omega)
            · exact transitions_chunk51 j hj (by omega) (by omega)
        · by_cases h054 : j < 864
          · by_cases h053 : j < 848
            · exact transitions_chunk52 j hj (by omega) (by omega)
            · exact transitions_chunk53 j hj (by omega) (by omega)
          · by_cases h055 : j < 880
            · exact transitions_chunk54 j hj (by omega) (by omega)
            · exact transitions_chunk55 j hj (by omega) (by omega)
      · by_cases h060 : j < 960
        · by_cases h058 : j < 928
          · by_cases h057 : j < 912
            · exact transitions_chunk56 j hj (by omega) (by omega)
            · exact transitions_chunk57 j hj (by omega) (by omega)
          · by_cases h059 : j < 944
            · exact transitions_chunk58 j hj (by omega) (by omega)
            · exact transitions_chunk59 j hj (by omega) (by omega)
        · by_cases h062 : j < 992
          · by_cases h061 : j < 976
            · exact transitions_chunk60 j hj (by omega) (by omega)
            · exact transitions_chunk61 j hj (by omega) (by omega)
          · by_cases h063 : j < 1008
            · exact transitions_chunk62 j hj (by omega) (by omega)
            · exact transitions_chunk63 j hj (by omega) (by omega)

theorem coefficients_checked (j : ℕ) (hj : j < 1024) :
    completeCoefficientRowCheck factors (stateRow j) j (coefficientRow j) = true := by
  by_cases h032 : j < 512
  · by_cases h016 : j < 256
    · by_cases h008 : j < 128
      · by_cases h004 : j < 64
        · by_cases h002 : j < 32
          · by_cases h001 : j < 16
            · exact coefficients_chunk00 j (by omega) (by omega)
            · exact coefficients_chunk01 j (by omega) (by omega)
          · by_cases h003 : j < 48
            · exact coefficients_chunk02 j (by omega) (by omega)
            · exact coefficients_chunk03 j (by omega) (by omega)
        · by_cases h006 : j < 96
          · by_cases h005 : j < 80
            · exact coefficients_chunk04 j (by omega) (by omega)
            · exact coefficients_chunk05 j (by omega) (by omega)
          · by_cases h007 : j < 112
            · exact coefficients_chunk06 j (by omega) (by omega)
            · exact coefficients_chunk07 j (by omega) (by omega)
      · by_cases h012 : j < 192
        · by_cases h010 : j < 160
          · by_cases h009 : j < 144
            · exact coefficients_chunk08 j (by omega) (by omega)
            · exact coefficients_chunk09 j (by omega) (by omega)
          · by_cases h011 : j < 176
            · exact coefficients_chunk10 j (by omega) (by omega)
            · exact coefficients_chunk11 j (by omega) (by omega)
        · by_cases h014 : j < 224
          · by_cases h013 : j < 208
            · exact coefficients_chunk12 j (by omega) (by omega)
            · exact coefficients_chunk13 j (by omega) (by omega)
          · by_cases h015 : j < 240
            · exact coefficients_chunk14 j (by omega) (by omega)
            · exact coefficients_chunk15 j (by omega) (by omega)
    · by_cases h024 : j < 384
      · by_cases h020 : j < 320
        · by_cases h018 : j < 288
          · by_cases h017 : j < 272
            · exact coefficients_chunk16 j (by omega) (by omega)
            · exact coefficients_chunk17 j (by omega) (by omega)
          · by_cases h019 : j < 304
            · exact coefficients_chunk18 j (by omega) (by omega)
            · exact coefficients_chunk19 j (by omega) (by omega)
        · by_cases h022 : j < 352
          · by_cases h021 : j < 336
            · exact coefficients_chunk20 j (by omega) (by omega)
            · exact coefficients_chunk21 j (by omega) (by omega)
          · by_cases h023 : j < 368
            · exact coefficients_chunk22 j (by omega) (by omega)
            · exact coefficients_chunk23 j (by omega) (by omega)
      · by_cases h028 : j < 448
        · by_cases h026 : j < 416
          · by_cases h025 : j < 400
            · exact coefficients_chunk24 j (by omega) (by omega)
            · exact coefficients_chunk25 j (by omega) (by omega)
          · by_cases h027 : j < 432
            · exact coefficients_chunk26 j (by omega) (by omega)
            · exact coefficients_chunk27 j (by omega) (by omega)
        · by_cases h030 : j < 480
          · by_cases h029 : j < 464
            · exact coefficients_chunk28 j (by omega) (by omega)
            · exact coefficients_chunk29 j (by omega) (by omega)
          · by_cases h031 : j < 496
            · exact coefficients_chunk30 j (by omega) (by omega)
            · exact coefficients_chunk31 j (by omega) (by omega)
  · by_cases h048 : j < 768
    · by_cases h040 : j < 640
      · by_cases h036 : j < 576
        · by_cases h034 : j < 544
          · by_cases h033 : j < 528
            · exact coefficients_chunk32 j (by omega) (by omega)
            · exact coefficients_chunk33 j (by omega) (by omega)
          · by_cases h035 : j < 560
            · exact coefficients_chunk34 j (by omega) (by omega)
            · exact coefficients_chunk35 j (by omega) (by omega)
        · by_cases h038 : j < 608
          · by_cases h037 : j < 592
            · exact coefficients_chunk36 j (by omega) (by omega)
            · exact coefficients_chunk37 j (by omega) (by omega)
          · by_cases h039 : j < 624
            · exact coefficients_chunk38 j (by omega) (by omega)
            · exact coefficients_chunk39 j (by omega) (by omega)
      · by_cases h044 : j < 704
        · by_cases h042 : j < 672
          · by_cases h041 : j < 656
            · exact coefficients_chunk40 j (by omega) (by omega)
            · exact coefficients_chunk41 j (by omega) (by omega)
          · by_cases h043 : j < 688
            · exact coefficients_chunk42 j (by omega) (by omega)
            · exact coefficients_chunk43 j (by omega) (by omega)
        · by_cases h046 : j < 736
          · by_cases h045 : j < 720
            · exact coefficients_chunk44 j (by omega) (by omega)
            · exact coefficients_chunk45 j (by omega) (by omega)
          · by_cases h047 : j < 752
            · exact coefficients_chunk46 j (by omega) (by omega)
            · exact coefficients_chunk47 j (by omega) (by omega)
    · by_cases h056 : j < 896
      · by_cases h052 : j < 832
        · by_cases h050 : j < 800
          · by_cases h049 : j < 784
            · exact coefficients_chunk48 j (by omega) (by omega)
            · exact coefficients_chunk49 j (by omega) (by omega)
          · by_cases h051 : j < 816
            · exact coefficients_chunk50 j (by omega) (by omega)
            · exact coefficients_chunk51 j (by omega) (by omega)
        · by_cases h054 : j < 864
          · by_cases h053 : j < 848
            · exact coefficients_chunk52 j (by omega) (by omega)
            · exact coefficients_chunk53 j (by omega) (by omega)
          · by_cases h055 : j < 880
            · exact coefficients_chunk54 j (by omega) (by omega)
            · exact coefficients_chunk55 j (by omega) (by omega)
      · by_cases h060 : j < 960
        · by_cases h058 : j < 928
          · by_cases h057 : j < 912
            · exact coefficients_chunk56 j (by omega) (by omega)
            · exact coefficients_chunk57 j (by omega) (by omega)
          · by_cases h059 : j < 944
            · exact coefficients_chunk58 j (by omega) (by omega)
            · exact coefficients_chunk59 j (by omega) (by omega)
        · by_cases h062 : j < 992
          · by_cases h061 : j < 976
            · exact coefficients_chunk60 j (by omega) (by omega)
            · exact coefficients_chunk61 j (by omega) (by omega)
          · by_cases h063 : j < 1008
            · exact coefficients_chunk62 j (by omega) (by omega)
            · exact coefficients_chunk63 j (by omega) (by omega)

theorem stateRows_correct (j : ℕ) (hj : j < 1024) : RowCorrect seeds (stateRow j) j := by
  apply rowCorrect_of_checked_transitions seeds stateRow 1024 _ transitions_checked hj
  exact initial_checked

theorem trigRows_correct (j : ℕ) (hj : j < 1024) :
    RowTrigCorrect FrontierTrig.correctionTerms (stateRow j) j := by
  simpa only [seeds_terms] using (stateRows_correct j hj).trig seeds_checked

theorem cosine_uniform_error (j : ℕ) (hj : j < 1024) {u : ℝ} (hu : |u| ≤ 1) :
    |cosineSum FrontierTrig.correctionTerms ((taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ)*u) -
      polynomialValue (quantizedCoefficients (coefficientRow j)) u| ≤
      (1 / 1000000000000 : ℝ) := by
  exact completeCoefficientRowCheck_sound factors_correct (trigRows_correct j hj)
    (coefficients_checked j hj) remainder_checked hu

end
end ErdosOverlap.FrontierGrid
