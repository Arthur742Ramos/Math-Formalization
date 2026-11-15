/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.IntegerOuterBindings
public import ErdosOverlap.Numerics.OuterTruncation
public import ErdosOverlap.Certificate.OuterData14
public import ErdosOverlap.Certificate.Outer90.IntegerBasis00
public import ErdosOverlap.Certificate.Outer90.IntegerBasis01
public import ErdosOverlap.Certificate.Outer90.IntegerBasis02
public import ErdosOverlap.Certificate.Outer90.IntegerBasis03
public import ErdosOverlap.Certificate.Outer90.IntegerBasis04
public import ErdosOverlap.Certificate.Outer90.IntegerBasis05
public import ErdosOverlap.Certificate.Outer90.IntegerBasis06
public import ErdosOverlap.Certificate.Outer90.IntegerBasis07
public import ErdosOverlap.Certificate.Outer90.IntegerBasis08
public import ErdosOverlap.Certificate.Outer90.IntegerBasis09
public import ErdosOverlap.Certificate.Outer90.IntegerBasis10
public import ErdosOverlap.Certificate.Outer90.IntegerBasis11
public import ErdosOverlap.Certificate.Outer90.IntegerBasis12
public import ErdosOverlap.Certificate.Outer90.IntegerBasis13
public import ErdosOverlap.Certificate.Outer90.IntegerBasis14
public import ErdosOverlap.Certificate.Outer90.IntegerBasis15
public import ErdosOverlap.Certificate.Outer90.IntegerBasis16
public import ErdosOverlap.Certificate.Outer90.IntegerBasis17
public import ErdosOverlap.Certificate.Outer90.IntegerBasis18
public import ErdosOverlap.Certificate.Outer90.IntegerBasis19
public import ErdosOverlap.Certificate.Outer90.IntegerBasis20
public import ErdosOverlap.Certificate.Outer90.IntegerBasis21
public import ErdosOverlap.Certificate.Outer90.IntegerBasis22
public import ErdosOverlap.Certificate.Outer90.IntegerBasis23
public import ErdosOverlap.Certificate.Outer90.IntegerBasis24
public import ErdosOverlap.Certificate.Outer90.IntegerBasis25
public import ErdosOverlap.Certificate.Outer90.IntegerBasis26
public import ErdosOverlap.Certificate.Outer90.IntegerBasis27
public import ErdosOverlap.Certificate.Outer90.IntegerBasis28
public import ErdosOverlap.Certificate.Outer90.IntegerBasis29
public import ErdosOverlap.Certificate.Outer90.IntegerBasis30
public import ErdosOverlap.Certificate.Outer90.IntegerBasis31

/-! # Exact integer weighted outer models for source bin 170

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin170

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 433914575931274400)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 1730085521117412000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 1177334671181919600)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 485104369712569400)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 854984441054060000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 698197152425804900)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 494189453854217350)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 346167545318472050)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 185696673565127170)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 106285943458599520)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial170.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial170.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 8875521424238652000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 3428738360981312700)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1132420125541571000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 909789128320720300)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 454002552179879700)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 170905341792355580)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 3161245112077798)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 38187314865678833)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 39429043628389625)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial170.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial170.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 8875521424238652000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 3428738360981312700)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1132420125541571000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 909789128320720300)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 454002552179879700)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 170905341792355580)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 3161245112077798)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 38187314865678833)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 39429043628389625)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial170.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial170.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial170.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 3998183360313108592975932767558580), (Int.ofNat 3800373641864027267014736469658636), (Int.ofNat 390985130874147921387430256214220), (Int.negOfNat 89211370878094706767281056958966), (Int.negOfNat 12169885200977970011040051814901), (Int.ofNat 1507990262224765631060322871346), (Int.ofNat 208120374109108608022687304746), (Int.negOfNat 17027871773795329296298095652), (Int.negOfNat 2203856561347582124891547732), (Int.ofNat 133696270137898410333965043), (Int.ofNat 15769004732119535664601703), (Int.negOfNat 762520124864596263250394), (Int.negOfNat 81132253501641405289895), (Int.ofNat 3273328734450005622161), (Int.ofNat 314508892404325449959), (Int.negOfNat 10748431750885193851), (Int.negOfNat 991887967494141353), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-199909168015655429648796638377929/562949953421312000000000000000000), (950093410466006816753684117414659/2814749767106560000000000000000000), (19549256543707396069371512810711/562949953421312000000000000000000), (-44605685439047353383640528479483/5629499534213120000000000000000000), (-12169885200977970011040051814901/11258999068426240000000000000000000), (753995131112382815530161435673/5629499534213120000000000000000000), (104060187054554304011343652373/5629499534213120000000000000000000), (-4256967943448832324074523913/2814749767106560000000000000000000), (-550964140336895531222886933/2814749767106560000000000000000000), (133696270137898410333965043/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial170.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial170.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial170.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial170 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 4317009691674838412103852787729004), (Int.ofNat 4055432883278873904399469404360368), (Int.negOfNat 280392864830735283010908280349589), (Int.negOfNat 105515717302235263262060941773719), (Int.ofNat 8871108690959209121785330403938), (Int.ofNat 1955046995797153614552137991987), (Int.negOfNat 149419298495385382341577365250), (Int.negOfNat 23506710444557355156139831116), (Int.ofNat 1575530636309327347023323523), (Int.ofNat 191448908082451108992240616), (Int.negOfNat 11344652630099326332128836), (Int.negOfNat 1113591653533051867158809), (Int.ofNat 58960229038655343642687), (Int.ofNat 4829050540564764492261), (Int.negOfNat 230953165372536178490), (Int.negOfNat 16011878325630525131), (Int.ofNat 733794788396086477), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(1079252422918709603025963196932251/2814749767106560000000000000000000), (253464555204929619024966837772523/703687441776640000000000000000000), (-280392864830735283010908280349589/11258999068426240000000000000000000), (-105515717302235263262060941773719/11258999068426240000000000000000000), (4435554345479604560892665201969/5629499534213120000000000000000000), (1955046995797153614552137991987/11258999068426240000000000000000000), (-597677193981541529366309461/45035996273704960000000000000000), (-5876677611139338789034957779/2814749767106560000000000000000000), (1575530636309327347023323523/11258999068426240000000000000000000), (23931113510306388624030077/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial170.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial170.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial170.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial170 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 10654593546301848501135785274719905), (Int.ofNat 2070718032204371841414333022557759), (Int.negOfNat 592285785185684071415493631260313), (Int.ofNat 10223331993141700342105613678757), (Int.ofNat 15220511752244008323419962189596), (Int.negOfNat 837869955975206989847806666353), (Int.negOfNat 223646014623592207338882461871), (Int.ofNat 14401413805582678947640441086), (Int.ofNat 2120634581906382567685390804), (Int.negOfNat 140115681676313774737648654), (Int.negOfNat 14029843306286740988463708), (Int.ofNat 907617307209315417230353), (Int.ofNat 68207720735053000088610), (Int.negOfNat 4225976628855836540662), (Int.negOfNat 252883518916993362485), (Int.ofNat 14869987553825554753), (Int.ofNat 712459180746732418), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(2130918709260369700227157054943981/2251799813685248000000000000000000), (2070718032204371841414333022557759/11258999068426240000000000000000000), (-592285785185684071415493631260313/11258999068426240000000000000000000), (10223331993141700342105613678757/11258999068426240000000000000000000), (3805127938061002080854990547399/2814749767106560000000000000000000), (-837869955975206989847806666353/11258999068426240000000000000000000), (-223646014623592207338882461871/11258999068426240000000000000000000), (7200706902791339473820220543/5629499534213120000000000000000000), (530158645476595641921347701/2814749767106560000000000000000000), (-70057840838156887368824327/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial170.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial170.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial170.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial170 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 12713378387988983033314582470981495), (Int.ofNat 209581973602019151188917956369537), (Int.negOfNat 273658088021041840245515943569011), (Int.ofNat 73630098746324395770068042417665), (Int.negOfNat 877729166715007426600843450586), (Int.negOfNat 1725318766723392877691611875545), (Int.ofNat 90558600575196652571212949186), (Int.ofNat 20659648040858408871106243019), (Int.negOfNat 1397176643144821738315803114), (Int.negOfNat 160006916649061348205683655), (Int.ofNat 11910032545097582425444239), (Int.ofNat 879086906508345578456065), (Int.negOfNat 67718549859627089253570), (Int.negOfNat 3616366680191321996766), (Int.ofNat 279110210781431724554), (Int.ofNat 11285855562014315708), (Int.negOfNat 852081919281255352), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(2542675677597796606662916494196299/2251799813685248000000000000000000), (209581973602019151188917956369537/11258999068426240000000000000000000), (-273658088021041840245515943569011/11258999068426240000000000000000000), (14726019749264879154013608483533/2251799813685248000000000000000000), (-438864583357503713300421725293/5629499534213120000000000000000000), (-345063753344678575538322375109/2251799813685248000000000000000000), (45279300287598326285606474593/5629499534213120000000000000000000), (20659648040858408871106243019/11258999068426240000000000000000000), (-698588321572410869157901557/5629499534213120000000000000000000), (-32001383329812269641136731/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial170.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial170.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial170.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial170 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 12565711184640227938848453102255159), (Int.negOfNat 142689560396611172838396682586253), (Int.ofNat 41564714864539522864764523911041), (Int.ofNat 20501965362481941603774070297949), (Int.negOfNat 8935075091753525454653878753465), (Int.ofNat 262578071963088206800363954780), (Int.ofNat 164237033407690942128581657513), (Int.negOfNat 10638224928148305775239191243), (Int.negOfNat 1598326997825260860822130828), (Int.ofNat 131218748923370026493306191), (Int.ofNat 10183895839067760116480635), (Int.negOfNat 945387972849727191467199), (Int.negOfNat 46616437297019751202779), (Int.ofNat 4656764009075640609653), (Int.ofNat 161976966783221117374), (Int.negOfNat 17105559994476340803), (Int.negOfNat 393601350370933858), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(12565711184640227938848453102255159/11258999068426240000000000000000000), (-142689560396611172838396682586253/11258999068426240000000000000000000), (41564714864539522864764523911041/11258999068426240000000000000000000), (20501965362481941603774070297949/11258999068426240000000000000000000), (-1787015018350705090930775750693/2251799813685248000000000000000000), (13128903598154410340018197739/562949953421312000000000000000000), (164237033407690942128581657513/11258999068426240000000000000000000), (-10638224928148305775239191243/11258999068426240000000000000000000), (-399581749456315215205532707/2814749767106560000000000000000000), (131218748923370026493306191/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial170.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial170.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial170.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial170 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 12484863774115341770928592612176645), (Int.ofNat 30150562295736435880325027858734), (Int.ofNat 1237740396480983196033429351208), (Int.negOfNat 22201070920825954257479520945194), (Int.negOfNat 601975226753677624991015135201), (Int.ofNat 939387645350256579687286557818), (Int.negOfNat 56945481370139338200042968874), (Int.negOfNat 13159381990469061644120623167), (Int.ofNat 1187746370341436145496101573), (Int.ofNat 102761279312507613291475147), (Int.negOfNat 11400716116715774624925139), (Int.negOfNat 531463103027204668877993), (Int.ofNat 68794892950691062072486), (Int.ofNat 1986609301263585536256), (Int.negOfNat 293363606793587731535), (Int.negOfNat 5558680038913114745), (Int.ofNat 970369050166424227), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(2496972754823068354185718522435329/2251799813685248000000000000000000), (15075281147868217940162513929367/5629499534213120000000000000000000), (154717549560122899504178668901/1407374883553280000000000000000000), (-11100535460412977128739760472597/5629499534213120000000000000000000), (-601975226753677624991015135201/11258999068426240000000000000000000), (469693822675128289843643278909/5629499534213120000000000000000000), (-28472740685069669100021484437/5629499534213120000000000000000000), (-13159381990469061644120623167/11258999068426240000000000000000000), (1187746370341436145496101573/11258999068426240000000000000000000), (102761279312507613291475147/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial170.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial170.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial170.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial170 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 12387951389458117715357505891489704), (Int.negOfNat 190862040158021369604518886228333), (Int.negOfNat 91314581391639626186467137543260), (Int.negOfNat 3430469512716024491532796719213), (Int.ofNat 3268615986526081433896523528135), (Int.negOfNat 210399396941882069219628336653), (Int.negOfNat 80984606350413667238947397674), (Int.ofNat 8720594227190096791060810843), (Int.ofNat 852609486248836998385930751), (Int.negOfNat 117565400632871569934332865), (Int.negOfNat 5137781991909286380716592), (Int.ofNat 893972982311069513634646), (Int.ofNat 20220690024682046238597), (Int.negOfNat 4545746772835661685531), (Int.negOfNat 54760585625771531039), (Int.ofNat 17136555478698357203), (Int.ofNat 74743519995135298), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(1548493923682264714419688236436213/1407374883553280000000000000000000), (-190862040158021369604518886228333/11258999068426240000000000000000000), (-4565729069581981309323356877163/562949953421312000000000000000000), (-3430469512716024491532796719213/11258999068426240000000000000000000), (653723197305216286779304705627/2251799813685248000000000000000000), (-210399396941882069219628336653/11258999068426240000000000000000000), (-40492303175206833619473698837/5629499534213120000000000000000000), (8720594227190096791060810843/11258999068426240000000000000000000), (852609486248836998385930751/11258999068426240000000000000000000), (-23513080126574313986866573/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial170.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial170.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial170.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial170 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 11655178213358973714729453427089363), (Int.negOfNat 520578239841337644459377293536500), (Int.negOfNat 62905876454407556371341955237927), (Int.ofNat 7084104670323627344521618224327), (Int.negOfNat 802190606516626152348530034500), (Int.negOfNat 319178322185278994869335459444), (Int.ofNat 53743371794892563697154242914), (Int.ofNat 5237293525782778682373123254), (Int.negOfNat 1032350083362850175416261867), (Int.negOfNat 38338259812979929983667584), (Int.ofNat 10139853917220986191584893), (Int.ofNat 146262103402897227468209), (Int.negOfNat 62681382079640743441632), (Int.negOfNat 228880729583244956281), (Int.ofNat 270769307284314147154), (Int.negOfNat 665528241322753648), (Int.negOfNat 982370237592993582), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(11655178213358973714729453427089363/11258999068426240000000000000000000), (-1041156479682675288918754587073/22517998136852480000000000000000), (-62905876454407556371341955237927/11258999068426240000000000000000000), (7084104670323627344521618224327/11258999068426240000000000000000000), (-1604381213033252304697060069/22517998136852480000000000000000), (-79794580546319748717333864861/2814749767106560000000000000000000), (26871685897446281848577121457/5629499534213120000000000000000000), (2618646762891389341186561627/5629499534213120000000000000000000), (-1032350083362850175416261867/11258999068426240000000000000000000), (-299517654788905702997403/87960930222080000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial170.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial170.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial170.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial170 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 10399858776273621810127860472599110), (Int.negOfNat 726825236298290892593949819826076), (Int.negOfNat 50680096270473649528243137033483), (Int.negOfNat 2469810814695628533631089306981), (Int.negOfNat 479039952837015813353832342637), (Int.ofNat 305823652336397471803483220580), (Int.ofNat 18354555031550889619224927252), (Int.negOfNat 7794807269469462733581656536), (Int.negOfNat 161091357881467488412720815), (Int.ofNat 99704956637971151126926770), (Int.ofNat 164405757041906803350389), (Int.negOfNat 762045632943302168542129), (Int.ofNat 5866527143828550693024), (Int.ofNat 3916018997253143666049), (Int.negOfNat 49606286276093841046), (Int.negOfNat 14796417889663553896), (Int.ofNat 216686454178842992), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(1039985877627362181012786047259911/1125899906842624000000000000000000), (-181706309074572723148487454956519/2814749767106560000000000000000000), (-50680096270473649528243137033483/11258999068426240000000000000000000), (-2469810814695628533631089306981/11258999068426240000000000000000000), (-479039952837015813353832342637/11258999068426240000000000000000000), (15291182616819873590174161029/562949953421312000000000000000000), (4588638757887722404806231813/2814749767106560000000000000000000), (-974350908683682841697707067/1407374883553280000000000000000000), (-32218271576293497682544163/2251799813685248000000000000000000), (9970495663797115112692677/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial170.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial170.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial170.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial170 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 8726036577977978071469600613863657), (Int.negOfNat 949957372162575912150016671561208), (Int.negOfNat 53210853829602572088087575090778), (Int.ofNat 4721872316982142985208928007989), (Int.ofNat 1691620970371850292687336740951), (Int.negOfNat 19262952283142615501049760238), (Int.negOfNat 51392241426083373694884491196), (Int.ofNat 654649545840420953702279819), (Int.ofNat 844759832023169154784734103), (Int.negOfNat 16801997083335448492262401), (Int.negOfNat 8077623930075645680604016), (Int.ofNat 197824093838656371222634), (Int.ofNat 49947645575745254811093), (Int.negOfNat 1347888757903267794837), (Int.negOfNat 216933604129914096139), (Int.ofNat 6245169898109661801), (Int.ofNat 848656437932573792), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(8726036577977978071469600613863657/11258999068426240000000000000000000), (-118744671520321989018752083945151/1407374883553280000000000000000000), (-26605426914801286044043787545389/5629499534213120000000000000000000), (4721872316982142985208928007989/11258999068426240000000000000000000), (1691620970371850292687336740951/11258999068426240000000000000000000), (-9631476141571307750524880119/5629499534213120000000000000000000), (-12848060356520843423721122799/2814749767106560000000000000000000), (654649545840420953702279819/11258999068426240000000000000000000), (844759832023169154784734103/11258999068426240000000000000000000), (-16801997083335448492262401/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial170.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial170.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial170.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial170 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 6674497589396251752442500007361242), (Int.negOfNat 1062333186349677761607142085973282), (Int.ofNat 3636022215491386411214002852600), (Int.ofNat 10941016844404981513922000157215), (Int.negOfNat 617427738389870341440428012088), (Int.negOfNat 291267101469832249922754659968), (Int.ofNat 19390337456551735244312895208), (Int.ofNat 6077446511312583520844945289), (Int.negOfNat 345149953021234615946102819), (Int.negOfNat 73432119316081357509953953), (Int.ofNat 3779983401356496583918105), (Int.ofNat 553697827720854115358173), (Int.negOfNat 27042785899713650135790), (Int.negOfNat 2838863259220829076324), (Int.ofNat 134266750458201834725), (Int.ofNat 10549984281071322349), (Int.negOfNat 441259528522611387), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(3337248794698125876221250003680621/5629499534213120000000000000000000), (-531166593174838880803571042986641/5629499534213120000000000000000000), (18180111077456932056070014263/56294995342131200000000000000000), (2188203368880996302784400031443/2251799813685248000000000000000000), (-77178467298733792680053501511/1407374883553280000000000000000000), (-2275524230233064452521520781/87960930222080000000000000000000), (2423792182068966905539111901/1407374883553280000000000000000000), (6077446511312583520844945289/11258999068426240000000000000000000), (-345149953021234615946102819/11258999068426240000000000000000000), (-73432119316081357509953953/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial170.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial170.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial170.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial170 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 4634601861527918072557517615586304), (Int.negOfNat 953608139160802343014711651874894), (Int.ofNat 39000244866017769799457284028810), (Int.negOfNat 78856674028653529401493385168), (Int.negOfNat 1277752062011321965819502419723), (Int.ofNat 192597533416168403984490857396), (Int.ofNat 35260633601929918439861485095), (Int.negOfNat 4391137284527530606555347979), (Int.negOfNat 554209369972885980281102280), (Int.ofNat 55015417480100601986878375), (Int.ofNat 5181964154510968594630759), (Int.negOfNat 445144347357170381471401), (Int.negOfNat 31741956861676361334155), (Int.ofNat 2489077306229938812735), (Int.ofNat 137137808378184593054), (Int.negOfNat 10157078776726607901), (Int.negOfNat 529798607556775232), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(4525978380398357492731950796471/10995116277760000000000000000000), (-476804069580401171507355825937447/5629499534213120000000000000000000), (3900024486601776979945728402881/1125899906842624000000000000000000), (-4928542126790845587593336573/703687441776640000000000000000000), (-1277752062011321965819502419723/11258999068426240000000000000000000), (48149383354042100996122714349/2814749767106560000000000000000000), (7052126720385983687972297019/2251799813685248000000000000000000), (-4391137284527530606555347979/11258999068426240000000000000000000), (-13855234249322149507027557/281474976710656000000000000000000), (440123339840804815895027/90071992547409920000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial170.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial170.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial170.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial170 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 2870059989581980281993667360275253), (Int.negOfNat 819650762707568194684372950788195), (Int.ofNat 28086388876709815187177249073693), (Int.negOfNat 53659986832122493594792413308), (Int.ofNat 1183292095138999975968320951162), (Int.ofNat 135829103586207447542646793213), (Int.negOfNat 41739425159426186491193094851), (Int.negOfNat 3201286444243413706402976321), (Int.ofNat 649374437559546154655201278), (Int.ofNat 38453992930478921781429441), (Int.negOfNat 6210192143228440654799925), (Int.negOfNat 285850738799335597152925), (Int.ofNat 40172646027428829856286), (Int.ofNat 1446403094851968747374), (Int.negOfNat 186019607192423594886), (Int.negOfNat 5223421684478173232), (Int.ofNat 559546659407780262), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(2870059989581980281993667360275253/11258999068426240000000000000000000), (-163930152541513638936874590157639/2251799813685248000000000000000000), (28086388876709815187177249073693/11258999068426240000000000000000000), (-13414996708030623398698103327/2814749767106560000000000000000000), (591646047569499987984160475581/5629499534213120000000000000000000), (135829103586207447542646793213/11258999068426240000000000000000000), (-41739425159426186491193094851/11258999068426240000000000000000000), (-3201286444243413706402976321/11258999068426240000000000000000000), (324687218779773077327600639/5629499534213120000000000000000000), (38453992930478921781429441/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial170.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial170.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial170.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial170 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 1363052013584622608304883627606550), (Int.negOfNat 667946014333812071362907789062331), (Int.ofNat 56125198250457555723959172205302), (Int.ofNat 7642559958394649346323490160682), (Int.negOfNat 66916896490569797990872137994), (Int.negOfNat 319692433368822099949851064063), (Int.negOfNat 10536706434825190606099195773), (Int.ofNat 6345336376689636367676744976), (Int.ofNat 186175349653135732353623696), (Int.negOfNat 74027385829362361812076372), (Int.negOfNat 1729339567330162922928252), (Int.ofNat 566005634814345337460727), (Int.ofNat 10271424256221689881366), (Int.negOfNat 3033265456536047784906), (Int.negOfNat 42586820415598733685), (Int.ofNat 12022126873428342851), (Int.ofNat 210940777180976672), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(27261040271692452166097672552131/225179981368524800000000000000000), (-667946014333812071362907789062331/11258999068426240000000000000000000), (28062599125228777861979586102651/5629499534213120000000000000000000), (3821279979197324673161745080341/5629499534213120000000000000000000), (-33458448245284898995436068997/5629499534213120000000000000000000), (-319692433368822099949851064063/11258999068426240000000000000000000), (-10536706434825190606099195773/11258999068426240000000000000000000), (396583523543102272979796561/703687441776640000000000000000000), (11635959353320983272101481/703687441776640000000000000000000), (-18506846457340590453019093/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial170.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial170.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial170.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial170 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 301647447339408225760449155444120), (Int.negOfNat 378613879419244395647268511019955), (Int.ofNat 76523143179385443996753450000710), (Int.negOfNat 3879697461880114673214455720784), (Int.negOfNat 2208464519999426797549971911369), (Int.ofNat 23868211224243450149672297583), (Int.ofNat 51899710171171521312710491932), (Int.negOfNat 79216555702799077861150682), (Int.negOfNat 752389724839054638197711689), (Int.ofNat 357179131053465849883298), (Int.ofNat 6940230750370347630220248), (Int.negOfNat 6395441730937111710411), (Int.negOfNat 43694606485071953350669), (Int.ofNat 71330143722218737531), (Int.ofNat 198167116144124513050), (Int.negOfNat 679149897765569345), (Int.negOfNat 677833790292949137), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(7541186183485205644011228886103/281474976710656000000000000000000), (-75722775883848879129453702203991/2251799813685248000000000000000000), (7652314317938544399675345000071/1125899906842624000000000000000000), (-242481091367507167075903482549/703687441776640000000000000000000), (-2208464519999426797549971911369/11258999068426240000000000000000000), (23868211224243450149672297583/11258999068426240000000000000000000), (12974927542792880328177622983/2814749767106560000000000000000000), (-39608277851399538930575341/5629499534213120000000000000000000), (-752389724839054638197711689/11258999068426240000000000000000000), (178589565526732924941649/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial170.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial170.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial170.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial170 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 211971036695019684778235360473450), (Int.negOfNat 178645038573948329209823772192760), (Int.ofNat 13284229247304486926579761191525), (Int.negOfNat 13577879951888376941001850999666), (Int.ofNat 368476232099659807181882484999), (Int.ofNat 355227083078152427058328375608), (Int.negOfNat 12434486164223097952184107952), (Int.negOfNat 6454079058638917270210459310), (Int.ofNat 187363706034249166896619556), (Int.ofNat 73302067289854828495485483), (Int.negOfNat 1760844798108816170437733), (Int.negOfNat 551155250788868281504286), (Int.ofNat 11355803606801193963569), (Int.ofNat 2919653936926336763267), (Int.negOfNat 53001911352133494781), (Int.negOfNat 11521720594075671853), (Int.ofNat 147346096823211513), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-4239420733900393695564707209469/225179981368524800000000000000000), (-4466125964348708230245594304819/281474976710656000000000000000000), (531369169892179477063190447661/450359962737049600000000000000000), (-6788939975944188470500925499833/5629499534213120000000000000000000), (368476232099659807181882484999/11258999068426240000000000000000000), (44403385384769053382291046951/1407374883553280000000000000000000), (-777155385263943622011506747/703687441776640000000000000000000), (-645407905863891727021045931/1125899906842624000000000000000000), (46840926508562291724154889/2814749767106560000000000000000000), (73302067289854828495485483/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial170.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial170.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial170.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial170 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 609023646237342768748817697737436), (Int.negOfNat 253166173291194556260784335586071), (Int.negOfNat 37603941179531899695047738851942), (Int.negOfNat 1343214202476864508980552504544), (Int.ofNat 1828413748180974786045766473087), (Int.negOfNat 132883619199049628805058700198), (Int.negOfNat 45367635588966444896957195148), (Int.ofNat 3066697120395530836726211450), (Int.ofNat 653876179371401237214726824), (Int.negOfNat 36381176752052479597196057), (Int.negOfNat 5985400498239944877308547), (Int.ofNat 277885249776357485154554), (Int.ofNat 37512698403479411351651), (Int.negOfNat 1484681928093068777093), (Int.negOfNat 170149409957605529839), (Int.ofNat 6028132272502847067), (Int.ofNat 544119990632529347), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-152255911559335692187204424434359/2814749767106560000000000000000000), (-253166173291194556260784335586071/11258999068426240000000000000000000), (-18801970589765949847523869425971/5629499534213120000000000000000000), (-41975443827402015905642265767/351843720888320000000000000000000), (1828413748180974786045766473087/11258999068426240000000000000000000), (-66441809599524814402529350099/5629499534213120000000000000000000), (-11341908897241611224239298787/2814749767106560000000000000000000), (61333942407910616734524229/225179981368524800000000000000000), (81734522421425154651840853/1407374883553280000000000000000000), (-36381176752052479597196057/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial170.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial170.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial170.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial170 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 1253882774321243469948224302267038), (Int.negOfNat 378599606875794218405748151769952), (Int.negOfNat 20294182226903726355187235958774), (Int.ofNat 3326919841235523765291616751837), (Int.negOfNat 842802906248451833547420312485), (Int.negOfNat 236988375747811187000752017538), (Int.ofNat 32130096263370207113833188768), (Int.ofNat 4736627080399353011199622258), (Int.negOfNat 501827210628823088089892451), (Int.negOfNat 54230369069056835430104042), (Int.ofNat 4712045890904658787665312), (Int.ofNat 409519673059239272524329), (Int.negOfNat 29749079549657423490471), (Int.negOfNat 2182708347090333241429), (Int.ofNat 134786119694783650870), (Int.ofNat 8847590695844733035), (Int.negOfNat 438776070997189803), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-626941387160621734974112151133519/5629499534213120000000000000000000), (-11831237714868569325179629742811/351843720888320000000000000000000), (-10147091113451863177593617979387/5629499534213120000000000000000000), (3326919841235523765291616751837/11258999068426240000000000000000000), (-168560581249690366709484062497/2251799813685248000000000000000000), (-118494187873905593500376008769/5629499534213120000000000000000000), (1004065508230318972307287149/351843720888320000000000000000000), (2368313540199676505599811129/5629499534213120000000000000000000), (-501827210628823088089892451/11258999068426240000000000000000000), (-27115184534528417715052021/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial170.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial170.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial170.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial170 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 2084199925498611045505139096599490), (Int.negOfNat 458101982650431722266703638909117), (Int.negOfNat 29710422034560763952416483489211), (Int.negOfNat 6206729399765577985788211020028), (Int.negOfNat 663110923969575221205534047130), (Int.ofNat 258834175542408229181568260768), (Int.ofNat 25565006357861503888283159493), (Int.negOfNat 5339316884433091012817260724), (Int.negOfNat 383512299723935121597037576), (Int.ofNat 63371988391074753054372528), (Int.ofNat 3575851972621817042841412), (Int.negOfNat 483847237737316776529993), (Int.negOfNat 22885309413089657427726), (Int.ofNat 2569015149352334478174), (Int.ofNat 105484793461056740705), (Int.negOfNat 10149688075443207969), (Int.negOfNat 264691203885120412), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-208419992549861104550513909659949/1125899906842624000000000000000000), (-458101982650431722266703638909117/11258999068426240000000000000000000), (-29710422034560763952416483489211/11258999068426240000000000000000000), (-1551682349941394496447052755007/2814749767106560000000000000000000), (-66311092396957522120553404713/1125899906842624000000000000000000), (8088567985700257161924008149/351843720888320000000000000000000), (25565006357861503888283159493/11258999068426240000000000000000000), (-1334829221108272753204315181/2814749767106560000000000000000000), (-47939037465491890199629697/1407374883553280000000000000000000), (3960749274442172065898283/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial170.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial170.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial170.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial170 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 3170336900698230940713216233206786), (Int.negOfNat 649655037176029402388578756361159), (Int.negOfNat 59979919205192297728162132189617), (Int.negOfNat 371711454723436765388365782943), (Int.ofNat 1815845300307573637325691864583), (Int.ofNat 86187111653395437267218304184), (Int.negOfNat 45426608531954643681489874464), (Int.negOfNat 1741158190107503029741808041), (Int.ofNat 698019206113452140137411082), (Int.ofNat 20798404681492611222121941), (Int.negOfNat 6605153833804489284000355), (Int.negOfNat 167129869348080978432325), (Int.ofNat 41863479345335419877174), (Int.ofNat 949089422832210310994), (Int.negOfNat 189215249233514516294), (Int.negOfNat 4121567932228523612), (Int.ofNat 557063201882358678), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-1585168450349115470356608116603393/5629499534213120000000000000000000), (-649655037176029402388578756361159/11258999068426240000000000000000000), (-59979919205192297728162132189617/11258999068426240000000000000000000), (-371711454723436765388365782943/11258999068426240000000000000000000), (1815845300307573637325691864583/11258999068426240000000000000000000), (10773388956674429658402288023/1407374883553280000000000000000000), (-1419581516623582615046558577/351843720888320000000000000000000), (-1741158190107503029741808041/11258999068426240000000000000000000), (349009603056726070068705541/5629499534213120000000000000000000), (20798404681492611222121941/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial170.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial170.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial170.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial170 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 4683676590526769178276456642299617), (Int.negOfNat 837807133343516168125892993396119), (Int.negOfNat 22538576236252457136547663268226), (Int.ofNat 10618225245042368809033872584967), (Int.ofNat 239855483729286026519934152577), (Int.negOfNat 304396781544507812211796836310), (Int.ofNat 221399639647225848263148445), (Int.ofNat 6278056643106836761201257861), (Int.negOfNat 4001801945275284290498180), (Int.negOfNat 75974121299777291945489945), (Int.negOfNat 134648509787121255319399), (Int.ofNat 587722427370853986704859), (Int.ofNat 2226332649789575230135), (Int.negOfNat 3144532272967167778705), (Int.negOfNat 16822703540194678594), (Int.ofNat 12385260516093994019), (Int.negOfNat 54166626490678148), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-4683676590526769178276456642299617/11258999068426240000000000000000000), (-837807133343516168125892993396119/11258999068426240000000000000000000), (-11269288118126228568273831634113/5629499534213120000000000000000000), (10618225245042368809033872584967/11258999068426240000000000000000000), (239855483729286026519934152577/11258999068426240000000000000000000), (-30439678154450781221179683631/1125899906842624000000000000000000), (44279927929445169652629689/2251799813685248000000000000000000), (6278056643106836761201257861/11258999068426240000000000000000000), (-200090097263764214524909/562949953421312000000000000000000), (-15194824259955458389097989/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial170.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial170.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial170.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial170 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 6369623482582607201303847748414591), (Int.negOfNat 814537347387173817161260479620235), (Int.ofNat 26504946009178685477975757886200), (Int.ofNat 3518823043202710404106037997416), (Int.negOfNat 1321618135542015688602878362928), (Int.ofNat 86162447222971997151965838128), (Int.ofNat 44307361777613505191896119052), (Int.negOfNat 2028512009369329478181366591), (Int.negOfNat 725087528867743431144324321), (Int.ofNat 21347854032215299952362447), (Int.ofNat 7056028248325713587583995), (Int.negOfNat 136879443760801496365967), (Int.negOfNat 45516847052479055221850), (Int.ofNat 586524362942665041256), (Int.ofNat 209131214294427817875), (Int.negOfNat 1605607590872677351), (Int.negOfNat 675350332767527553), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-6369623482582607201303847748414591/11258999068426240000000000000000000), (-162907469477434763432252095924047/2251799813685248000000000000000000), (132524730045893427389878789431/56294995342131200000000000000000), (439852880400338800513254749677/1407374883553280000000000000000000), (-82601133471375980537679897683/703687441776640000000000000000000), (5385152951435749821997864883/703687441776640000000000000000000), (11076840444403376297974029763/2814749767106560000000000000000000), (-2028512009369329478181366591/11258999068426240000000000000000000), (-725087528867743431144324321/11258999068426240000000000000000000), (21347854032215299952362447/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial170.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial170.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial170.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial170 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 7880508404797406115685302561327814), (Int.negOfNat 694752014703184438567064182383445), (Int.ofNat 30936188862152338825644256026553), (Int.ofNat 1258788786710569952477628395742), (Int.ofNat 988142952335437335744196573170), (Int.ofNat 214287539441782247160980797583), (Int.negOfNat 31683867226158599524050865964), (Int.negOfNat 5509186423973347335644671181), (Int.ofNat 448651296458518169714141297), (Int.ofNat 70775863332087643861901559), (Int.negOfNat 3794991964046069598428284), (Int.negOfNat 566949689921144101138966), (Int.ofNat 21289850866541241498067), (Int.ofNat 3104183405114841882123), (Int.negOfNat 84805214854589010701), (Int.negOfNat 12416256000316010419), (Int.ofNat 373024456866476708), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-3940254202398703057842651280663907/5629499534213120000000000000000000), (-138950402940636887713412836476689/2251799813685248000000000000000000), (30936188862152338825644256026553/11258999068426240000000000000000000), (629394393355284976238814197871/5629499534213120000000000000000000), (98814295233543733574419657317/1125899906842624000000000000000000), (214287539441782247160980797583/11258999068426240000000000000000000), (-7920966806539649881012716491/2814749767106560000000000000000000), (-5509186423973347335644671181/11258999068426240000000000000000000), (448651296458518169714141297/11258999068426240000000000000000000), (70775863332087643861901559/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial170.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial170.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial170.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial170 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 9116116667669921793915680735650369), (Int.negOfNat 515092288206748878441686888153812), (Int.ofNat 69113382140756666674332337317391), (Int.ofNat 10686328666291183760000357209976), (Int.ofNat 404034774502952906974815931006), (Int.negOfNat 329317528311616556339238155134), (Int.negOfNat 30288044363973969111411256792), (Int.ofNat 6049389894628444385986005144), (Int.ofNat 562415518925463574809811335), (Int.negOfNat 65672126390368266163291070), (Int.negOfNat 5876276494946930614021089), (Int.ofNat 457050214084405942158431), (Int.ofNat 39747211205150363111636), (Int.negOfNat 2197529768620212676011), (Int.negOfNat 187599399978954065754), (Int.ofNat 7829815871108545744), (Int.ofNat 687351520194096908), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-9116116667669921793915680735650369/11258999068426240000000000000000000), (-128773072051687219610421722038453/2814749767106560000000000000000000), (69113382140756666674332337317391/11258999068426240000000000000000000), (1335791083286397970000044651247/1407374883553280000000000000000000), (202017387251476453487407965503/5629499534213120000000000000000000), (-164658764155808278169619077567/5629499534213120000000000000000000), (-3786005545496746138926407099/1407374883553280000000000000000000), (756173736828555548248250643/1407374883553280000000000000000000), (112483103785092714961962267/2251799813685248000000000000000000), (-6567212639036826616329107/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial170.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial170.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial170.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial170 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 9789489388647024076491460887671738), (Int.negOfNat 126523775920496952466506112122026), (Int.ofNat 114031526089106888018456160694649), (Int.negOfNat 124971017064065266449439474392), (Int.negOfNat 2703084327392537109332118366568), (Int.negOfNat 95788624764801924345946131807), (Int.ofNat 62022935487758382413379059346), (Int.ofNat 3062801944280205296303428294), (Int.negOfNat 877708403961227662190505493), (Int.negOfNat 46592479489674054476985904), (Int.ofNat 7647393941143903298782287), (Int.ofNat 416699461006292885315569), (Int.negOfNat 44301334429382716575148), (Int.negOfNat 2436939557795404828781), (Int.ofNat 182862949483573364646), (Int.ofNat 10076118411281207112), (Int.negOfNat 664454431040454998), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-4894744694323512038245730443835869/5629499534213120000000000000000000), (-63261887960248476233253056061013/5629499534213120000000000000000000), (114031526089106888018456160694649/11258999068426240000000000000000000), (-15621377133008158306179934299/1407374883553280000000000000000000), (-337885540924067138666514795821/1407374883553280000000000000000000), (-95788624764801924345946131807/11258999068426240000000000000000000), (31011467743879191206689529673/5629499534213120000000000000000000), (1531400972140102648151714147/5629499534213120000000000000000000), (-877708403961227662190505493/11258999068426240000000000000000000), (-2912029968104628404811619/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial170.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial170.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial170.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial170 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 9629603745474169799365015052875662), (Int.ofNat 246257957207230417509524187260532), (Int.ofNat 55997266609099762657921031987120), (Int.negOfNat 15636172442824637669602633452841), (Int.negOfNat 138816599136298193397105815327), (Int.ofNat 487526720350402925237768558451), (Int.ofNat 4150638961826907866344340594), (Int.negOfNat 9445373202946806481276336197), (Int.negOfNat 199719320037014213730422711), (Int.ofNat 106153776739246399717641815), (Int.ofNat 3093918485955497205894412), (Int.negOfNat 751018000969034575016554), (Int.negOfNat 25068111099203416172237), (Int.ofNat 3659071398189928018389), (Int.ofNat 130189045020350685879), (Int.negOfNat 13409457527895453897), (Int.negOfNat 553637720533677118), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-4814801872737084899682507526437831/5629499534213120000000000000000000), (61564489301807604377381046815133/2814749767106560000000000000000000), (699965832613747033224012899839/140737488355328000000000000000000), (-15636172442824637669602633452841/11258999068426240000000000000000000), (-138816599136298193397105815327/11258999068426240000000000000000000), (487526720350402925237768558451/11258999068426240000000000000000000), (2075319480913453933172170297/5629499534213120000000000000000000), (-9445373202946806481276336197/11258999068426240000000000000000000), (-199719320037014213730422711/11258999068426240000000000000000000), (21230755347849279943528363/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial170.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial170.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial170.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial170 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 9025746939935127199062028892035692), (Int.ofNat 313785393607293769320984458352754), (Int.negOfNat 7355686729090398949528788779081), (Int.negOfNat 1644039386843136734629188285240), (Int.ofNat 2553226600747788547607885331060), (Int.negOfNat 130048214046263445158421053417), (Int.negOfNat 80440731826264907060032633426), (Int.ofNat 1449995715342650708107069193), (Int.ofNat 1241838115448126230784894007), (Int.ofNat 4215105893149514830653827), (Int.negOfNat 10999328352799363429116841), (Int.negOfNat 153727170440324481517733), (Int.ofNat 63865803436519389344474), (Int.ofNat 1235157587187154577676), (Int.negOfNat 264484170656464656665), (Int.negOfNat 5829684802688975565), (Int.ofNat 889027505384223393), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-2256436734983781799765507223008923/2814749767106560000000000000000000), (156892696803646884660492229176377/5629499534213120000000000000000000), (-7355686729090398949528788779081/11258999068426240000000000000000000), (-41100984671078418365729707131/281474976710656000000000000000000), (127661330037389427380394266553/562949953421312000000000000000000), (-130048214046263445158421053417/11258999068426240000000000000000000), (-40220365913132453530016316713/5629499534213120000000000000000000), (1449995715342650708107069193/11258999068426240000000000000000000), (1241838115448126230784894007/11258999068426240000000000000000000), (4215105893149514830653827/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial170.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial170.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial170.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial170 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 8408714981564793623127058184921407), (Int.ofNat 322363455406930806853576884896060), (Int.ofNat 17440447223371153238869998140067), (Int.ofNat 3601267807857651893194592350844), (Int.negOfNat 1905907168686325418620218457523), (Int.negOfNat 495340505098646580585450307537), (Int.ofNat 46383778317689520836487677212), (Int.ofNat 12188728422016014661957445437), (Int.negOfNat 361245921881573125899615352), (Int.negOfNat 140616356285606217691361849), (Int.ofNat 950877287964230344484485), (Int.ofNat 988012371233243595312061), (Int.ofNat 3713687769464546128679), (Int.negOfNat 4779544101380985242547), (Int.negOfNat 44121165138785863434), (Int.ofNat 17321366406512399997), (Int.ofNat 234779890157878558), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-8408714981564793623127058184921407/11258999068426240000000000000000000), (16118172770346540342678844244803/562949953421312000000000000000000), (17440447223371153238869998140067/11258999068426240000000000000000000), (900316951964412973298648087711/2814749767106560000000000000000000), (-1905907168686325418620218457523/11258999068426240000000000000000000), (-495340505098646580585450307537/11258999068426240000000000000000000), (11595944579422380209121919303/2814749767106560000000000000000000), (12188728422016014661957445437/11258999068426240000000000000000000), (-45155740235196640737451919/1407374883553280000000000000000000), (-140616356285606217691361849/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial170.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial170.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial170.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial170 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 7707394332682290908364291148975124), (Int.ofNat 348412361516778627414368659619348), (Int.negOfNat 28255076338213405193616405005782), (Int.negOfNat 18560466167585934254970970915462), (Int.negOfNat 1581764218523666497067735021898), (Int.ofNat 675488845652269779108397739110), (Int.ofNat 99054434490179319132503251489), (Int.negOfNat 8131997526214613194842859141), (Int.negOfNat 1578678038853769921074954686), (Int.ofNat 50297688885881972536948165), (Int.ofNat 13659686367871414739821721), (Int.negOfNat 177439184607480743662335), (Int.negOfNat 77725887129909060932810), (Int.ofNat 301813101827668341614), (Int.ofNat 318481489603596599826), (Int.ofNat 503122206095826448), (Int.negOfNat 1007314636269392268), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-1926848583170572727091072787243781/2814749767106560000000000000000000), (87103090379194656853592164904837/2814749767106560000000000000000000), (-14127538169106702596808202502891/5629499534213120000000000000000000), (-9280233083792967127485485457731/5629499534213120000000000000000000), (-790882109261833248533867510949/5629499534213120000000000000000000), (67548884565226977910839773911/1125899906842624000000000000000000), (99054434490179319132503251489/11258999068426240000000000000000000), (-8131997526214613194842859141/11258999068426240000000000000000000), (-789339019426884960537477343/5629499534213120000000000000000000), (10059537777176394507389633/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial170.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial170.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial170.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial170 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 7270832716422814990296592089242548), (Int.ofNat 30029831781685469046337610179903), (Int.negOfNat 107682689182976180517888325428551), (Int.ofNat 4735058703343508132163524557177), (Int.ofNat 7440784070793021396134855270617), (Int.ofNat 672650356688652938392143701201), (Int.negOfNat 118824637434484527972281916739), (Int.negOfNat 15773591030464523831406001254), (Int.ofNat 1006311988164962632376321116), (Int.ofNat 170200251215186231909876366), (Int.negOfNat 5432132168786527684831732), (Int.negOfNat 1146119749621112160479967), (Int.ofNat 20412221239676844709470), (Int.ofNat 5410816750562456201778), (Int.negOfNat 56092391872557290535), (Int.negOfNat 19186414503214134947), (Int.ofNat 84077940217920002), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-1817708179105703747574148022310637/2814749767106560000000000000000000), (30029831781685469046337610179903/11258999068426240000000000000000000), (-107682689182976180517888325428551/11258999068426240000000000000000000), (4735058703343508132163524557177/11258999068426240000000000000000000), (7440784070793021396134855270617/11258999068426240000000000000000000), (672650356688652938392143701201/11258999068426240000000000000000000), (-118824637434484527972281916739/11258999068426240000000000000000000), (-7886795515232261915703000627/5629499534213120000000000000000000), (251577997041240658094080279/2814749767106560000000000000000000), (85100125607593115954938183/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial170.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial170.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial170.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial170 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 7472332804826625323113035074811089), (Int.negOfNat 80461339712277219379935576555286), (Int.ofNat 116495690960916777043795140920303), (Int.ofNat 65912457931610531935775450194055), (Int.ofNat 4317558978647725447631260317462), (Int.negOfNat 1358230690144315407138144745723), (Int.negOfNat 145463949359168557033070919690), (Int.ofNat 14626987075335776688981259864), (Int.ofNat 1938245560975972098145750457), (Int.negOfNat 101994706783558986338320644), (Int.negOfNat 15428646396148028525777604), (Int.ofNat 506547923810010938940731), (Int.ofNat 84036344868506150613973), (Int.negOfNat 1897273803067007975259), (Int.negOfNat 336217461317963415030), (Int.ofNat 5399449376147916129), (Int.ofNat 1125601767154561143), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-7472332804826625323113035074811089/11258999068426240000000000000000000), (-40230669856138609689967788277643/5629499534213120000000000000000000), (116495690960916777043795140920303/11258999068426240000000000000000000), (13182491586322106387155090038811/2251799813685248000000000000000000), (2158779489323862723815630158731/5629499534213120000000000000000000), (-1358230690144315407138144745723/11258999068426240000000000000000000), (-14546394935916855703307091969/1125899906842624000000000000000000), (1828373384416972086122657483/1407374883553280000000000000000000), (1938245560975972098145750457/11258999068426240000000000000000000), (-25498676695889746584580161/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial170.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial170.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial170.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial170 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 6621363402339198435752281315867834), (Int.ofNat 1186276569644185925622913177493583), (Int.ofNat 484696514920831345446483058480467), (Int.ofNat 33758682516913744431756910100232), (Int.negOfNat 12313767808618320669301271147323), (Int.negOfNat 1314282101560521664478637914841), (Int.ofNat 167822069257500371273162145769), (Int.ofNat 20603310096139557960060202148), (Int.negOfNat 1475638274809167087963869488), (Int.negOfNat 191310557355811689126843217), (Int.ofNat 9181214768554596855618657), (Int.ofNat 1198725116113465719750046), (Int.negOfNat 42590668485457629284245), (Int.negOfNat 5443709178206471484159), (Int.ofNat 152743608834089351261), (Int.ofNat 18686008223861463949), (Int.negOfNat 442364814222108187), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-3310681701169599217876140657933917/5629499534213120000000000000000000), (1186276569644185925622913177493583/11258999068426240000000000000000000), (484696514920831345446483058480467/11258999068426240000000000000000000), (4219835314614218053969613762529/1407374883553280000000000000000000), (-12313767808618320669301271147323/11258999068426240000000000000000000), (-1314282101560521664478637914841/11258999068426240000000000000000000), (167822069257500371273162145769/11258999068426240000000000000000000), (5150827524034889490015050537/2814749767106560000000000000000000), (-92227392175572942997741843/703687441776640000000000000000000), (-191310557355811689126843217/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial170.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial170.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial170.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial170.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial170 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial170 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial170 := by
  interval_cases j
  · exact positiveCell00_correct
  · exact positiveCell01_correct
  · exact positiveCell02_correct
  · exact positiveCell03_correct
  · exact positiveCell04_correct
  · exact positiveCell05_correct
  · exact positiveCell06_correct
  · exact positiveCell07_correct
  · exact positiveCell08_correct
  · exact positiveCell09_correct
  · exact positiveCell10_correct
  · exact positiveCell11_correct
  · exact positiveCell12_correct
  · exact positiveCell13_correct
  · exact positiveCell14_correct
  · exact positiveCell15_correct
  · exact positiveCell16_correct
  · exact positiveCell17_correct
  · exact positiveCell18_correct
  · exact positiveCell19_correct
  · exact positiveCell20_correct
  · exact positiveCell21_correct
  · exact positiveCell22_correct
  · exact positiveCell23_correct
  · exact positiveCell24_correct
  · exact positiveCell25_correct
  · exact positiveCell26_correct
  · exact positiveCell27_correct
  · exact positiveCell28_correct
  · exact positiveCell29_correct
  · exact positiveCell30_correct
  · exact positiveCell31_correct

def negativeCell00Integer : List ℤ := [(Int.negOfNat 9549389017960647765341402656107980), (Int.negOfNat 1630862205889583690021465662206636), (Int.ofNat 570560376381808164100259998528240), (Int.negOfNat 30035942153642069858888943902994), (Int.negOfNat 12769134360229971371902389955519), (Int.ofNat 1303686393746953190164514996814), (Int.ofNat 168835822046958187931638412994), (Int.negOfNat 20587561859342781902743396148), (Int.negOfNat 1476878844710989994180052688), (Int.ofNat 191296107098200413009527617), (Int.ofNat 9182170548808682641529457), (Int.negOfNat 1198715697436096264393246), (Int.negOfNat 42590668485457629284245), (Int.ofNat 5443709178206471484159), (Int.ofNat 152743608834089351261), (Int.negOfNat 18686008223861463949), (Int.negOfNat 442364814222108187), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-477469450898032388267070132805399/562949953421312000000000000000000), (-407715551472395922505366415551659/2814749767106560000000000000000000), (7132004704772602051253249981603/140737488355328000000000000000000), (-15017971076821034929444471951497/5629499534213120000000000000000000), (-12769134360229971371902389955519/11258999068426240000000000000000000), (651843196873476595082257498407/5629499534213120000000000000000000), (84417911023479093965819206497/5629499534213120000000000000000000), (-5146890464835695475685849037/2814749767106560000000000000000000), (-92304927794436874636253293/703687441776640000000000000000000), (191296107098200413009527617/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial170.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial170.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial170.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 10923850679700250678793409052711764), (Int.ofNat 8785044489042665783255324458072), (Int.ofNat 213171145774245650554577489462089), (Int.negOfNat 66087744603322682842486054358221), (Int.ofNat 3820035494047443724259223625262), (Int.ofNat 1360545889381338041483204908193), (Int.negOfNat 144375058719768914748465872490), (Int.negOfNat 14632216053481154140582879864), (Int.ofNat 1936924817166812928642106457), (Int.ofNat 102000442284419689200165444), (Int.negOfNat 15427632445577176201248804), (Int.negOfNat 506551455814024484699531), (Int.ofNat 84036344868506150613973), (Int.ofNat 1897273803067007975259), (Int.negOfNat 336217461317963415030), (Int.negOfNat 5399449376147916129), (Int.ofNat 1125601767154561143), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-2730962669925062669698352263177941/2814749767106560000000000000000000), (1098130561130333222906915557259/1407374883553280000000000000000000), (213171145774245650554577489462089/11258999068426240000000000000000000), (-66087744603322682842486054358221/11258999068426240000000000000000000), (1910017747023721862129611812631/5629499534213120000000000000000000), (1360545889381338041483204908193/11258999068426240000000000000000000), (-14437505871976891474846587249/1125899906842624000000000000000000), (-1829027006685144267572859983/1407374883553280000000000000000000), (1936924817166812928642106457/11258999068426240000000000000000000), (25500110571104922300041361/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial170.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial170.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial170.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 10488221259695480015638768823484645), (Int.ofNat 267362106947144310395106249863401), (Int.negOfNat 23558811019946925160961025135667), (Int.negOfNat 8628951595752013803442978706137), (Int.ofNat 7028839193215563128547823346084), (Int.negOfNat 658279824884374206138274426427), (Int.negOfNat 117949702374943411612478555489), (Int.ofNat 15748995983650441272037717254), (Int.ofNat 1005267817643393967672296716), (Int.negOfNat 170175988598812121805806366), (Int.negOfNat 5431336096962815326363732), (Int.ofNat 1146104444270386795525167), (Int.ofNat 20412221239676844709470), (Int.negOfNat 5410816750562456201778), (Int.negOfNat 56092391872557290535), (Int.ofNat 19186414503214134947), (Int.ofNat 84077940217920002), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-2097644251939096003127753764696929/2251799813685248000000000000000000), (267362106947144310395106249863401/11258999068426240000000000000000000), (-23558811019946925160961025135667/11258999068426240000000000000000000), (-8628951595752013803442978706137/11258999068426240000000000000000000), (1757209798303890782136955836521/2814749767106560000000000000000000), (-658279824884374206138274426427/11258999068426240000000000000000000), (-117949702374943411612478555489/11258999068426240000000000000000000), (7874497991825220636018858627/5629499534213120000000000000000000), (251316954410848491918074179/2814749767106560000000000000000000), (-85087994299406060902903183/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial170.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial170.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial170.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 10030733296434009970141769073453035), (Int.ofNat 226871741126640056251680633734683), (Int.ofNat 23960115844111269445517300671451), (Int.ofNat 12070322709209613538487209650255), (Int.negOfNat 1805455948366621467096045707234), (Int.negOfNat 653098037982112184470578130435), (Int.ofNat 99486815499768191423623539114), (Int.ofNat 8094861121845111698793268741), (Int.negOfNat 1579165876154680098076888286), (Int.negOfNat 50261592948096866201992165), (Int.ofNat 13660046825866789788037721), (Int.ofNat 177416815248728287189935), (Int.negOfNat 77725887129909060932810), (Int.negOfNat 301813101827668341614), (Int.ofNat 318481489603596599826), (Int.negOfNat 503122206095826448), (Int.negOfNat 1007314636269392268), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-2006146659286801994028353814690607/2251799813685248000000000000000000), (226871741126640056251680633734683/11258999068426240000000000000000000), (23960115844111269445517300671451/11258999068426240000000000000000000), (2414064541841922707697441930051/2251799813685248000000000000000000), (-902727974183310733548022853617/5629499534213120000000000000000000), (-130619607596422436894115626087/2251799813685248000000000000000000), (49743407749884095711811769557/5629499534213120000000000000000000), (8094861121845111698793268741/11258999068426240000000000000000000), (-789582938077340049038444143/5629499534213120000000000000000000), (-10052318589619373240398433/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial170.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial170.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial170.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 9427385867958261697794029431486559), (Int.ofNat 378598788971503656477817430167073), (Int.ofNat 27215553152297864191973227139279), (Int.negOfNat 10937603827182591918024387194969), (Int.negOfNat 1890543139292794596061409562835), (Int.ofNat 519656856803356820531309549300), (Int.ofNat 46266730832135920012254957507), (Int.negOfNat 12228251374064441665086421837), (Int.negOfNat 361050556383227777079729352), (Int.ofNat 140654393938059906323398649), (Int.ofNat 950705662521202475976085), (Int.negOfNat 988037095261338415623661), (Int.ofNat 3713687769464546128679), (Int.ofNat 4779544101380985242547), (Int.negOfNat 44121165138785863434), (Int.negOfNat 17321366406512399997), (Int.ofNat 234779890157878558), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-9427385867958261697794029431486559/11258999068426240000000000000000000), (378598788971503656477817430167073/11258999068426240000000000000000000), (27215553152297864191973227139279/11258999068426240000000000000000000), (-10937603827182591918024387194969/11258999068426240000000000000000000), (-378108627858558919212281912567/2251799813685248000000000000000000), (5196568568033568205313095493/112589990684262400000000000000000), (46266730832135920012254957507/11258999068426240000000000000000000), (-12228251374064441665086421837/11258999068426240000000000000000000), (-45131319547903472134966169/1407374883553280000000000000000000), (140654393938059906323398649/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial170.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial170.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial170.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 8661072134997956658983153406499405), (Int.ofNat 340638306480950287098622140366906), (Int.negOfNat 39338680162463290758799817926588), (Int.negOfNat 4637039824714756631518062925186), (Int.ofNat 2794033749174492582368078897521), (Int.ofNat 149802197818523933920626566262), (Int.negOfNat 81064581015870980675718024226), (Int.negOfNat 1481203148577226066727224793), (Int.ofNat 1242656765039138381625746007), (Int.negOfNat 4185502741743436368621827), (Int.negOfNat 10999981436289933391806841), (Int.ofNat 153708333085585570804133), (Int.ofNat 63865803436519389344474), (Int.negOfNat 1235157587187154577676), (Int.negOfNat 264484170656464656665), (Int.ofNat 5829684802688975565), (Int.ofNat 889027505384223393), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-1732214426999591331796630681299881/2251799813685248000000000000000000), (170319153240475143549311070183453/5629499534213120000000000000000000), (-9834670040615822689699954481647/2814749767106560000000000000000000), (-2318519912357378315759031462593/5629499534213120000000000000000000), (2794033749174492582368078897521/11258999068426240000000000000000000), (74901098909261966960313283131/5629499534213120000000000000000000), (-40532290507935490337859012113/5629499534213120000000000000000000), (-1481203148577226066727224793/11258999068426240000000000000000000), (1242656765039138381625746007/11258999068426240000000000000000000), (-4185502741743436368621827/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial170.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial170.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial170.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 8129820802804338694550323504350864), (Int.ofNat 214014109046507393027364862630533), (Int.negOfNat 6481611616441615042478646465300), (Int.ofNat 11956033134044272646465343611093), (Int.ofNat 254388090905933174424246647145), (Int.negOfNat 477459691901901617706877197287), (Int.ofNat 3199021845970645870881433394), (Int.ofNat 9430811801101500421886560197), (Int.negOfNat 198506804649396234309128711), (Int.negOfNat 106140625384928033398393415), (Int.ofNat 3092964701205897229148812), (Int.ofNat 751010936961007483498954), (Int.negOfNat 25068111099203416172237), (Int.negOfNat 3659071398189928018389), (Int.ofNat 130189045020350685879), (Int.ofNat 13409457527895453897), (Int.negOfNat 553637720533677118), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-508113800175271168409395219021929/703687441776640000000000000000000), (214014109046507393027364862630533/11258999068426240000000000000000000), (-64816116164416150424786464653/112589990684262400000000000000000), (11956033134044272646465343611093/11258999068426240000000000000000000), (50877618181186634884849329429/2251799813685248000000000000000000), (-477459691901901617706877197287/11258999068426240000000000000000000), (1599510922985322935440716697/5629499534213120000000000000000000), (9430811801101500421886560197/11258999068426240000000000000000000), (-198506804649396234309128711/11258999068426240000000000000000000), (-21228125076985606679678683/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial170.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial170.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial170.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 7641967972099931214539114017907423), (Int.ofNat 305918602883505451799452195229020), (Int.ofNat 39478135725679363553730488050227), (Int.negOfNat 165034161224940870858979009387), (Int.negOfNat 2268985622859656130493484583800), (Int.ofNat 93774933132901600969183140424), (Int.ofNat 61008805148437137864042535746), (Int.negOfNat 3057014252694424548231159094), (Int.negOfNat 876437341373591182800748693), (Int.ofNat 46585706212775318131379104), (Int.ofNat 7646402625350768122479087), (Int.negOfNat 416693574332936975717569), (Int.negOfNat 44301334429382716575148), (Int.ofNat 2436939557795404828781), (Int.ofNat 182862949483573364646), (Int.negOfNat 10076118411281207112), (Int.negOfNat 664454431040454998), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-7641967972099931214539114017907423/11258999068426240000000000000000000), (15295930144175272589972609761451/562949953421312000000000000000000), (39478135725679363553730488050227/11258999068426240000000000000000000), (-165034161224940870858979009387/11258999068426240000000000000000000), (-11344928114298280652467422919/56294995342131200000000000000000), (11721866641612700121147892553/1407374883553280000000000000000000), (30504402574218568932021267873/5629499534213120000000000000000000), (-1528507126347212274115579547/5629499534213120000000000000000000), (-876437341373591182800748693/11258999068426240000000000000000000), (1455803319149228691605597/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial170.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial170.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial170.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 6903521901533997247040540471713550), (Int.ofNat 406332715599484032909007793485616), (Int.ofNat 2839967602764181975435154208323), (Int.negOfNat 7740885273323646257340502710499), (Int.ofNat 760152504979663502468775475977), (Int.ofNat 316168410032186679108014448220), (Int.negOfNat 31086573460700236640011840872), (Int.negOfNat 6025155222436227559721962344), (Int.ofNat 563396314517722453427000535), (Int.ofNat 65647433377263138789033470), (Int.negOfNat 5877034554809229148373889), (Int.negOfNat 457033731399009395284031), (Int.ofNat 39747211205150363111636), (Int.ofNat 2197529768620212676011), (Int.negOfNat 187599399978954065754), (Int.negOfNat 7829815871108545744), (Int.ofNat 687351520194096908), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-138070438030679944940810809434271/225179981368524800000000000000000), (25395794724967752056812987092851/703687441776640000000000000000000), (2839967602764181975435154208323/11258999068426240000000000000000000), (-7740885273323646257340502710499/11258999068426240000000000000000000), (760152504979663502468775475977/11258999068426240000000000000000000), (15808420501609333955400722411/562949953421312000000000000000000), (-3885821682587529580001480109/1407374883553280000000000000000000), (-753144402804528444965245293/1407374883553280000000000000000000), (112679262903544490685400107/2251799813685248000000000000000000), (6564743337726313878903347/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial170.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial170.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial170.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 6121733549106969080245040069196437), (Int.ofNat 366446425868862195228154579938708), (Int.negOfNat 10343394988857941551043249471202), (Int.ofNat 3897052391690547783983493696271), (Int.ofNat 1172632928597665149928076138029), (Int.negOfNat 234599279072873056154397309982), (Int.negOfNat 32052142904176353314996266364), (Int.ofNat 5544924542032127315115381581), (Int.ofNat 449075263517915051484758897), (Int.negOfNat 70811562540892357203105159), (Int.negOfNat 3795307826989882355569084), (Int.ofNat 566973236614567739530966), (Int.ofNat 21289850866541241498067), (Int.negOfNat 3104183405114841882123), (Int.negOfNat 84805214854589010701), (Int.ofNat 12416256000316010419), (Int.ofNat 373024456866476708), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-6121733549106969080245040069196437/11258999068426240000000000000000000), (91611606467215548807038644984677/2814749767106560000000000000000000), (-5171697494428970775521624735601/5629499534213120000000000000000000), (3897052391690547783983493696271/11258999068426240000000000000000000), (1172632928597665149928076138029/11258999068426240000000000000000000), (-117299639536436528077198654991/5629499534213120000000000000000000), (-8013035726044088328749066591/2814749767106560000000000000000000), (5544924542032127315115381581/11258999068426240000000000000000000), (449075263517915051484758897/11258999068426240000000000000000000), (-70811562540892357203105159/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial170.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial170.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial170.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 5389048451768799650484110517567282), (Int.ofNat 387207909639252050734492404323022), (Int.ofNat 18899451598257219222462569898400), (Int.ofNat 2262121552323633498328901905905), (Int.negOfNat 1352007785188702772802314965872), (Int.negOfNat 107775384653728667867991028812), (Int.ofNat 44462198189285826403732591852), (Int.ofNat 2065713563146457095839919791), (Int.negOfNat 725331868936393149458204721), (Int.negOfNat 21384649529554585454476447), (Int.ofNat 7056236995727369342027195), (Int.ofNat 136902990454225134757967), (Int.negOfNat 45516847052479055221850), (Int.negOfNat 586524362942665041256), (Int.ofNat 209131214294427817875), (Int.ofNat 1605607590872677351), (Int.negOfNat 675350332767527553), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-2694524225884399825242055258783641/5629499534213120000000000000000000), (193603954819626025367246202161511/5629499534213120000000000000000000), (23624314497821524028078212373/14073748835532800000000000000000), (452424310464726699665780381181/2251799813685248000000000000000000), (-84500486574293923300144685367/703687441776640000000000000000000), (-26943846163432166966997757203/2814749767106560000000000000000000), (11115549547321456600933147963/2814749767106560000000000000000000), (2065713563146457095839919791/11258999068426240000000000000000000), (-725331868936393149458204721/11258999068426240000000000000000000), (-21384649529554585454476447/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial170.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial170.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial170.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 4543098114278970354725835277978664), (Int.ofNat 446771610557487241352619975066594), (Int.ofNat 2144766183139784610721366873710), (Int.negOfNat 5899940115742448099182156316812), (Int.ofNat 12624856278833512894851320863), (Int.ofNat 287585541367557541468093131824), (Int.ofNat 846009636201677839344434765), (Int.negOfNat 6249741169054480787762324661), (Int.negOfNat 4840881247563429649379780), (Int.ofNat 75946396395365781197675945), (Int.negOfNat 133971183186335096875399), (Int.negOfNat 587704767350786257910859), (Int.ofNat 2226332649789575230135), (Int.ofNat 3144532272967167778705), (Int.negOfNat 16822703540194678594), (Int.negOfNat 12385260516093994019), (Int.negOfNat 54166626490678148), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-567887264284871294340729409747333/1407374883553280000000000000000000), (223385805278743620676309987533297/5629499534213120000000000000000000), (214476618313978461072136687371/1125899906842624000000000000000000), (-1474985028935612024795539079203/2814749767106560000000000000000000), (12624856278833512894851320863/11258999068426240000000000000000000), (17974096335472346341755820739/703687441776640000000000000000000), (169201927240335567868886953/2251799813685248000000000000000000), (-6249741169054480787762324661/11258999068426240000000000000000000), (-242044062378171482468989/562949953421312000000000000000000), (15189279279073156239535189/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial170.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial170.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial170.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 3679480097887928752746106240212393), (Int.ofNat 405487717332017092169225205143155), (Int.negOfNat 13617989015668831841848116038433), (Int.ofNat 2713854626085867075176931194628), (Int.ofNat 1464865428660383654313991572438), (Int.negOfNat 93550399449512869151015473973), (Int.negOfNat 44515680571594791955439329209), (Int.ofNat 1752788296027063776087321241), (Int.ofNat 696822936978858753865900682), (Int.negOfNat 20809434358146859171501941), (Int.negOfNat 6604200386306825309942755), (Int.ofNat 167136933356108069949925), (Int.ofNat 41863479345335419877174), (Int.negOfNat 949089422832210310994), (Int.negOfNat 189215249233514516294), (Int.ofNat 4121567932228523612), (Int.ofNat 557063201882358678), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-3679480097887928752746106240212393/11258999068426240000000000000000000), (81097543466403418433845041028631/2251799813685248000000000000000000), (-13617989015668831841848116038433/11258999068426240000000000000000000), (678463656521466768794232798657/2814749767106560000000000000000000), (732432714330191827156995786219/5629499534213120000000000000000000), (-93550399449512869151015473973/11258999068426240000000000000000000), (-44515680571594791955439329209/11258999068426240000000000000000000), (1752788296027063776087321241/11258999068426240000000000000000000), (348411468489429376932950341/5629499534213120000000000000000000), (-20809434358146859171501941/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial170.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial170.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial170.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 2883284722263754623576790458074050), (Int.ofNat 415846545715679643662582785100411), (Int.ofNat 21916041987378986260904663389858), (Int.ofNat 5596575290286252670967236643838), (Int.negOfNat 1031182815993422097084125258466), (Int.negOfNat 254839720809410135072809877257), (Int.ofNat 26500637880811820080986043893), (Int.ofNat 5331157418800583449367603924), (Int.negOfNat 384730400535156945906626776), (Int.negOfNat 63363337909408305277495728), (Int.ofNat 3576818298967892707079812), (Int.ofNat 483841351063960866931993), (Int.negOfNat 22885309413089657427726), (Int.negOfNat 2569015149352334478174), (Int.ofNat 105484793461056740705), (Int.ofNat 10149688075443207969), (Int.negOfNat 264691203885120412), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-57665694445275092471535809161481/225179981368524800000000000000000), (415846545715679643662582785100411/11258999068426240000000000000000000), (10958020993689493130452331694929/5629499534213120000000000000000000), (2798287645143126335483618321919/5629499534213120000000000000000000), (-515591407996711048542062629233/5629499534213120000000000000000000), (-254839720809410135072809877257/11258999068426240000000000000000000), (26500637880811820080986043893/11258999068426240000000000000000000), (1332789354700145862341900981/2814749767106560000000000000000000), (-48091300066894618238328347/1407374883553280000000000000000000), (-3960208619338019079843483/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial170.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial170.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial170.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1941556619886595754059752142772040), (Int.ofNat 524244195833912259584617967719555), (Int.ofNat 19374124489559432972896546123510), (Int.negOfNat 6578860922569287840319629730176), (Int.negOfNat 1118393705727597612475601496711), (Int.ofNat 251004325671913107310242398177), (Int.ofNat 32824017499381181688102001968), (Int.negOfNat 4762144670357037738480966658), (Int.negOfNat 502726976166056836464108051), (Int.ofNat 54256237908340747194330842), (Int.ofNat 4712758393879637781827712), (Int.negOfNat 409537333079307001318329), (Int.negOfNat 29749079549657423490471), (Int.ofNat 2182708347090333241429), (Int.ofNat 134786119694783650870), (Int.negOfNat 8847590695844733035), (Int.negOfNat 438776070997189803), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-48538915497164893851493803569301/281474976710656000000000000000000), (104848839166782451916923593543911/2251799813685248000000000000000000), (1937412448955943297289654612351/1125899906842624000000000000000000), (-51397350957572561252497107267/87960930222080000000000000000000), (-1118393705727597612475601496711/11258999068426240000000000000000000), (251004325671913107310242398177/11258999068426240000000000000000000), (2051501093711323855506375123/703687441776640000000000000000000), (-2381072335178518869240483329/5629499534213120000000000000000000), (-502726976166056836464108051/11258999068426240000000000000000000), (27128118954170373597165421/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial170.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial170.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial170.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 876670629758791157891268257846970), (Int.ofNat 510884009240808896017009290245460), (Int.negOfNat 22792276328562611913417766108385), (Int.negOfNat 3457540837291968147682860068234), (Int.ofNat 1726578191433624038414778544281), (Int.ofNat 152737420827777720633974425892), (Int.negOfNat 45112223480109282027933713148), (Int.negOfNat 3102298692891081751796181050), (Int.ofNat 653545558961630138239932824), (Int.ofNat 36417035722837908711846857), (Int.negOfNat 5985139058109971180222547), (Int.negOfNat 277908796469781123546554), (Int.ofNat 37512698403479411351651), (Int.ofNat 1484681928093068777093), (Int.negOfNat 170149409957605529839), (Int.negOfNat 6028132272502847067), (Int.ofNat 544119990632529347), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-87667062975879115789126825784697/1125899906842624000000000000000000), (25544200462040444800850464512273/562949953421312000000000000000000), (-4558455265712522382683553221677/2251799813685248000000000000000000), (-1728770418645984073841430034117/5629499534213120000000000000000000), (1726578191433624038414778544281/11258999068426240000000000000000000), (38184355206944430158493606473/2814749767106560000000000000000000), (-11278055870027320506983428287/2814749767106560000000000000000000), (-62045973857821635035923621/225179981368524800000000000000000), (81693194870203767279991603/1407374883553280000000000000000000), (36417035722837908711846857/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial170.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial170.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial170.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 55675946827078346919163161958596), (Int.ofNat 436362874523853689262540243277791), (Int.negOfNat 1527435603518810156877273301718), (Int.ofNat 8777124912115215176189674009124), (Int.ofNat 470311788847802850549250864573), (Int.negOfNat 335373281449420496196713915902), (Int.negOfNat 12689898273080260821207589952), (Int.ofNat 6418477486143366355140489710), (Int.ofNat 187694326444020265871413556), (Int.negOfNat 73266208319069399380834683), (Int.negOfNat 1761106238238789867523733), (Int.ofNat 551131704095444643112286), (Int.ofNat 11355803606801193963569), (Int.negOfNat 2919653936926336763267), (Int.negOfNat 53001911352133494781), (Int.ofNat 11521720594075671853), (Int.ofNat 147346096823211513), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(13918986706769586729790790489649/2814749767106560000000000000000000), (436362874523853689262540243277791/11258999068426240000000000000000000), (-763717801759405078438636650859/5629499534213120000000000000000000), (2194281228028803794047418502281/2814749767106560000000000000000000), (470311788847802850549250864573/11258999068426240000000000000000000), (-167686640724710248098356957951/5629499534213120000000000000000000), (-198279660516879075331368593/175921860444160000000000000000000), (641847748614336635514048971/1125899906842624000000000000000000), (46923581611005066467853389/2814749767106560000000000000000000), (-73266208319069399380834683/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial170.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial170.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial170.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 989321292906477834790463411604898), (Int.ofNat 524258468378096720848375919760472), (Int.ofNat 36854836463007665390552779038974), (Int.ofNat 627756380538354854351738397503), (Int.negOfNat 1932873720519778552920524629355), (Int.negOfNat 9852261299717022036641692522), (Int.ofNat 51205788935160546738441678732), (Int.ofNat 53698965745114350579806282), (Int.negOfNat 751489959301820889823496089), (Int.negOfNat 331310291769554085656498), (Int.ofNat 6939518247395368636057848), (Int.ofNat 6377781710869382916411), (Int.negOfNat 43694606485071953350669), (Int.negOfNat 71330143722218737531), (Int.ofNat 198167116144124513050), (Int.ofNat 679149897765569345), (Int.negOfNat 677833790292949137), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(494660646453238917395231705802449/5629499534213120000000000000000000), (65532308547262090106046989970059/1407374883553280000000000000000000), (18427418231503832695276389519487/5629499534213120000000000000000000), (627756380538354854351738397503/11258999068426240000000000000000000), (-386574744103955710584104925871/2251799813685248000000000000000000), (-4926130649858511018320846261/5629499534213120000000000000000000), (12801447233790136684610419683/2814749767106560000000000000000000), (26849482872557175289903141/5629499534213120000000000000000000), (-751489959301820889823496089/11258999068426240000000000000000000), (-165655145884777042828249/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial170.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial170.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial170.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 2162136810353224116168117878094030), (Int.ofNat 625690577400027434509824811826817), (Int.ofNat 4498734228544111512651943185551), (Int.negOfNat 8252714067879685303954469467612), (Int.ofNat 301154995534468399072717777270), (Int.ofNat 323686888101746302886403511492), (Int.negOfNat 11472337957775506798802080173), (Int.negOfNat 6353495842322143931126401776), (Int.ofNat 187393450464357556663212896), (Int.ofNat 74036036311028809588953172), (Int.negOfNat 1730305893676238587166652), (Int.negOfNat 566011521487701247058727), (Int.ofNat 10271424256221689881366), (Int.ofNat 3033265456536047784906), (Int.negOfNat 42586820415598733685), (Int.negOfNat 12022126873428342851), (Int.ofNat 210940777180976672), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(216213681035322411616811787809403/1125899906842624000000000000000000), (625690577400027434509824811826817/11258999068426240000000000000000000), (4498734228544111512651943185551/11258999068426240000000000000000000), (-2063178516969921325988617366903/2814749767106560000000000000000000), (30115499553446839907271777727/1125899906842624000000000000000000), (80921722025436575721600877873/2814749767106560000000000000000000), (-11472337957775506798802080173/11258999068426240000000000000000000), (-397093490145133995695400111/703687441776640000000000000000000), (5856045327011173645725403/351843720888320000000000000000000), (18509009077757202397238293/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial170.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial170.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial170.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3379203186777098413057005133375246), (Int.ofNat 575483442864556820012137905156119), (Int.negOfNat 18275541312823477955461239189343), (Int.ofNat 2395803158192228280522052098543), (Int.ofNat 1534271966786810750887438525037), (Int.negOfNat 143192391382407576546399476264), (Int.negOfNat 42650353119864896304500419356), (Int.ofNat 3212916550162974452748489521), (Int.ofNat 650570706694139540926711678), (Int.negOfNat 38465022607133169730809441), (Int.negOfNat 6211145590726104628857525), (Int.ofNat 285857802807362688670525), (Int.ofNat 40172646027428829856286), (Int.negOfNat 1446403094851968747374), (Int.negOfNat 186019607192423594886), (Int.ofNat 5223421684478173232), (Int.ofNat 559546659407780262), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(1689601593388549206528502566687623/5629499534213120000000000000000000), (575483442864556820012137905156119/11258999068426240000000000000000000), (-18275541312823477955461239189343/11258999068426240000000000000000000), (2395803158192228280522052098543/11258999068426240000000000000000000), (1534271966786810750887438525037/11258999068426240000000000000000000), (-17899048922800947068299934533/1407374883553280000000000000000000), (-10662588279966224076125104839/2814749767106560000000000000000000), (3212916550162974452748489521/11258999068426240000000000000000000), (325285353347069770463355839/5629499534213120000000000000000000), (-38465022607133169730809441/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial170.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial170.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial170.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4494023385287477820139705280755137), (Int.ofNat 562572616375689560556067840386459), (Int.ofNat 14316902446594746990747247163066), (Int.ofNat 4797141803320377139323027329933), (Int.negOfNat 1050521434563853973301502138377), (Int.negOfNat 209408773593123641643245405050), (Int.ofNat 34636023605375466448780198775), (Int.ofNat 4419452758579886579994281179), (Int.negOfNat 553370290670597834922220680), (Int.negOfNat 55043142384512112734692375), (Int.ofNat 5181286827910182436186759), (Int.ofNat 445162007377238110265401), (Int.negOfNat 31741956861676361334155), (Int.negOfNat 2489077306229938812735), (Int.ofNat 137137808378184593054), (Int.ofNat 10157078776726607901), (Int.negOfNat 529798607556775232), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(4494023385287477820139705280755137/11258999068426240000000000000000000), (562572616375689560556067840386459/11258999068426240000000000000000000), (7158451223297373495373623581533/5629499534213120000000000000000000), (4797141803320377139323027329933/11258999068426240000000000000000000), (-1050521434563853973301502138377/11258999068426240000000000000000000), (-4188175471862472832864908101/225179981368524800000000000000000), (1385440944215018657951207951/450359962737049600000000000000000), (4419452758579886579994281179/11258999068426240000000000000000000), (-13834257266764945873055517/281474976710656000000000000000000), (-440345139076096901877539/90071992547409920000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial170.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial170.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial170.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 5693922558591429663685309693452911), (Int.ofNat 635003748602381589379415205777515), (Int.ofNat 11241516626292354492787574833540), (Int.negOfNat 5160072248900169052197197272436), (Int.negOfNat 587038088741821128964325947572), (Int.ofNat 269654164039243456904165917392), (Int.ofNat 19235501044879414032476422408), (Int.negOfNat 6040244957535455903186392089), (Int.negOfNat 344905612952584897632222419), (Int.ofNat 73395323818742072007839953), (Int.ofNat 3779774653954840829474905), (Int.negOfNat 553674281027430476966173), (Int.negOfNat 27042785899713650135790), (Int.ofNat 2838863259220829076324), (Int.ofNat 134266750458201834725), (Int.negOfNat 10549984281071322349), (Int.negOfNat 441259528522611387), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(5693922558591429663685309693452911/11258999068426240000000000000000000), (127000749720476317875883041155503/2251799813685248000000000000000000), (562075831314617724639378741677/562949953421312000000000000000000), (-1290018062225042263049299318109/2814749767106560000000000000000000), (-146759522185455282241081486893/2814749767106560000000000000000000), (16853385252452716056510369837/703687441776640000000000000000000), (2404437630609926754059552801/1407374883553280000000000000000000), (-6040244957535455903186392089/11258999068426240000000000000000000), (-344905612952584897632222419/11258999068426240000000000000000000), (73395323818742072007839953/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial170.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial170.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial170.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 6967261722297105776418257139958094), (Int.ofNat 621651783328161037827247689540265), (Int.negOfNat 11931269978818639335114179759413), (Int.ofNat 433968861411730546327495677618), (Int.ofNat 1507130994110340374248499201290), (Int.negOfNat 1048787347680273980987977083), (Int.negOfNat 51023965748065619903939090796), (Int.negOfNat 618911427781640974231569419), (Int.ofNat 844335864963772273014116503), (Int.ofNat 16766297874530735151058801), (Int.negOfNat 8077308067131832923463216), (Int.negOfNat 197800547145232732830634), (Int.ofNat 49947645575745254811093), (Int.ofNat 1347888757903267794837), (Int.negOfNat 216933604129914096139), (Int.negOfNat 6245169898109661801), (Int.ofNat 848656437932573792), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(3483630861148552888209128569979047/5629499534213120000000000000000000), (124330356665632207565449537908053/2251799813685248000000000000000000), (-11931269978818639335114179759413/11258999068426240000000000000000000), (216984430705865273163747838809/5629499534213120000000000000000000), (150713099411034037424849920129/1125899906842624000000000000000000), (-1048787347680273980987977083/11258999068426240000000000000000000), (-12755991437016404975984772699/2814749767106560000000000000000000), (-618911427781640974231569419/11258999068426240000000000000000000), (844335864963772273014116503/11258999068426240000000000000000000), (16766297874530735151058801/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial170.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial170.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial170.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 8187264010146138823508793154966429), (Int.ofNat 618065663690007254267069189032812), (Int.ofNat 15593318267302642739091604526469), (Int.ofNat 5415254207671515903355006336144), (Int.negOfNat 835157683313219075683319075206), (Int.negOfNat 318972770615988904241919220006), (Int.ofNat 19153084128277157147825511332), (Int.ofNat 7819041941661679559845699336), (Int.negOfNat 162072153473726367029910015), (Int.negOfNat 99729649651076278501184370), (Int.ofNat 165163816904205337703189), (Int.ofNat 762062115628698715416529), (Int.ofNat 5866527143828550693024), (Int.negOfNat 3916018997253143666049), (Int.negOfNat 49606286276093841046), (Int.ofNat 14796417889663553896), (Int.ofNat 216686454178842992), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(8187264010146138823508793154966429/11258999068426240000000000000000000), (154516415922501813566767297258203/2814749767106560000000000000000000), (15593318267302642739091604526469/11258999068426240000000000000000000), (338453387979469743959687896009/703687441776640000000000000000000), (-417578841656609537841659537603/5629499534213120000000000000000000), (-159486385307994452120959610003/5629499534213120000000000000000000), (4788271032069289286956377833/2814749767106560000000000000000000), (977380242707709944980712417/1407374883553280000000000000000000), (-32414430694745273405982003/2251799813685248000000000000000000), (-9972964965107627850118437/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial170.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial170.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial170.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 9507656796817499419648109616977098), (Int.ofNat 699973066802574041477049882145466), (Int.ofNat 11647513908875677871064454114731), (Int.negOfNat 7374109848600974473991798250028), (Int.negOfNat 1236289311047784201382504713592), (Int.ofNat 317164630553446240174554248547), (Int.ofNat 54757502134213808246490766514), (Int.negOfNat 5231505834196997934300854054), (Int.negOfNat 1033621145950486654806018667), (Int.ofNat 38331486536081193638060784), (Int.ofNat 10140845233014121367888093), (Int.negOfNat 146256216729541317870209), (Int.negOfNat 62681382079640743441632), (Int.ofNat 228880729583244956281), (Int.ofNat 270769307284314147154), (Int.ofNat 665528241322753648), (Int.negOfNat 982370237592993582), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(4753828398408749709824054808488549/5629499534213120000000000000000000), (349986533401287020738524941072733/5629499534213120000000000000000000), (11647513908875677871064454114731/11258999068426240000000000000000000), (-1843527462150243618497949562507/2814749767106560000000000000000000), (-154536163880973025172813089199/1407374883553280000000000000000000), (317164630553446240174554248547/11258999068426240000000000000000000), (27378751067106904123245383257/5629499534213120000000000000000000), (-2615752917098498967150427027/5629499534213120000000000000000000), (-1033621145950486654806018667/11258999068426240000000000000000000), (2395717908505074602378799/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial170.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial170.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial170.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 10888168446789894045181514912590162), (Int.ofNat 651134106409610354410685140988988), (Int.negOfNat 28835703166131929911965724921960), (Int.negOfNat 249669796053333523679518519659), (Int.ofNat 2875411296483746917668392698467), (Int.ofNat 220466425390203121274147279169), (Int.negOfNat 80032989234557405243484490474), (Int.negOfNat 8735155629035402850450586843), (Int.ofNat 851396970861219018964636751), (Int.ofNat 117578551987189936253581265), (Int.negOfNat 5136828207159686403970992), (Int.negOfNat 893980046319096605152246), (Int.ofNat 20220690024682046238597), (Int.ofNat 4545746772835661685531), (Int.negOfNat 54760585625771531039), (Int.negOfNat 17136555478698357203), (Int.ofNat 74743519995135298), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(5444084223394947022590757456295081/5629499534213120000000000000000000), (162783526602402588602671285247247/2814749767106560000000000000000000), (-720892579153298247799143123049/281474976710656000000000000000000), (-249669796053333523679518519659/11258999068426240000000000000000000), (2875411296483746917668392698467/11258999068426240000000000000000000), (220466425390203121274147279169/11258999068426240000000000000000000), (-40016494617278702621742245237/5629499534213120000000000000000000), (-8735155629035402850450586843/11258999068426240000000000000000000), (851396970861219018964636751/11258999068426240000000000000000000), (23515710397437987250716253/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial170.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial170.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial170.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 12120188969175461842959235785876432), (Int.ofNat 624273137790404788572461102273286), (Int.ofNat 33220733829928313296879100257401), (Int.ofNat 15919991709282737663114506909860), (Int.negOfNat 842782375182334728216737057360), (Int.negOfNat 919633661578066143064588247043), (Int.negOfNat 56321632180533264584357578074), (Int.ofNat 13128174557234486285500467567), (Int.ofNat 1186927720750423994655249573), (Int.negOfNat 102731676161101534829443147), (Int.negOfNat 11400063033225204662235139), (Int.ofNat 531444265672465758164393), (Int.ofNat 68794892950691062072486), (Int.negOfNat 1986609301263585536256), (Int.negOfNat 293363606793587731535), (Int.ofNat 5558680038913114745), (Int.ofNat 970369050166424227), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(757511810573466365184952236617277/703687441776640000000000000000000), (312136568895202394286230551136643/5629499534213120000000000000000000), (33220733829928313296879100257401/11258999068426240000000000000000000), (795999585464136883155725345493/562949953421312000000000000000000), (-10534779689779184102709213217/140737488355328000000000000000000), (-919633661578066143064588247043/11258999068426240000000000000000000), (-28160816090266632292178789037/5629499534213120000000000000000000), (13128174557234486285500467567/11258999068426240000000000000000000), (1186927720750423994655249573/11258999068426240000000000000000000), (-102731676161101534829443147/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial170.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial170.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial170.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 13584382071027212635863685801053327), (Int.ofNat 843651804773420167771693176612880), (Int.ofNat 31789608935778455146743043130073), (Int.negOfNat 27838301381801447033092143189484), (Int.negOfNat 8950439121147943376574356243097), (Int.negOfNat 238261720258612057658749629183), (Int.ofNat 164354080893165684865557597968), (Int.ofNat 10598701976099878772110214843), (Int.negOfNat 1598522363323606209642016828), (Int.negOfNat 131180711270916337861269391), (Int.ofNat 10184067464510787984989035), (Int.ofNat 945363248821632371155599), (Int.negOfNat 46616437297019751202779), (Int.negOfNat 4656764009075640609653), (Int.ofNat 161976966783221117374), (Int.ofNat 17105559994476340803), (Int.negOfNat 393601350370933858), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(13584382071027212635863685801053327/11258999068426240000000000000000000), (10545647559667752097146164707661/140737488355328000000000000000000), (31789608935778455146743043130073/11258999068426240000000000000000000), (-6959575345450361758273035797371/2814749767106560000000000000000000), (-8950439121147943376574356243097/11258999068426240000000000000000000), (-238261720258612057658749629183/11258999068426240000000000000000000), (10272130055822855304097349873/703687441776640000000000000000000), (10598701976099878772110214843/11258999068426240000000000000000000), (-399630590830901552410504207/2814749767106560000000000000000000), (-131180711270916337861269391/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial170.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial170.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial170.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 15036717351731598989280337302054004), (Int.ofNat 365702129040398748254109829897912), (Int.negOfNat 325873280203215440001998008700598), (Int.negOfNat 80120242204709146092198458117858), (Int.negOfNat 654037436874765763391270434422), (Int.ofNat 1747709574393620524468938686290), (Int.ofNat 90126219565686638367349440811), (Int.negOfNat 20696784445227910367155833419), (Int.negOfNat 1396688805843911561313869514), (Int.ofNat 160043012586846454540639655), (Int.ofNat 11909672087102207377228239), (Int.negOfNat 879109275867098034928465), (Int.negOfNat 67718549859627089253570), (Int.ofNat 3616366680191321996766), (Int.ofNat 279110210781431724554), (Int.negOfNat 11285855562014315708), (Int.negOfNat 852081919281255352), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(3759179337932899747320084325513501/2814749767106560000000000000000000), (45712766130049843531763728737239/1407374883553280000000000000000000), (-162936640101607720000999004350299/5629499534213120000000000000000000), (-40060121102354573046099229058929/5629499534213120000000000000000000), (-327018718437382881695635217211/5629499534213120000000000000000000), (174770957439362052446893868629/1125899906842624000000000000000000), (90126219565686638367349440811/11258999068426240000000000000000000), (-20696784445227910367155833419/11258999068426240000000000000000000), (-698344402921955780656934757/5629499534213120000000000000000000), (32008602517369290908127931/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial170.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial170.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial170.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 13871982089563862965371969841403468), (Int.negOfNat 1773326093476120602916605768973743), (Int.negOfNat 676409663348650477588730406535449), (Int.negOfNat 14117224885563513016893840963457), (Int.ofNat 15632456629823282691945352046323), (Int.ofNat 852240487779796187535652214959), (Int.negOfNat 224520949683133323698685823121), (Int.negOfNat 14426008852396761507008725086), (Int.ofNat 2121678752427951232389415204), (Int.ofNat 140139944292687884841718654), (Int.negOfNat 14030639378110453346931708), (Int.negOfNat 907632612560040782185153), (Int.ofNat 68207720735053000088610), (Int.ofNat 4225976628855836540662), (Int.negOfNat 252883518916993362485), (Int.negOfNat 14869987553825554753), (Int.ofNat 712459180746732418), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(3467995522390965741342992460350867/2814749767106560000000000000000000), (-1773326093476120602916605768973743/11258999068426240000000000000000000), (-676409663348650477588730406535449/11258999068426240000000000000000000), (-14117224885563513016893840963457/11258999068426240000000000000000000), (15632456629823282691945352046323/11258999068426240000000000000000000), (852240487779796187535652214959/11258999068426240000000000000000000), (-224520949683133323698685823121/11258999068426240000000000000000000), (-7213004426198380753504362543/5629499534213120000000000000000000), (530419688106987808097353801/2814749767106560000000000000000000), (70069972146343942420859327/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial170.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial170.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial170.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 7768527566536846249760577292631089), (Int.negOfNat 4127109178502513593924124349351914), (Int.negOfNat 377068319644006184757686848287923), (Int.ofNat 105340430630527431561991886480445), (Int.ofNat 9368632175562866322415076299258), (Int.negOfNat 1952731796560279890433841810837), (Int.negOfNat 150508189134785024626182412450), (Int.ofNat 23501481466411977704538211116), (Int.ofNat 1576851380118486516526967523), (Int.negOfNat 191443172581590406130395816), (Int.negOfNat 11345666580670178656657636), (Int.ofNat 1113588121529038321400009), (Int.ofNat 58960229038655343642687), (Int.negOfNat 4829050540564764492261), (Int.negOfNat 230953165372536178490), (Int.ofNat 16011878325630525131), (Int.ofNat 733794788396086477), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(7768527566536846249760577292631089/11258999068426240000000000000000000), (-2063554589251256796962062174675957/5629499534213120000000000000000000), (-377068319644006184757686848287923/11258999068426240000000000000000000), (21068086126105486312398377296089/2251799813685248000000000000000000), (4684316087781433161207538149629/5629499534213120000000000000000000), (-1952731796560279890433841810837/11258999068426240000000000000000000), (-3010163782695700492523648249/225179981368524800000000000000000), (5875370366602994426134552779/2814749767106560000000000000000000), (1576851380118486516526967523/11258999068426240000000000000000000), (-23930396572698800766299477/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial170.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial170.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial170.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 1070157744703907363140076655191866), (Int.negOfNat 4244959278109605466523023896997203), (Int.ofNat 305121269413251639496098071446333), (Int.ofNat 92934111241372312067258614266208), (Int.negOfNat 11714518649368040334478399455097), (Int.negOfNat 1518585970038559390230941128359), (Int.ofNat 207106621319729649451467816771), (Int.ofNat 17043620010592105353614901652), (Int.negOfNat 2202615991445759218675364532), (Int.negOfNat 133710720395509686451280643), (Int.ofNat 15768048951865449878690903), (Int.ofNat 762529543541965718607194), (Int.negOfNat 81132253501641405289895), (Int.negOfNat 3273328734450005622161), (Int.ofNat 314508892404325449959), (Int.ofNat 10748431750885193851), (Int.negOfNat 991887967494141353), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-535078872351953681570038327595933/5629499534213120000000000000000000), (-4244959278109605466523023896997203/11258999068426240000000000000000000), (305121269413251639496098071446333/11258999068426240000000000000000000), (2904190976292884752101831695819/351843720888320000000000000000000), (-11714518649368040334478399455097/11258999068426240000000000000000000), (-1518585970038559390230941128359/11258999068426240000000000000000000), (207106621319729649451467816771/11258999068426240000000000000000000), (4260905002648026338403725413/2814749767106560000000000000000000), (-550653997861439804668841133/2814749767106560000000000000000000), (-133710720395509686451280643/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial170.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial170.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial170.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial170.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial170.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial170.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial170.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial170.reflect := by
  interval_cases j
  · exact negativeCell00_correct
  · exact negativeCell01_correct
  · exact negativeCell02_correct
  · exact negativeCell03_correct
  · exact negativeCell04_correct
  · exact negativeCell05_correct
  · exact negativeCell06_correct
  · exact negativeCell07_correct
  · exact negativeCell08_correct
  · exact negativeCell09_correct
  · exact negativeCell10_correct
  · exact negativeCell11_correct
  · exact negativeCell12_correct
  · exact negativeCell13_correct
  · exact negativeCell14_correct
  · exact negativeCell15_correct
  · exact negativeCell16_correct
  · exact negativeCell17_correct
  · exact negativeCell18_correct
  · exact negativeCell19_correct
  · exact negativeCell20_correct
  · exact negativeCell21_correct
  · exact negativeCell22_correct
  · exact negativeCell23_correct
  · exact negativeCell24_correct
  · exact negativeCell25_correct
  · exact negativeCell26_correct
  · exact negativeCell27_correct
  · exact negativeCell28_correct
  · exact negativeCell29_correct
  · exact negativeCell30_correct
  · exact negativeCell31_correct

end Bin170
end
end ErdosOverlap.OuterNumerics
