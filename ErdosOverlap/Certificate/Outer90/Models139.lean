/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.IntegerOuterBindings
public import ErdosOverlap.Numerics.OuterTruncation
public import ErdosOverlap.Certificate.OuterData11
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

/-! # Exact integer weighted outer models for source bin 139

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin139

def weightDenominator : ℤ := (Int.ofNat 1000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 327088680820623260)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 305287500488475600)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 220190345519217350)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 116593961176143750)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 56409086974141470)⟩, ⟨(19494472361809/1000000000000), (Int.negOfNat 54662402641158805)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 75078690169423420)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 26507549662685852)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 48786094635170696)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 11484631468221377)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial139.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial139.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 974546464132639200)⟩, ⟨(314159265359/50000000000), (Int.ofNat 171342723658811500)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 160453421603984930)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 58916055695213916)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 11545111987190777)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 7323271077289296)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 4514323116698779)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 4998621581807085)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 2150864547744611)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial139.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial139.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 974546464132639200)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 171342723658811500)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 160453421603984930)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 58916055695213916)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 11545111987190777)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 7323271077289296)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 4514323116698779)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 4998621581807085)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 2150864547744611)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial139.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial139.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial139.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 1046455291239410304253883667235371), (Int.ofNat 464714464333932843709755747593094), (Int.ofNat 100417618524735144411443249380445), (Int.negOfNat 15356519951173877025171487205461), (Int.negOfNat 2801600739427072367776110655128), (Int.ofNat 316068423723622856226361090478), (Int.ofNat 41984008283200741740648853220), (Int.negOfNat 3892499382034992287999553234), (Int.negOfNat 387468985347725380156213421), (Int.ofNat 31193329853882108744863399), (Int.ofNat 2412329309901869142746361), (Int.negOfNat 175316273568177181467855), (Int.negOfNat 10840280642346676913741), (Int.ofNat 730667816824773020702), (Int.ofNat 36876306720206954912), (Int.negOfNat 2324983660863325609), (Int.negOfNat 98302686271617000), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1046455291239410304253883667235371/1125899906842624000000000000000000), (232357232166966421854877873796547/562949953421312000000000000000000), (20083523704947028882288649876089/225179981368524800000000000000000), (-15356519951173877025171487205461/1125899906842624000000000000000000), (-350200092428384045972013831891/140737488355328000000000000000000), (158034211861811428113180545239/562949953421312000000000000000000), (2099200414160037087032442661/56294995342131200000000000000000), (-1946249691017496143999776617/562949953421312000000000000000000), (-387468985347725380156213421/1125899906842624000000000000000000), (31193329853882108744863399/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial139.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial139.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial139.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial139 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 129188118464307552216362115059605), (Int.ofNat 623743292788757787377713417519480), (Int.negOfNat 26742399379897358244881399779584), (Int.negOfNat 21086932583358462241929040327978), (Int.ofNat 1503971256785902894166955999918), (Int.ofNat 395647214290398864883238716143), (Int.negOfNat 29890864646891861775585420125), (Int.negOfNat 4392578125002096270268332643), (Int.ofNat 325970564223999822337889401), (Int.ofNat 31660704174063628804804465), (Int.negOfNat 2302913030223825917724982), (Int.negOfNat 159749035990697091924017), (Int.ofNat 11518996617542689231690), (Int.ofNat 597470594962947793068), (Int.negOfNat 43182088584754334475), (Int.negOfNat 1690422502726380837), (Int.ofNat 132783351521891694), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(25837623692861510443272423011921/225179981368524800000000000000000), (15593582319718944684442835437987/28147497671065600000000000000000), (-104462497577724055644067967889/4398046511104000000000000000000), (-10543466291679231120964520163989/562949953421312000000000000000000), (751985628392951447083477999959/562949953421312000000000000000000), (395647214290398864883238716143/1125899906842624000000000000000000), (-239126917175134894204683361/9007199254740992000000000000000), (-4392578125002096270268332643/1125899906842624000000000000000000), (325970564223999822337889401/1125899906842624000000000000000000), (6332140834812725760960893/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial139.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial139.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial139.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial139 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 1135355656200866415177092946945934), (Int.ofNat 336195900008643352801447421411006), (Int.negOfNat 94942667274869582739321751382457), (Int.ofNat 242008297202905136341658978133), (Int.ofNat 2893744025335456214661645135931), (Int.negOfNat 144134830578005737809279103439), (Int.negOfNat 42925857409298505556850457926), (Int.ofNat 2664364613806076170065888908), (Int.ofNat 377038799831005170924474329), (Int.negOfNat 25551071697554071357524021), (Int.negOfNat 2195770103610948146320583), (Int.ofNat 159157825994793161338237), (Int.ofNat 9130176177088101667343), (Int.negOfNat 708539446357789905473), (Int.negOfNat 28516510860767410082), (Int.ofNat 2380551565761114025), (Int.ofNat 61697927319208258), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(567677828100433207588546473472967/562949953421312000000000000000000), (168097950004321676400723710705503/562949953421312000000000000000000), (-94942667274869582739321751382457/1125899906842624000000000000000000), (242008297202905136341658978133/1125899906842624000000000000000000), (2893744025335456214661645135931/1125899906842624000000000000000000), (-144134830578005737809279103439/1125899906842624000000000000000000), (-21462928704649252778425228963/562949953421312000000000000000000), (666091153451519042516472227/281474976710656000000000000000000), (377038799831005170924474329/1125899906842624000000000000000000), (-25551071697554071357524021/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial139.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial139.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial139.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial139 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 1469275775597444647336897587050168), (Int.ofNat 33668176034193278648774865956016), (Int.negOfNat 43545703895900043970975688631343), (Int.ofNat 12762565365562276685879513143354), (Int.negOfNat 79785038606237221565386086230), (Int.negOfNat 330366126037905661147924205971), (Int.ofNat 14777327886572279050590614226), (Int.ofNat 3895284813787865869136851656), (Int.negOfNat 228277765801534984979321381), (Int.negOfNat 27493344148503886620733414), (Int.ofNat 1885859431818858060416701), (Int.ofNat 130607017236409846973552), (Int.negOfNat 10295168728408031749109), (Int.negOfNat 447187094058087760646), (Int.ofNat 40709061447197466950), (Int.ofNat 1079413637982444043), (Int.negOfNat 126330757878657861), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(183659471949680580917112198381271/140737488355328000000000000000000), (2104261002137079915548429122251/70368744177664000000000000000000), (-43545703895900043970975688631343/1125899906842624000000000000000000), (6381282682781138342939756571677/562949953421312000000000000000000), (-7978503860623722156538608623/112589990684262400000000000000000), (-330366126037905661147924205971/1125899906842624000000000000000000), (7388663943286139525295307113/562949953421312000000000000000000), (486910601723483233642106457/140737488355328000000000000000000), (-228277765801534984979321381/1125899906842624000000000000000000), (-13746672074251943310366707/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial139.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial139.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial139.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial139 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 1454055541563457046541039927006004), (Int.negOfNat 12050178211529011789549255055847), (Int.ofNat 10338635971213934338302160592970), (Int.ofNat 2931718933386552246423118266045), (Int.negOfNat 1743212663197181615274708148422), (Int.ofNat 34393179415828430479394057591), (Int.ofNat 32862221569372670166173428071), (Int.negOfNat 1507170774588314520819867872), (Int.negOfNat 302904855105791196023685713), (Int.ofNat 18511985133565755363024839), (Int.ofNat 1715411997331759477695532), (Int.negOfNat 130083471830753090224034), (Int.negOfNat 6590947728226220575752), (Int.ofNat 619624284807780013003), (Int.ofNat 18067894047507014963), (Int.negOfNat 2224543526787391866), (Int.negOfNat 27244032914544127), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(363513885390864261635259981751501/281474976710656000000000000000000), (-12050178211529011789549255055847/1125899906842624000000000000000000), (1033863597121393433830216059297/112589990684262400000000000000000), (586343786677310449284623653209/225179981368524800000000000000000), (-871606331598590807637354074211/562949953421312000000000000000000), (34393179415828430479394057591/1125899906842624000000000000000000), (32862221569372670166173428071/1125899906842624000000000000000000), (-47099086705884828775620871/35184372088832000000000000000000), (-302904855105791196023685713/1125899906842624000000000000000000), (18511985133565755363024839/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial139.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial139.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial139.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial139 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 1469816326909619116321580779307698), (Int.ofNat 16827643264281242377808898373964), (Int.negOfNat 4724331109327790861406326686156), (Int.negOfNat 5647298084537446078159377702642), (Int.negOfNat 97204192831275057434688278695), (Int.ofNat 213290696718855784996599583761), (Int.negOfNat 6128315561515296941467139984), (Int.negOfNat 2822691860718483389785864319), (Int.ofNat 142333120033865270578583001), (Int.ofNat 20136822720311108181026933), (Int.negOfNat 1391660840737847571226138), (Int.negOfNat 90122264931350289584942), (Int.ofNat 8293165199616031464530), (Int.ofNat 268785954419208065538), (Int.negOfNat 34435603370449247856), (Int.negOfNat 514960350919642567), (Int.ofNat 119878164235424028), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(734908163454809558160790389653849/562949953421312000000000000000000), (4206910816070310594452224593491/281474976710656000000000000000000), (-1181082777331947715351581671539/281474976710656000000000000000000), (-2823649042268723039079688851321/562949953421312000000000000000000), (-19440838566255011486937655739/225179981368524800000000000000000), (213290696718855784996599583761/1125899906842624000000000000000000), (-383019722594706058841696249/70368744177664000000000000000000), (-2822691860718483389785864319/1125899906842624000000000000000000), (142333120033865270578583001/1125899906842624000000000000000000), (20136822720311108181026933/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial139.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial139.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial139.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial139 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 1443957596077867156633308199275172), (Int.negOfNat 58141521142169630892473457937572), (Int.negOfNat 26915537163129727620898111201390), (Int.negOfNat 115421137850480154923820462260), (Int.ofNat 1096857555206313049595378110486), (Int.negOfNat 5987877375108326492800942991), (Int.negOfNat 21658567548446187068719190662), (Int.ofNat 766835331092750443698090102), (Int.ofNat 205385715334032347996418975), (Int.negOfNat 12072801012713720153459653), (Int.negOfNat 1118658769502824331923984), (Int.ofNat 95360707930728128087209), (Int.ofNat 3757496321259572939705), (Int.negOfNat 483269405712328935456), (Int.negOfNat 7305083500284658102), (Int.ofNat 1761974635240886732), (Int.negOfNat 7209861490120004), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(360989399019466789158327049818793/281474976710656000000000000000000), (-14535380285542407723118364484393/281474976710656000000000000000000), (-2691553716312972762089811120139/112589990684262400000000000000000), (-5771056892524007746191023113/56294995342131200000000000000000), (548428777603156524797689055243/562949953421312000000000000000000), (-5987877375108326492800942991/1125899906842624000000000000000000), (-10829283774223093534359595331/562949953421312000000000000000000), (383417665546375221849045051/562949953421312000000000000000000), (8215428613361293919856759/45035996273704960000000000000000), (-12072801012713720153459653/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial139.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial139.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial139.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial139 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 1235204610074815790475964738219126), (Int.negOfNat 136205302565657622601898595729702), (Int.negOfNat 6142862071394692900694631843038), (Int.ofNat 5674253924964372023067384432087), (Int.ofNat 122822901378554996382925321800), (Int.negOfNat 139784250164478915893676807188), (Int.ofNat 1733334224067271582018468142), (Int.ofNat 1785858047493984280112517145), (Int.negOfNat 77566235804251884649947588), (Int.negOfNat 12315336959812429029821798), (Int.ofNat 906576484630367906788325), (Int.ofNat 48549413554637683246574), (Int.negOfNat 5870401471811222319790), (Int.negOfNat 97717670625226456506), (Int.ofNat 25327018617450518344), (Int.negOfNat 65661645873733551), (Int.negOfNat 101940939123968818), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(617602305037407895237982369109563/562949953421312000000000000000000), (-68102651282828811300949297864851/562949953421312000000000000000000), (-3071431035697346450347315921519/562949953421312000000000000000000), (5674253924964372023067384432087/1125899906842624000000000000000000), (614114506892774981914626609/5629499534213120000000000000000), (-34946062541119728973419201797/281474976710656000000000000000000), (866667112033635791009234071/562949953421312000000000000000000), (357171609498796856022503429/225179981368524800000000000000000), (-19391558951062971162486897/281474976710656000000000000000000), (-6157668479906214514910899/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial139.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial139.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial139.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial139 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 981423022613585321639194877412352), (Int.negOfNat 98908006785071206393394531495492), (Int.ofNat 21099427995053451011964674347741), (Int.ofNat 2152979565380713601614475115591), (Int.negOfNat 794028100182336610808453796672), (Int.negOfNat 20405474906264702361947278377), (Int.ofNat 13186080636712450414436456596), (Int.negOfNat 250802056187023539733190620), (Int.negOfNat 117881056025801590950946776), (Int.ofNat 6556774447755126063486189), (Int.ofNat 568101150810225918252390), (Int.negOfNat 59369369569566588764205), (Int.negOfNat 1241998091176531851977), (Int.ofNat 319216607219985531456), (Int.negOfNat 1641370145142693825), (Int.negOfNat 1240902204789579175), (Int.ofNat 25877395331073536), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(958420920521079415663276247473/1099511627776000000000000000000), (-24727001696267801598348632873873/281474976710656000000000000000000), (21099427995053451011964674347741/1125899906842624000000000000000000), (2152979565380713601614475115591/1125899906842624000000000000000000), (-12406689065349009543882090573/17592186044416000000000000000000), (-20405474906264702361947278377/1125899906842624000000000000000000), (3296520159178112603609114149/281474976710656000000000000000000), (-12540102809351176986659531/56294995342131200000000000000000), (-14735132003225198868868347/140737488355328000000000000000000), (6556774447755126063486189/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial139.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial139.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial139.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial139 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 872656576373090576965303411356205), (Int.negOfNat 13399886502065706372737285281640), (Int.ofNat 16148122282488570330066078084993), (Int.negOfNat 3215965562555118202065931674151), (Int.negOfNat 377650247805852247094122336902), (Int.ofNat 79967801142481796753443914715), (Int.ofNat 1902051057796350141893166840), (Int.negOfNat 959723023697460425150991693), (Int.ofNat 26158545133381060831777682), (Int.ofNat 5888818874368414454689251), (Int.negOfNat 457420063273666797799139), (Int.negOfNat 15005039705092091643505), (Int.ofNat 3303318689968488037704), (Int.negOfNat 33373444860161477754), (Int.negOfNat 14871794742874164974), (Int.ofNat 447546682621853517), (Int.ofNat 74669947092036842), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(174531315274618115393060682271241/225179981368524800000000000000000), (-334997162551642659318432132041/28147497671065600000000000000000), (16148122282488570330066078084993/1125899906842624000000000000000000), (-3215965562555118202065931674151/1125899906842624000000000000000000), (-188825123902926123547061168451/562949953421312000000000000000000), (15993560228496359350688782943/225179981368524800000000000000000), (47551276444908753547329171/28147497671065600000000000000000), (-959723023697460425150991693/1125899906842624000000000000000000), (13079272566690530415888841/562949953421312000000000000000000), (5888818874368414454689251/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial139.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial139.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial139.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial139 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 881246245956146408022837182567875), (Int.ofNat 6886790940855907695924423974735), (Int.negOfNat 5933761955380816476894546882732), (Int.negOfNat 3200345365072747003587579407930), (Int.ofNat 314080802476497568476958339576), (Int.ofNat 41944613008565627199636216395), (Int.negOfNat 6227761356772385997444103750), (Int.negOfNat 137073843154532494874502987), (Int.ofNat 52431854073447564619430867), (Int.negOfNat 1886418617310548119133421), (Int.negOfNat 169491157274050904783476), (Int.ofNat 24869552100700387051762), (Int.negOfNat 478617284894946656491), (Int.negOfNat 146835502503744708334), (Int.ofNat 7374726725152115295), (Int.ofNat 535258077179684213), (Int.negOfNat 30909433156061080), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(7049969967649171264182697460543/9007199254740992000000000000000), (1377358188171181539184884794947/225179981368524800000000000000000), (-1483440488845204119223636720683/281474976710656000000000000000000), (-320034536507274700358757940793/112589990684262400000000000000000), (39260100309562196059619792447/140737488355328000000000000000000), (8388922601713125439927243279/225179981368524800000000000000000), (-4982209085417908797955283/900719925474099200000000000000), (-137073843154532494874502987/1125899906842624000000000000000000), (52431854073447564619430867/1125899906842624000000000000000000), (-1886418617310548119133421/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial139.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial139.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial139.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial139 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 851645746427085348871283114644531), (Int.negOfNat 43054648185293397485618739608904), (Int.negOfNat 15745141818893063926918934695719), (Int.negOfNat 944604689265759476286051947), (Int.ofNat 371265085273494322390197676608), (Int.negOfNat 25335764417238585032501976999), (Int.negOfNat 3797761840483247905649836154), (Int.ofNat 374424453112440627336071717), (Int.ofNat 12685956283191033255779856), (Int.negOfNat 1741056254238784802860688), (Int.ofNat 64522471951031283923587), (Int.negOfNat 4861951807518974933144), (Int.negOfNat 841440881706144476438), (Int.ofNat 102118418846566368702), (Int.ofNat 4187123886751671144), (Int.negOfNat 668521569731211699), (Int.negOfNat 40216052687372711), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(851645746427085348871283114644531/1125899906842624000000000000000000), (-5381831023161674685702342451113/140737488355328000000000000000000), (-15745141818893063926918934695719/1125899906842624000000000000000000), (-944604689265759476286051947/1125899906842624000000000000000000), (5801016957398348787346838697/17592186044416000000000000000000), (-25335764417238585032501976999/1125899906842624000000000000000000), (-1898880920241623952824918077/562949953421312000000000000000000), (374424453112440627336071717/1125899906842624000000000000000000), (792872267699439578486241/70368744177664000000000000000000), (-108816015889924050178793/70368744177664000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial139.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial139.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial139.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial139 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 707485102154997205270194240560169), (Int.negOfNat 96745117557495674349156579379851), (Int.negOfNat 9511880859791173214439322798094), (Int.ofNat 1571877392343647163200676590530), (Int.ofNat 2664008909819703763830541170), (Int.negOfNat 36956675296336855898298761133), (Int.ofNat 1814194131865508936045579455), (Int.ofNat 353636852532450769258487863), (Int.negOfNat 15636034737692871976176987), (Int.negOfNat 1768561097409413736826724), (Int.negOfNat 24615152694152738894859), (Int.ofNat 5402576453966331925790), (Int.ofNat 1146089324419762694611), (Int.negOfNat 14266645421415421319), (Int.negOfNat 8804638475085459380), (Int.ofNat 94690308452537519), (Int.ofNat 24456839512827247), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(707485102154997205270194240560169/1125899906842624000000000000000000), (-96745117557495674349156579379851/1125899906842624000000000000000000), (-4755940429895586607219661399047/562949953421312000000000000000000), (157187739234364716320067659053/112589990684262400000000000000000), (266400890981970376383054117/112589990684262400000000000000000), (-36956675296336855898298761133/1125899906842624000000000000000000), (362838826373101787209115891/225179981368524800000000000000000), (353636852532450769258487863/1125899906842624000000000000000000), (-15636034737692871976176987/1125899906842624000000000000000000), (-442140274352353434206681/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial139.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial139.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial139.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial139 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 487538829180783587126775629545884), (Int.negOfNat 118314768261533104795558043346866), (Int.negOfNat 2336392499373849252896478621381), (Int.ofNat 565671293512843857138367744187), (Int.negOfNat 183647230899993754040219651174), (Int.ofNat 4012953203160806185121124511), (Int.ofNat 3880855666939525629661222984), (Int.negOfNat 122412679753380610615530147), (Int.negOfNat 37811362758198634798405398), (Int.ofNat 286749103568162689466775), (Int.ofNat 246389823959713493304071), (Int.ofNat 8826259039806900300316), (Int.negOfNat 1265151489420035492147), (Int.negOfNat 99901558741668131300), (Int.ofNat 5410873939224293195), (Int.ofNat 572684842761021361), (Int.ofNat 5762158282708580), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(121884707295195896781693907386471/281474976710656000000000000000000), (-59157384130766552397779021673433/562949953421312000000000000000000), (-2336392499373849252896478621381/1125899906842624000000000000000000), (565671293512843857138367744187/1125899906842624000000000000000000), (-91823615449996877020109825587/562949953421312000000000000000000), (4012953203160806185121124511/1125899906842624000000000000000000), (485106958367440703707652873/140737488355328000000000000000000), (-122412679753380610615530147/1125899906842624000000000000000000), (-18905681379099317399202699/562949953421312000000000000000000), (11469964142726507578671/45035996273704960000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial139.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial139.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial139.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial139 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 243502589346998376626443200704526), (Int.negOfNat 125774407358854179764641303713333), (Int.negOfNat 2243166658095229735834641457579), (Int.negOfNat 252828441960143727794983909204), (Int.ofNat 17359884319599309367096034946), (Int.ofNat 26032900699095760656361677458), (Int.negOfNat 1008104202776587173635710172), (Int.negOfNat 442846983474082389829352932), (Int.ofNat 10633709986389554830930948), (Int.ofNat 4274202744165337076592465), (Int.ofNat 4458702353905953979139), (Int.negOfNat 28701438908017301460163), (Int.negOfNat 724568754966920553870), (Int.ofNat 145171723271183023706), (Int.ofNat 6057611445348738539), (Int.negOfNat 632144590530738425), (Int.negOfNat 18004245869593414), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(121751294673499188313221600352263/562949953421312000000000000000000), (-125774407358854179764641303713333/1125899906842624000000000000000000), (-2243166658095229735834641457579/1125899906842624000000000000000000), (-63207110490035931948745977301/281474976710656000000000000000000), (8679942159799654683548017473/562949953421312000000000000000000), (13016450349547880328180838729/562949953421312000000000000000000), (-252026050694146793408927543/281474976710656000000000000000000), (-110711745868520597457338233/281474976710656000000000000000000), (2658427496597388707732737/281474976710656000000000000000000), (854840548833067415318493/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial139.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial139.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial139.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial139 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 18047056942487540815016358434467), (Int.negOfNat 135514391710309909367664120901347), (Int.negOfNat 1762435995986141209469513276023), (Int.ofNat 558929794810057007985010913239), (Int.ofNat 121162185257018830429813776808), (Int.negOfNat 10716848966744745075517830245), (Int.negOfNat 3562001835088725405455892047), (Int.ofNat 194694533745357348840910653), (Int.ofNat 51354458958294677646560770), (Int.negOfNat 1388172282174371480250617), (Int.negOfNat 453116176021011623084231), (Int.ofNat 2113411705364994289785), (Int.ofNat 2779076531665835392036), (Int.ofNat 31415760074549148169), (Int.negOfNat 12501989474411390137), (Int.negOfNat 283701203574645323), (Int.ofNat 26540871574210940), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-18047056942487540815016358434467/1125899906842624000000000000000000), (-135514391710309909367664120901347/1125899906842624000000000000000000), (-1762435995986141209469513276023/1125899906842624000000000000000000), (558929794810057007985010913239/1125899906842624000000000000000000), (15145273157127353803726722101/140737488355328000000000000000000), (-2143369793348949015103566049/225179981368524800000000000000000), (-3562001835088725405455892047/1125899906842624000000000000000000), (194694533745357348840910653/1125899906842624000000000000000000), (5135445895829467764656077/112589990684262400000000000000000), (-1388172282174371480250617/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial139.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial139.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial139.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial139 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 290249549646237920512288001203276), (Int.negOfNat 133386656398519633518946834070522), (Int.ofNat 2998299686000993714811867870621), (Int.ofNat 716668274643639579815659698587), (Int.negOfNat 98942362555864737083845404868), (Int.negOfNat 20211004134463494074714151544), (Int.ofNat 2652570952600009244684203102), (Int.ofNat 460802896851661562105147150), (Int.negOfNat 31593262724669294695386518), (Int.negOfNat 5560942757011905080057098), (Int.ofNat 195097567255043065402164), (Int.ofNat 42572067778669156154537), (Int.negOfNat 613506282497053285455), (Int.negOfNat 228932386001698282223), (Int.ofNat 288732628106113424), (Int.ofNat 976799622481061761), (Int.negOfNat 9266746162338562), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-72562387411559480128072000300819/281474976710656000000000000000000), (-66693328199259816759473417035261/562949953421312000000000000000000), (2998299686000993714811867870621/1125899906842624000000000000000000), (716668274643639579815659698587/1125899906842624000000000000000000), (-24735590638966184270961351217/281474976710656000000000000000000), (-2526375516807936759339268943/140737488355328000000000000000000), (1326285476300004622342101551/562949953421312000000000000000000), (9216057937033231242102943/22517998136852480000000000000000), (-15796631362334647347693259/562949953421312000000000000000000), (-2780471378505952540028549/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial139.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial139.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial139.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial139 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 541308052587655931889255611038297), (Int.negOfNat 116904453462638043968304337498519), (Int.ofNat 4174218138704605919553951781747), (Int.negOfNat 282699863511146216293078372222), (Int.negOfNat 66417860148785057618047883722), (Int.ofNat 27660161916728590327365020324), (Int.ofNat 3029311425081201662077838880), (Int.negOfNat 472464486728049769837016481), (Int.negOfNat 53868949857949350758294066), (Int.ofNat 4311688369144423016903279), (Int.ofNat 534739933178724977193725), (Int.negOfNat 24096680653160308144103), (Int.negOfNat 3499439076050963548480), (Int.ofNat 87191813838799679701), (Int.ofNat 16385335504322986730), (Int.negOfNat 136718614867651563), (Int.negOfNat 45208405415164472), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-541308052587655931889255611038297/1125899906842624000000000000000000), (-116904453462638043968304337498519/1125899906842624000000000000000000), (4174218138704605919553951781747/1125899906842624000000000000000000), (-141349931755573108146539186111/562949953421312000000000000000000), (-33208930074392528809023941861/562949953421312000000000000000000), (6915040479182147581841255081/281474976710656000000000000000000), (18933196406757510387986493/7036874417766400000000000000000), (-472464486728049769837016481/1125899906842624000000000000000000), (-26934474928974675379147033/562949953421312000000000000000000), (4311688369144423016903279/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial139.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial139.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial139.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial139 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 760736943975447998760545387897147), (Int.negOfNat 103185414933878485122859621262082), (Int.ofNat 3434941846020413853631795318037), (Int.ofNat 445958594915503364518771205707), (Int.ofNat 222477195942712348380458751641), (Int.ofNat 12173215172348930270633877866), (Int.negOfNat 5456770602223906449829831394), (Int.negOfNat 399949010755395457599859748), (Int.ofNat 66860149822945662625753754), (Int.ofNat 5448155151684719376721268), (Int.negOfNat 504269953867389710013137), (Int.negOfNat 44871817220739008212716), (Int.ofNat 2539594234595967300665), (Int.ofNat 252470451865363726920), (Int.negOfNat 9060168254427697961), (Int.negOfNat 1058875077041536029), (Int.ofNat 45871505114747304), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-760736943975447998760545387897147/1125899906842624000000000000000000), (-51592707466939242561429810631041/562949953421312000000000000000000), (3434941846020413853631795318037/1125899906842624000000000000000000), (445958594915503364518771205707/1125899906842624000000000000000000), (222477195942712348380458751641/1125899906842624000000000000000000), (6086607586174465135316938933/562949953421312000000000000000000), (-2728385301111953224914915697/562949953421312000000000000000000), (-99987252688848864399964937/281474976710656000000000000000000), (33430074911472831312876877/562949953421312000000000000000000), (1362038787921179844180317/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial139.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial139.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial139.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial139 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 946232276797791006659332982632509), (Int.negOfNat 77149889418401939779640638188944), (Int.ofNat 10983666113753749680698230314415), (Int.ofNat 1755463180772695679245459162846), (Int.negOfNat 6602756062561581469273738217), (Int.negOfNat 51031659936694034291567005998), (Int.negOfNat 2067991404634725321366732190), (Int.ofNat 819937823441969844935688775), (Int.ofNat 42964526669194128376012512), (Int.negOfNat 8008416910891138956959966), (Int.negOfNat 468125650811784327183723), (Int.ofNat 51491257208684964037017), (Int.ofNat 3277064475013823621751), (Int.negOfNat 231440600479674496073), (Int.negOfNat 16035120937785339209), (Int.ofNat 721219929948902505), (Int.ofNat 38755811771930639), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-946232276797791006659332982632509/1125899906842624000000000000000000), (-4821868088650121236227539886809/70368744177664000000000000000000), (2196733222750749936139646062883/225179981368524800000000000000000), (877731590386347839622729581423/562949953421312000000000000000000), (-6602756062561581469273738217/1125899906842624000000000000000000), (-25515829968347017145783502999/562949953421312000000000000000000), (-206799140463472532136673219/112589990684262400000000000000000), (32797512937678793797427551/45035996273704960000000000000000), (1342641458412316511750391/35184372088832000000000000000000), (-4004208455445569478479983/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial139.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial139.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial139.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial139 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 1044313206360912289237615604205271), (Int.negOfNat 16449415918385280150071084868260), (Int.ofNat 17366452667998006787902481506496), (Int.negOfNat 181123875803879765649102890667), (Int.negOfNat 399385891205187558663690074703), (Int.negOfNat 5879767155712040653452942059), (Int.ofNat 8162861622140349470538251439), (Int.ofNat 228775314951511252925806749), (Int.negOfNat 103350381277265822588790864), (Int.negOfNat 3636329234789026011252252), (Int.ofNat 840113800569862709865334), (Int.ofNat 33908710890634251687893), (Int.negOfNat 4652271070723306299785), (Int.negOfNat 208211462042904981223), (Int.ofNat 18464761734469133778), (Int.ofNat 929374587730499722), (Int.negOfNat 80325399519411435), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-1044313206360912289237615604205271/1125899906842624000000000000000000), (-822470795919264007503554243413/56294995342131200000000000000000), (271350822937468856060976273539/17592186044416000000000000000000), (-181123875803879765649102890667/1125899906842624000000000000000000), (-399385891205187558663690074703/1125899906842624000000000000000000), (-5879767155712040653452942059/1125899906842624000000000000000000), (8162861622140349470538251439/1125899906842624000000000000000000), (228775314951511252925806749/1125899906842624000000000000000000), (-6459398829829113911799429/70368744177664000000000000000000), (-909082308697256502813063/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial139.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial139.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial139.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial139 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 1015249249165395398519369490886448), (Int.ofNat 39152290453932646741675993814321), (Int.ofNat 8145223217709740432414068566167), (Int.negOfNat 2368215809662495286111412999699), (Int.negOfNat 22690180645382329059878986030), (Int.ofNat 64918134723344653690568194757), (Int.ofNat 366122238516456310001297028), (Int.negOfNat 1094444047285698338928867351), (Int.negOfNat 14156455388057510955795233), (Int.ofNat 11435494995280104719496471), (Int.ofNat 230843326830697513656745), (Int.negOfNat 78490552914720813125317), (Int.negOfNat 2039449678708410629986), (Int.ofNat 375391680494398088224), (Int.ofNat 11475562699182341737), (Int.negOfNat 1259165667349018129), (Int.negOfNat 32303218128696806), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-63453078072837212407460593180403/70368744177664000000000000000000), (39152290453932646741675993814321/1125899906842624000000000000000000), (8145223217709740432414068566167/1125899906842624000000000000000000), (-2368215809662495286111412999699/1125899906842624000000000000000000), (-2269018064538232905987898603/112589990684262400000000000000000), (64918134723344653690568194757/1125899906842624000000000000000000), (91530559629114077500324257/281474976710656000000000000000000), (-1094444047285698338928867351/1125899906842624000000000000000000), (-14156455388057510955795233/1125899906842624000000000000000000), (11435494995280104719496471/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial139.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial139.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial139.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial139 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 921709520038524366243880610928796), (Int.ofNat 47374062950818502246285069070607), (Int.negOfNat 2035081649915464546769033842268), (Int.negOfNat 471095676014320471461501052800), (Int.ofNat 371940724013455507623567545474), (Int.negOfNat 6444811944942035655291238040), (Int.negOfNat 9274733262441675064791328501), (Int.ofNat 125154224675532487261344536), (Int.ofNat 129949226726255078715189982), (Int.negOfNat 240771813731388208356715), (Int.negOfNat 1131972209533526020962727), (Int.negOfNat 8880002271144205195706), (Int.ofNat 6582691700715799126490), (Int.ofNat 96804917910725174457), (Int.negOfNat 27220164657232633779), (Int.negOfNat 547975648487839245), (Int.ofNat 114779293924075566), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-230427380009631091560970152732199/281474976710656000000000000000000), (47374062950818502246285069070607/1125899906842624000000000000000000), (-508770412478866136692258460567/281474976710656000000000000000000), (-147217398754475147331719079/351843720888320000000000000000), (185970362006727753811783772737/562949953421312000000000000000000), (-161120298623550891382280951/28147497671065600000000000000000), (-9274733262441675064791328501/1125899906842624000000000000000000), (15644278084441560907668067/140737488355328000000000000000000), (64974613363127539357594991/562949953421312000000000000000000), (-48154362746277641671343/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial139.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial139.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial139.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial139 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 833671238030244157288537431842028), (Int.ofNat 43369208037539659623735157162287), (Int.ofNat 1626423463544726392535978271108), (Int.ofNat 1047328094250873868483992133883), (Int.negOfNat 84123773728060117020747504202), (Int.negOfNat 58217096749125675741125496311), (Int.ofNat 3324211327008999214127172557), (Int.ofNat 1201240178537981904501359769), (Int.negOfNat 39117125879848915583978442), (Int.negOfNat 13925192987884734224030893), (Int.ofNat 190413359801750237845913), (Int.ofNat 100835955889838113558031), (Int.negOfNat 168173250988169812219), (Int.negOfNat 497506654886994443688), (Int.negOfNat 2963243790615085140), (Int.ofNat 1786772564817022543), (Int.ofNat 14365993017241596), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-208417809507561039322134357960507/281474976710656000000000000000000), (43369208037539659623735157162287/1125899906842624000000000000000000), (406605865886181598133994567777/281474976710656000000000000000000), (1047328094250873868483992133883/1125899906842624000000000000000000), (-42061886864030058510373752101/562949953421312000000000000000000), (-58217096749125675741125496311/1125899906842624000000000000000000), (3324211327008999214127172557/1125899906842624000000000000000000), (1201240178537981904501359769/1125899906842624000000000000000000), (-19558562939924457791989221/562949953421312000000000000000000), (-13925192987884734224030893/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial139.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial139.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial139.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial139 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 734907669497101511449931639757277), (Int.ofNat 56199855324213323687495903761027), (Int.ofNat 2709775356968850074001007483674), (Int.negOfNat 887716833953946285262256611364), (Int.negOfNat 223835364211993655438445229851), (Int.ofNat 41318483266852080653853446714), (Int.ofNat 8416373689091456243302240164), (Int.negOfNat 771899788087849346719492746), (Int.negOfNat 143310896589506935837562968), (Int.ofNat 6459400788744612032097301), (Int.ofNat 1347972730538323170286642), (Int.negOfNat 29226177301266083613233), (Int.negOfNat 8087656664379879287429), (Int.ofNat 71124248943898688333), (Int.ofNat 33927131431486511902), (Int.ofNat 26903218036531688), (Int.negOfNat 133446827765029098), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-734907669497101511449931639757277/1125899906842624000000000000000000), (56199855324213323687495903761027/1125899906842624000000000000000000), (1354887678484425037000503741837/562949953421312000000000000000000), (-221929208488486571315564152841/281474976710656000000000000000000), (-223835364211993655438445229851/1125899906842624000000000000000000), (20659241633426040326926723357/562949953421312000000000000000000), (2104093422272864060825560041/281474976710656000000000000000000), (-385949894043924673359746373/562949953421312000000000000000000), (-17913862073688366979695371/140737488355328000000000000000000), (6459400788744612032097301/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial139.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial139.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial139.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial139 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 620622013614061514573999082788758), (Int.ofNat 53673747777681343851183372945541), (Int.negOfNat 3394748056745540570478709380076), (Int.negOfNat 314786897004959185786866156180), (Int.ofNat 359653444278507902287522557809), (Int.ofNat 35537502117108284055979672171), (Int.negOfNat 10440674094033829326481200903), (Int.negOfNat 1177876778850060296830459005), (Int.ofNat 122051735417755282534538043), (Int.ofNat 15583354635620924085002879), (Int.negOfNat 779015592293020753464493), (Int.negOfNat 117087010360477421885605), (Int.ofNat 3125026026971730784445), (Int.ofNat 584127844993347290723), (Int.negOfNat 8244289248627476735), (Int.negOfNat 2168657601565142509), (Int.ofNat 12904999014690380), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-310311006807030757286999541394379/562949953421312000000000000000000), (53673747777681343851183372945541/1125899906842624000000000000000000), (-848687014186385142619677345019/281474976710656000000000000000000), (-15739344850247959289343307809/56294995342131200000000000000000), (359653444278507902287522557809/1125899906842624000000000000000000), (35537502117108284055979672171/1125899906842624000000000000000000), (-10440674094033829326481200903/1125899906842624000000000000000000), (-235575355770012059366091801/225179981368524800000000000000000), (122051735417755282534538043/1125899906842624000000000000000000), (15583354635620924085002879/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial139.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial139.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial139.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial139 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 523260917859108152271448657674904), (Int.ofNat 48292608986775691908394574169494), (Int.ofNat 3172471423647014248116948596351), (Int.ofNat 1939916311415806637674275479842), (Int.negOfNat 56507586861462458426892957529), (Int.negOfNat 111846554930807184917379399053), (Int.negOfNat 6836111876024477523738996433), (Int.ofNat 1789283780960559903271322324), (Int.ofNat 153356631142481666391743686), (Int.negOfNat 14728100511932009080429113), (Int.negOfNat 1508574265208974378161972), (Int.ofNat 76156004408560035543623), (Int.ofNat 9081123531705442323715), (Int.negOfNat 272810982206304868395), (Int.negOfNat 38033475509392596411), (Int.ofNat 733403312214522079), (Int.ofNat 138478865590016642), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-65407614732388519033931082209363/140737488355328000000000000000000), (24146304493387845954197287084747/562949953421312000000000000000000), (3172471423647014248116948596351/1125899906842624000000000000000000), (969958155707903318837137739921/562949953421312000000000000000000), (-56507586861462458426892957529/1125899906842624000000000000000000), (-111846554930807184917379399053/1125899906842624000000000000000000), (-6836111876024477523738996433/1125899906842624000000000000000000), (447320945240139975817830581/281474976710656000000000000000000), (76678315571240833195871843/562949953421312000000000000000000), (-14728100511932009080429113/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial139.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial139.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial139.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial139 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 403127813616419835839516320612540), (Int.ofNat 73111030989710929757338750995643), (Int.ofNat 4262065252662367137522831621499), (Int.negOfNat 2901187133504291661005269941767), (Int.negOfNat 987808350931697951757260345036), (Int.negOfNat 13686582026689475097574829361), (Int.ofNat 22000192503383293739215849906), (Int.ofNat 1261317098569211237553041486), (Int.negOfNat 228442095100941294867684479), (Int.negOfNat 17333377521882424011345801), (Int.ofNat 1453895328790279655486408), (Int.ofNat 128250528235292294022564), (Int.negOfNat 6382146057953400992510), (Int.negOfNat 628649964473871930492), (Int.ofNat 20652512127513115688), (Int.ofNat 2281954986707970182), (Int.negOfNat 47358893419354511), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-20156390680820991791975816030627/56294995342131200000000000000000), (73111030989710929757338750995643/1125899906842624000000000000000000), (4262065252662367137522831621499/1125899906842624000000000000000000), (-2901187133504291661005269941767/1125899906842624000000000000000000), (-246952087732924487939315086259/281474976710656000000000000000000), (-13686582026689475097574829361/1125899906842624000000000000000000), (11000096251691646869607924953/562949953421312000000000000000000), (630658549284605618776520743/562949953421312000000000000000000), (-228442095100941294867684479/1125899906842624000000000000000000), (-17333377521882424011345801/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial139.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial139.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial139.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial139 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 277806066329679309408856119782834), (Int.ofNat 27164199936010394847619152891592), (Int.negOfNat 32289135540474486644055137346025), (Int.negOfNat 7600435926105300016839142640108), (Int.ofNat 246708534811970492351140831610), (Int.ofNat 233669864529709322621139347571), (Int.ofNat 8711784772358794914850264652), (Int.negOfNat 3035300066226553442759643295), (Int.negOfNat 180311205208704324470804537), (Int.ofNat 23466966155187480831611841), (Int.ofNat 1658536352725446988838946), (Int.negOfNat 123349404074832654426077), (Int.negOfNat 9565772078958946070951), (Int.ofNat 474687667993235440769), (Int.ofNat 38961736195530184877), (Int.negOfNat 1389859247509429663), (Int.negOfNat 132026271946782809), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-138903033164839654704428059891417/562949953421312000000000000000000), (3395524992001299355952394111449/140737488355328000000000000000000), (-1291565421618979465762205493841/45035996273704960000000000000000), (-1900108981526325004209785660027/281474976710656000000000000000000), (24670853481197049235114083161/112589990684262400000000000000000), (233669864529709322621139347571/1125899906842624000000000000000000), (2177946193089698728712566163/281474976710656000000000000000000), (-607060013245310688551928659/225179981368524800000000000000000), (-180311205208704324470804537/1125899906842624000000000000000000), (23466966155187480831611841/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial139.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial139.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial139.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial139 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 401876621557271932275239671832184), (Int.negOfNat 166420137047080303653353296948083), (Int.negOfNat 53425957038633037970033358740367), (Int.ofNat 3236537499369590746850074081237), (Int.ofNat 2164977773341674383948058616737), (Int.ofNat 58724630290765134587609288349), (Int.negOfNat 34894311061783935057146272649), (Int.negOfNat 1776236677878370978825654423), (Int.ofNat 327591309522141726387480796), (Int.ofNat 19994427374627077452296838), (Int.negOfNat 2055409449255563095110944), (Int.negOfNat 135099912144960046440936), (Int.ofNat 9306897490547043750969), (Int.ofNat 629140464958589428397), (Int.negOfNat 31966057094950088750), (Int.negOfNat 2214273112716252797), (Int.ofNat 81812787824018642), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-50234577694658991534404958979023/140737488355328000000000000000000), (-166420137047080303653353296948083/1125899906842624000000000000000000), (-53425957038633037970033358740367/1125899906842624000000000000000000), (3236537499369590746850074081237/1125899906842624000000000000000000), (2164977773341674383948058616737/1125899906842624000000000000000000), (58724630290765134587609288349/1125899906842624000000000000000000), (-34894311061783935057146272649/1125899906842624000000000000000000), (-1776236677878370978825654423/1125899906842624000000000000000000), (81897827380535431596870199/281474976710656000000000000000000), (9997213687313538726148419/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial139.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial139.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial139.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial139 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 888378423686782165118649813343110), (Int.negOfNat 274433984519649235506913306771308), (Int.ofNat 13734850355430196081481180982123), (Int.ofNat 16986023686415138067163087619636), (Int.ofNat 576779185517742097355755190409), (Int.negOfNat 341598552253107046446290747639), (Int.negOfNat 17879392795881666840890638446), (Int.ofNat 3945846721120859476950551292), (Int.ofNat 231216684253148558097641320), (Int.negOfNat 29846146143983694068854315), (Int.negOfNat 1795952240592346531026163), (Int.ofNat 159705666199937881468127), (Int.ofNat 9497474500241176407195), (Int.negOfNat 638298374942239063095), (Int.negOfNat 36702949942900291827), (Int.ofNat 1953821079250316421), (Int.ofNat 125573678303548976), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-88837842368678216511864981334311/112589990684262400000000000000000), (-68608496129912308876728326692827/281474976710656000000000000000000), (13734850355430196081481180982123/1125899906842624000000000000000000), (4246505921603784516790771904909/281474976710656000000000000000000), (576779185517742097355755190409/1125899906842624000000000000000000), (-341598552253107046446290747639/1125899906842624000000000000000000), (-8939696397940833420445319223/562949953421312000000000000000000), (986461680280214869237637823/281474976710656000000000000000000), (5780417106328713952441033/28147497671065600000000000000000), (-5969229228796738813770863/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial139.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial139.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial139.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial139 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 1248718269866198736032653199102410), (Int.negOfNat 26037553425719980819262183929906), (Int.ofNat 100787508800788598679875531988372), (Int.ofNat 7519193593129089834982565729867), (Int.negOfNat 2684962945836703575196741579600), (Int.negOfNat 190323452620302633018766641229), (Int.ofNat 39927866351310126794155075863), (Int.ofNat 2624870743361673703244494518), (Int.negOfNat 374675852459025797571643093), (Int.negOfNat 22809828192511651757660570), (Int.ofNat 2408207177807000413008829), (Int.ofNat 135377573595823930732659), (Int.negOfNat 11279914261880271847045), (Int.negOfNat 582941196515824158006), (Int.ofNat 40244841083726682856), (Int.ofNat 1898781923867190907), (Int.negOfNat 114115817680938162), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-124871826986619873603265319910241/112589990684262400000000000000000), (-13018776712859990409631091964953/562949953421312000000000000000000), (25196877200197149669968882997093/281474976710656000000000000000000), (7519193593129089834982565729867/1125899906842624000000000000000000), (-6712407364591758937991853949/2814749767106560000000000000000), (-190323452620302633018766641229/1125899906842624000000000000000000), (39927866351310126794155075863/1125899906842624000000000000000000), (1312435371680836851622247259/562949953421312000000000000000000), (-374675852459025797571643093/1125899906842624000000000000000000), (-2280982819251165175766057/112589990684262400000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial139.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial139.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial139.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial139.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial139 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial139 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial139 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 1503228554621702844966459053047679), (Int.ofNat 15647708592854488484814888541968), (Int.ofNat 111918578053385278926926601281659), (Int.negOfNat 11620766560192315734277301715821), (Int.negOfNat 2874851888229795784777377723286), (Int.ofNat 301578969761986083678222134352), (Int.ofNat 42049818598428651693351631692), (Int.negOfNat 3892889383664107172191030586), (Int.negOfNat 390607983963041671801214603), (Int.ofNat 31130019488680931165624209), (Int.ofNat 2490714179047356315082805), (Int.negOfNat 171391815685986770776507), (Int.negOfNat 11585010360025721105809), (Int.ofNat 694150925831531395834), (Int.ofNat 41040067573607258416), (Int.negOfNat 2137349870831363575), (Int.negOfNat 114115817680938162), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1503228554621702844966459053047679/1125899906842624000000000000000000), (977981787053405530300930533873/70368744177664000000000000000000), (111918578053385278926926601281659/1125899906842624000000000000000000), (-11620766560192315734277301715821/1125899906842624000000000000000000), (-1437425944114897892388688861643/562949953421312000000000000000000), (18848685610124130229888883397/70368744177664000000000000000000), (10512454649607162923337907923/281474976710656000000000000000000), (-1946444691832053586095515293/562949953421312000000000000000000), (-390607983963041671801214603/1125899906842624000000000000000000), (31130019488680931165624209/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial139.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial139.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial139.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 1151461061096040479212586346554657), (Int.ofNat 262015749240279916640970260052150), (Int.ofNat 4266471208766259327612222861284), (Int.negOfNat 18511142171584802032809609982122), (Int.ofNat 1287010232261229572294450130592), (Int.ofNat 381046117199806896450367663291), (Int.negOfNat 29951755054485822750397809377), (Int.negOfNat 4377186829118614031118377633), (Int.ofNat 334476212638303727912659851), (Int.ofNat 32600824458364310069954577), (Int.negOfNat 2342837575768491325037618), (Int.negOfNat 171406938318714448437319), (Int.ofNat 11489628424663942349100), (Int.ofNat 674007780674943529154), (Int.negOfNat 42054029671521167493), (Int.negOfNat 2033343728238373977), (Int.ofNat 125573678303548976), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-1151461061096040479212586346554657/1125899906842624000000000000000000), (5240314984805598332819405201043/22517998136852480000000000000000), (1066617802191564831903055715321/281474976710656000000000000000000), (-9255571085792401016404804991061/562949953421312000000000000000000), (40219069758163424134201566581/35184372088832000000000000000000), (381046117199806896450367663291/1125899906842624000000000000000000), (-29951755054485822750397809377/1125899906842624000000000000000000), (-4377186829118614031118377633/1125899906842624000000000000000000), (334476212638303727912659851/1125899906842624000000000000000000), (32600824458364310069954577/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial139.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial139.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial139.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 728044748663456031831496249315684), (Int.ofNat 121308231038354249534122679061638), (Int.negOfNat 54839680974378474276150987083297), (Int.ofNat 516153127776111623159866842103), (Int.ofNat 2543740522731449534669893856879), (Int.negOfNat 153112260434345135839387874509), (Int.negOfNat 41478325303438191632603670220), (Int.ofNat 2858925590913894899736130664), (Int.ofNat 382742242172481413120619451), (Int.negOfNat 27188568966630593055178849), (Int.negOfNat 2339603925450458378635227), (Int.ofNat 166609757897448081027109), (Int.ofNat 10315019699974919209649), (Int.negOfNat 727618980834317777969), (Int.negOfNat 34606777544713859108), (Int.ofNat 2399825960355053761), (Int.ofNat 81812787824018642), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-182011187165864007957874062328921/281474976710656000000000000000000), (60654115519177124767061339530819/562949953421312000000000000000000), (-54839680974378474276150987083297/1125899906842624000000000000000000), (516153127776111623159866842103/1125899906842624000000000000000000), (2543740522731449534669893856879/1125899906842624000000000000000000), (-153112260434345135839387874509/1125899906842624000000000000000000), (-2073916265171909581630183511/56294995342131200000000000000000), (357365698864236862467016333/140737488355328000000000000000000), (382742242172481413120619451/1125899906842624000000000000000000), (-27188568966630593055178849/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial139.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial139.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial139.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 667064157040297623049130594729158), (Int.negOfNat 29069584293421865573334174788048), (Int.negOfNat 10436671693104228075473558325243), (Int.ofNat 10217790614255052896959063811526), (Int.negOfNat 379929579270539583667796362374), (Int.negOfNat 307207781568833796753684497179), (Int.ofNat 18175421103439398366835426548), (Int.ofNat 3871988328060563934358425452), (Int.negOfNat 260586707900649073217785595), (Int.negOfNat 28853419344539708100299724), (Int.ofNat 2090271612844368739445239), (Int.ofNat 146120700116927264436278), (Int.negOfNat 11169189893416225248325), (Int.negOfNat 543498161854010006206), (Int.ofNat 43347013013083860164), (Int.ofNat 1495889446160173071), (Int.negOfNat 132026271946782809), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-333532078520148811524565297364579/562949953421312000000000000000000), (-1816849018338866598333385924253/70368744177664000000000000000000), (-10436671693104228075473558325243/1125899906842624000000000000000000), (5108895307127526448479531905763/562949953421312000000000000000000), (-189964789635269791833898181187/562949953421312000000000000000000), (-307207781568833796753684497179/1125899906842624000000000000000000), (4543855275859849591708856637/281474976710656000000000000000000), (967997082015140983589606363/281474976710656000000000000000000), (-52117341580129814643557119/225179981368524800000000000000000), (-7213354836134927025074931/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial139.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial139.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial139.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 699537461211041283707977874852222), (Int.ofNat 19965909742138472140719187820189), (Int.ofNat 23566659088950243593299511552262), (Int.negOfNat 618767766258832918855481785875), (Int.negOfNat 1652820653484461859834742589354), (Int.ofNat 81146053054425168294425859251), (Int.ofNat 32247929730490935736770581065), (Int.negOfNat 1996066434771823098173759194), (Int.negOfNat 312501630777507253287593143), (Int.ofNat 22297179877264424847640341), (Int.ofNat 1885644294443596696104184), (Int.negOfNat 150721528265999878009028), (Int.negOfNat 7915442021822179392590), (Int.ofNat 701290655653965083635), (Int.ofNat 24679861676315485855), (Int.negOfNat 2467507834346771146), (Int.negOfNat 47358893419354511), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-349768730605520641853988937426111/562949953421312000000000000000000), (19965909742138472140719187820189/1125899906842624000000000000000000), (11783329544475121796649755776131/562949953421312000000000000000000), (-4950142130070663350843854287/9007199254740992000000000000000), (-826410326742230929917371294677/562949953421312000000000000000000), (81146053054425168294425859251/1125899906842624000000000000000000), (6449585946098187147354116213/225179981368524800000000000000000), (-998033217385911549086879597/562949953421312000000000000000000), (-312501630777507253287593143/1125899906842624000000000000000000), (22297179877264424847640341/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial139.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial139.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial139.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 592396221655239094215062049709892), (Int.ofNat 65445293802199586691483633326366), (Int.negOfNat 7364007588307580249207317743520), (Int.negOfNat 6971828131569774452099118919254), (Int.ofNat 292765924756857399234207417765), (Int.ofNat 215597417736877218275092594633), (Int.negOfNat 11907576756879073940257135144), (Int.negOfNat 2887835653404111758533651771), (Int.ofNat 198143734233422866232582171), (Int.ofNat 21705093755667262417245707), (Int.negOfNat 1765918590882820559444158), (Int.negOfNat 105774903633214145022878), (Int.ofNat 10098384295734047271620), (Int.ofNat 363073051506865929768), (Int.negOfNat 40944364062340678828), (Int.negOfNat 918956159853323043), (Int.ofNat 138478865590016642), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-148099055413809773553765512427473/281474976710656000000000000000000), (32722646901099793345741816663183/562949953421312000000000000000000), (-46025047426922376557545735897/7036874417766400000000000000000), (-3485914065784887226049559459627/562949953421312000000000000000000), (58553184951371479846841483553/225179981368524800000000000000000), (215597417736877218275092594633/1125899906842624000000000000000000), (-1488447094609884242532141893/140737488355328000000000000000000), (-2887835653404111758533651771/1125899906842624000000000000000000), (198143734233422866232582171/1125899906842624000000000000000000), (21705093755667262417245707/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial139.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial139.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial139.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 536224788647299887927701170286690), (Int.negOfNat 24393438800248192948711050211544), (Int.negOfNat 29286751405819760789010809611790), (Int.ofNat 913175627496176695020467878814), (Int.ofNat 1208294575663095683413768014698), (Int.negOfNat 53614032874201687616412769241), (Int.negOfNat 22412464647352149004090505176), (Int.ofNat 1431282848056700422595288230), (Int.ofNat 218073940627983199403377083), (Int.negOfNat 17688183551722623458086045), (Int.negOfNat 1275441186840708956881292), (Int.ofNat 128160590708598698343567), (Int.ofNat 4915929952186185376687), (Int.negOfNat 623821580845569994476), (Int.negOfNat 13037063131016162408), (Int.ofNat 2220025397574727112), (Int.ofNat 12904999014690380), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-53622478864729988792770117028669/112589990684262400000000000000000), (-3049179850031024118588881276443/140737488355328000000000000000000), (-2928675140581976078901080961179/112589990684262400000000000000000), (456587813748088347510233939407/562949953421312000000000000000000), (604147287831547841706884007349/562949953421312000000000000000000), (-53614032874201687616412769241/1125899906842624000000000000000000), (-2801558080919018625511313147/140737488355328000000000000000000), (143128284805670042259528823/112589990684262400000000000000000), (218073940627983199403377083/1125899906842624000000000000000000), (-3537636710344524691617209/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial139.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial139.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial139.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 678441654341086656745306240595802), (Int.negOfNat 99690457470664850542955454834450), (Int.negOfNat 3216492993463627336354946891828), (Int.ofNat 5932379965268899956370821357015), (Int.negOfNat 110251399415946046261496481714), (Int.negOfNat 146507537944978471402242618536), (Int.ofNat 7921895557520704091170861662), (Int.ofNat 1879623837778189677042855717), (Int.negOfNat 148167904514925686234348608), (Int.negOfNat 13618311381182377938789880), (Int.ofNat 1415044602475631353773783), (Int.ofNat 60412726492922896522508), (Int.negOfNat 8461202199203404274398), (Int.negOfNat 168625974006535666162), (Int.ofNat 35206233725168673438), (Int.ofNat 239819581906113933), (Int.negOfNat 133446827765029098), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-339220827170543328372653120297901/562949953421312000000000000000000), (-1993809149413297010859109096689/22517998136852480000000000000000), (-804123248365906834088736722957/281474976710656000000000000000000), (1186475993053779991274164271403/225179981368524800000000000000000), (-55125699707973023130748240857/562949953421312000000000000000000), (-18313442243122308925280327317/140737488355328000000000000000000), (3960947778760352045585430831/562949953421312000000000000000000), (1879623837778189677042855717/1125899906842624000000000000000000), (-2315123508045713847411697/17592186044416000000000000000000), (-340457784529559448469747/28147497671065600000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial139.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial139.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial139.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 848977538259645900259191862967798), (Int.negOfNat 54428830128181530916543537364200), (Int.ofNat 20864659181945812362300235442115), (Int.ofNat 1194741719283862943209419520165), (Int.negOfNat 774103260778291861415189647026), (Int.ofNat 24929772862328210447152993567), (Int.ofNat 13627535217161116679084829672), (Int.negOfNat 992325031419111893555466356), (Int.negOfNat 126151494065414377022690084), (Int.ofNat 13344008750538654205482491), (Int.ofNat 661841465429220447866768), (Int.negOfNat 101029774933416877579323), (Int.negOfNat 1938092704035179128457), (Int.ofNat 505039172808660425848), (Int.ofNat 1922381863898047133), (Int.negOfNat 1866295213805080099), (Int.ofNat 14365993017241596), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-424488769129822950129595931483899/562949953421312000000000000000000), (-272144150640907654582717686821/5629499534213120000000000000000), (4172931836389162472460047088423/225179981368524800000000000000000), (238948343856772588641883904033/225179981368524800000000000000000), (-387051630389145930707594823513/562949953421312000000000000000000), (24929772862328210447152993567/1125899906842624000000000000000000), (1703441902145139584885603709/140737488355328000000000000000000), (-248081257854777973388866589/281474976710656000000000000000000), (-31537873516353594255672521/281474976710656000000000000000000), (13344008750538654205482491/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial139.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial139.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial139.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 875686378487225861776255542891387), (Int.ofNat 22665504997562440718840986032230), (Int.ofNat 13892933097860999831856377350215), (Int.negOfNat 2524689820685180844485799095521), (Int.negOfNat 67927098701896358329579447380), (Int.ofNat 77806863166120904979891190635), (Int.negOfNat 4703327152588323369077658694), (Int.negOfNat 982944818089873758487494065), (Int.ofNat 104220551112522260678505054), (Int.ofNat 6303266302490333600551743), (Int.negOfNat 1044922528770374581901847), (Int.negOfNat 19267904488333417230615), (Int.ofNat 6403539282676530735422), (Int.negOfNat 4485319124277254238), (Int.negOfNat 27036409809519712152), (Int.ofNat 309407701523666577), (Int.ofNat 114779293924075566), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-875686378487225861776255542891387/1125899906842624000000000000000000), (2266550499756244071884098603223/112589990684262400000000000000000), (2778586619572199966371275470043/225179981368524800000000000000000), (-2524689820685180844485799095521/1125899906842624000000000000000000), (-3396354935094817916478972369/56294995342131200000000000000000), (15561372633224180995978238127/225179981368524800000000000000000), (-2351663576294161684538829347/562949953421312000000000000000000), (-196588963617974751697498813/225179981368524800000000000000000), (52110275556261130339252527/562949953421312000000000000000000), (6303266302490333600551743/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial139.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial139.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial139.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 793976174462860121221055077709611), (Int.ofNat 50764275021691364954206032013981), (Int.ofNat 1753406395428497204714036237030), (Int.negOfNat 1054327098635228862118213897086), (Int.ofNat 280785008964949129073698786796), (Int.negOfNat 10176626855119405629038576087), (Int.negOfNat 5993549372745931890676612866), (Int.ofNat 638257322048290047944649069), (Int.ofNat 49992032659082118802173493), (Int.negOfNat 9141288211287138768721583), (Int.negOfNat 155020093690759009239344), (Int.ofNat 70808025429569059725922), (Int.negOfNat 487573129856585640217), (Int.negOfNat 357063439297896356932), (Int.ofNat 7005670626083155355), (Int.ofNat 1259165667349018129), (Int.negOfNat 32303218128696806), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-793976174462860121221055077709611/1125899906842624000000000000000000), (50764275021691364954206032013981/1125899906842624000000000000000000), (175340639542849720471403623703/112589990684262400000000000000000), (-527163549317614431059106948543/562949953421312000000000000000000), (70196252241237282268424696699/281474976710656000000000000000000), (-10176626855119405629038576087/1125899906842624000000000000000000), (-2996774686372965945338306433/562949953421312000000000000000000), (638257322048290047944649069/1125899906842624000000000000000000), (49992032659082118802173493/1125899906842624000000000000000000), (-9141288211287138768721583/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial139.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial139.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial139.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 689995498639228480030302750385421), (Int.ofNat 52462247646604864517394473034818), (Int.ofNat 390195352561466150834104767481), (Int.ofNat 224243969171702360808728578337), (Int.ofNat 17976589668660945313303582814), (Int.negOfNat 23830823948066871547616664479), (Int.ofNat 2825186950058618146257000500), (Int.ofNat 300167480983998273630193075), (Int.negOfNat 65312047428631706750987782), (Int.negOfNat 818994903302430986537554), (Int.ofNat 666953837588925015388871), (Int.negOfNat 11046727749039625806086), (Int.negOfNat 4099457002620344439628), (Int.ofNat 128280022901546140662), (Int.ofNat 17202433867165027724), (Int.negOfNat 745469043407485859), (Int.negOfNat 80325399519411435), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-689995498639228480030302750385421/1125899906842624000000000000000000), (26231123823302432258697236517409/562949953421312000000000000000000), (390195352561466150834104767481/1125899906842624000000000000000000), (224243969171702360808728578337/1125899906842624000000000000000000), (8988294834330472656651791407/562949953421312000000000000000000), (-23830823948066871547616664479/1125899906842624000000000000000000), (5650373900117236292514001/2251799813685248000000000000000), (12006699239359930945207723/45035996273704960000000000000000), (-32656023714315853375493891/562949953421312000000000000000000), (-409497451651215493268777/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial139.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial139.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial139.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 581988492069106779532846653958319), (Int.ofNat 55994084296903573421487684454269), (Int.ofNat 1026697086628272361815495890806), (Int.negOfNat 77129762192777889002403914632), (Int.negOfNat 35185154024629140047742008770), (Int.ofNat 9068044548247405461820824319), (Int.ofNat 1036690731964501354126241627), (Int.negOfNat 364468142178826433167205305), (Int.ofNat 822684577189042070508127), (Int.ofNat 5160655550084192042384878), (Int.negOfNat 176424351973364209180937), (Int.negOfNat 39653743095255150414904), (Int.ofNat 2005752565572740032499), (Int.ofNat 195906772643358046737), (Int.negOfNat 12159926080475751278), (Int.negOfNat 641697280960844949), (Int.ofNat 38755811771930639), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-581988492069106779532846653958319/1125899906842624000000000000000000), (55994084296903573421487684454269/1125899906842624000000000000000000), (513348543314136180907747945403/562949953421312000000000000000000), (-9641220274097236125300489329/140737488355328000000000000000000), (-3518515402462914004774200877/112589990684262400000000000000000), (9068044548247405461820824319/1125899906842624000000000000000000), (1036690731964501354126241627/1125899906842624000000000000000000), (-72893628435765286633441061/225179981368524800000000000000000), (822684577189042070508127/1125899906842624000000000000000000), (2580327775042096021192439/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial139.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial139.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial139.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 466761061385767347865105470442760), (Int.ofNat 58822037835296798474078556630134), (Int.ofNat 471068872308574373992642781261), (Int.negOfNat 9014607135910664742123171489), (Int.ofNat 33640561251129848807303306792), (Int.negOfNat 675974098471721405188550455), (Int.negOfNat 1533843520905971837045231578), (Int.ofNat 79266641030213939964106109), (Int.ofNat 30838971049074959810950124), (Int.negOfNat 2241197233479101184752745), (Int.negOfNat 304038238067561780018229), (Int.ofNat 26858673728874225503860), (Int.ofNat 1780735909441088335375), (Int.negOfNat 186100181283100828196), (Int.negOfNat 6936269674781255599), (Int.ofNat 873322229402735065), (Int.ofNat 45871505114747304), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-11669026534644183696627636761069/28147497671065600000000000000000), (29411018917648399237039278315067/562949953421312000000000000000000), (471068872308574373992642781261/1125899906842624000000000000000000), (-9014607135910664742123171489/1125899906842624000000000000000000), (4205070156391231100912913349/140737488355328000000000000000000), (-135194819694344281037710091/225179981368524800000000000000000), (-766921760452985918522615789/562949953421312000000000000000000), (79266641030213939964106109/1125899906842624000000000000000000), (7709742762268739952737531/281474976710656000000000000000000), (-448239446695820236950549/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial139.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial139.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial139.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 346869732488414431370335332462194), (Int.ofNat 61386766102297064729868924914157), (Int.ofNat 897700148402677262689154639501), (Int.ofNat 71867119540868094787155852320), (Int.negOfNat 20250805484078798270521247010), (Int.negOfNat 4668822329405264015715682980), (Int.ofNat 960687624861084371748710124), (Int.ofNat 123023451057343437661941766), (Int.negOfNat 22930241390387134212754874), (Int.negOfNat 1565606044152501939692651), (Int.ofNat 305569797631470622468255), (Int.ofNat 10538409693813538895251), (Int.negOfNat 2460031753275618994732), (Int.negOfNat 40920409767910230636), (Int.ofNat 13149616445549433449), (Int.ofNat 30688416216908155), (Int.negOfNat 45208405415164472), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-173434866244207215685167666231097/562949953421312000000000000000000), (61386766102297064729868924914157/1125899906842624000000000000000000), (897700148402677262689154639501/1125899906842624000000000000000000), (449169497130425592419724077/7036874417766400000000000000000), (-2025080548407879827052124701/112589990684262400000000000000000), (-233441116470263200785784149/56294995342131200000000000000000), (240171906215271092937177531/281474976710656000000000000000000), (61511725528671718830970883/562949953421312000000000000000000), (-11465120695193567106377437/562949953421312000000000000000000), (-1565606044152501939692651/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial139.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial139.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial139.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 220332994368406861653189728646793), (Int.ofNat 65032541467097371980993531210491), (Int.ofNat 737958249905363952264390491925), (Int.negOfNat 98937388570117544378385740111), (Int.negOfNat 2606940081142250290612930202), (Int.ofNat 6290556183496531108314084247), (Int.ofNat 100732300744775786480591829), (Int.negOfNat 181519290322166908334973575), (Int.negOfNat 925127087849250400465644), (Int.ofNat 2867146435168783160519065), (Int.negOfNat 10800816035488870773155), (Int.negOfNat 27537630192958627966475), (Int.ofNat 273158577734394966512), (Int.ofNat 173766057139317730733), (Int.negOfNat 2257110196806929969), (Int.negOfNat 791246774842260797), (Int.negOfNat 9266746162338562), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-220332994368406861653189728646793/1125899906842624000000000000000000), (65032541467097371980993531210491/1125899906842624000000000000000000), (29518329996214558090575619677/45035996273704960000000000000000), (-98937388570117544378385740111/1125899906842624000000000000000000), (-1303470040571125145306465101/562949953421312000000000000000000), (6290556183496531108314084247/1125899906842624000000000000000000), (100732300744775786480591829/1125899906842624000000000000000000), (-7260771612886676333398943/45035996273704960000000000000000), (-231281771962312600116411/281474976710656000000000000000000), (573429287033756632103813/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial139.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial139.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial139.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 87963612219966031757232450097864), (Int.ofNat 67160276778919732409802557371854), (Int.ofNat 497905440124661796391080002947), (Int.ofNat 58801091262262247790832462617), (Int.ofNat 24826762782201169659845418686), (Int.negOfNat 3203598984198890272389736102), (Int.negOfNat 1010163183233491947252280774), (Int.ofNat 84589072784137304929262922), (Int.ofNat 20686323321474633351639896), (Int.negOfNat 1305624039668750439287416), (Int.negOfNat 247217792730479686908912), (Int.ofNat 12921025880345533898277), (Int.ofNat 1892411671434387140069), (Int.negOfNat 86582088936929699659), (Int.negOfNat 9956146649498346744), (Int.ofNat 469254051213446287), (Int.ofNat 26540871574210940), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-10995451527495753969654056262233/140737488355328000000000000000000), (33580138389459866204901278685927/562949953421312000000000000000000), (497905440124661796391080002947/1125899906842624000000000000000000), (58801091262262247790832462617/1125899906842624000000000000000000), (12413381391100584829922709343/562949953421312000000000000000000), (-1601799492099445136194868051/562949953421312000000000000000000), (-505081591616745973626140387/562949953421312000000000000000000), (42294536392068652464631461/562949953421312000000000000000000), (2585790415184329168954987/140737488355328000000000000000000), (-163203004958593804910927/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial139.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial139.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial139.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 49064269248216963508204288351209), (Int.ofNat 70256719998580846378772883572133), (Int.ofNat 1033351332210445834499463078081), (Int.ofNat 41995697988092541669749688632), (Int.negOfNat 28807170344936101561201480858), (Int.negOfNat 3041561111738761913160749794), (Int.ofNat 1060519597443530116693418584), (Int.ofNat 93405947803376057654278217), (Int.negOfNat 20304998481172661714608244), (Int.negOfNat 1528120419173415999381837), (Int.ofNat 233628837901160308704609), (Int.ofNat 15143167948670532211311), (Int.negOfNat 1763976077742265107618), (Int.negOfNat 98900319200293574641), (Int.ofNat 9293330504122291820), (Int.ofNat 526114391879995017), (Int.negOfNat 18004245869593414), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(49064269248216963508204288351209/1125899906842624000000000000000000), (70256719998580846378772883572133/1125899906842624000000000000000000), (1033351332210445834499463078081/1125899906842624000000000000000000), (5249462248511567708718711079/140737488355328000000000000000000), (-14403585172468050780600740429/562949953421312000000000000000000), (-1520780555869380956580374897/562949953421312000000000000000000), (132564949680441264586677323/140737488355328000000000000000000), (93405947803376057654278217/1125899906842624000000000000000000), (-5076249620293165428652061/281474976710656000000000000000000), (-1528120419173415999381837/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial139.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial139.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial139.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 193562946591703350433132316101139), (Int.ofNat 73951391163019588099706206299434), (Int.ofNat 627480474335036321319882218819), (Int.negOfNat 128727305733375488467408867487), (Int.ofNat 5189403791802176809104524077), (Int.ofNat 7484287870692106464901485338), (Int.negOfNat 42071414378408983123376832), (Int.negOfNat 198269689971800907020223492), (Int.negOfNat 1790183984327931983601768), (Int.ofNat 2920208814637455502501748), (Int.ofNat 46158108159885563309163), (Int.negOfNat 26839402531671683009172), (Int.negOfNat 506293164265156526857), (Int.ofNat 166271829323931030024), (Int.ofNat 3286975359577850833), (Int.negOfNat 758237690399822325), (Int.ofNat 5762158282708580), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(193562946591703350433132316101139/1125899906842624000000000000000000), (36975695581509794049853103149717/562949953421312000000000000000000), (627480474335036321319882218819/1125899906842624000000000000000000), (-128727305733375488467408867487/1125899906842624000000000000000000), (5189403791802176809104524077/1125899906842624000000000000000000), (3742143935346053232450742669/562949953421312000000000000000000), (-657365849662640361302763/17592186044416000000000000000000), (-49567422492950226755055873/281474976710656000000000000000000), (-223772998040991497950221/140737488355328000000000000000000), (730052203659363875625437/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial139.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial139.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial139.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 343241317427034294171341834283003), (Int.ofNat 75589312436052581701895150014388), (Int.ofNat 445088167331118313921665054265), (Int.ofNat 106456026236361151598143738322), (Int.ofNat 31246406871783137759138130043), (Int.negOfNat 5006940092128798820844432274), (Int.negOfNat 1290488004729416010351905140), (Int.ofNat 101832828730692642509995607), (Int.ofNat 26505807354312214329327398), (Int.negOfNat 1079200263397533177748364), (Int.negOfNat 316316451532572856897645), (Int.ofNat 6434937659463481696323), (Int.ofNat 2417401233860846283863), (Int.negOfNat 21267182414901028017), (Int.negOfNat 12679833332395047311), (Int.negOfNat 15167659464479963), (Int.ofNat 24456839512827247), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(343241317427034294171341834283003/1125899906842624000000000000000000), (18897328109013145425473787503597/281474976710656000000000000000000), (89017633466223662784333010853/225179981368524800000000000000000), (53228013118180575799071869161/562949953421312000000000000000000), (31246406871783137759138130043/1125899906842624000000000000000000), (-2503470046064399410422216137/562949953421312000000000000000000), (-64524400236470800517595257/56294995342131200000000000000000), (101832828730692642509995607/1125899906842624000000000000000000), (13252903677156107164663699/562949953421312000000000000000000), (-269800065849383294437091/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial139.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial139.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial139.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 497328038706218858420164304366369), (Int.ofNat 79067479913551014782823114255068), (Int.ofNat 1231115496537805746178128207600), (Int.ofNat 44064698055920852959732372845), (Int.negOfNat 46097395600653591515818603663), (Int.negOfNat 4374826686511729224049422755), (Int.ofNat 1539912831598483418631414785), (Int.ofNat 154518342823068899219928107), (Int.negOfNat 25352377565443082582023226), (Int.negOfNat 2714267883852672194929118), (Int.ofNat 237682434931968978400050), (Int.ofNat 27723934949113600814951), (Int.negOfNat 1394254949809106336595), (Int.negOfNat 182049857987925209263), (Int.ofNat 5449451754055777198), (Int.ofNat 852427114054225562), (Int.negOfNat 40216052687372711), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(497328038706218858420164304366369/1125899906842624000000000000000000), (19766869978387753695705778563767/281474976710656000000000000000000), (3077788741344514365445320519/2814749767106560000000000000000), (8812939611184170591946474569/225179981368524800000000000000000), (-46097395600653591515818603663/1125899906842624000000000000000000), (-874965337302345844809884551/225179981368524800000000000000000), (307982566319696683726282957/225179981368524800000000000000000), (154518342823068899219928107/1125899906842624000000000000000000), (-12676188782721541291011613/562949953421312000000000000000000), (-1357133941926336097464559/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial139.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial139.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial139.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 659973171254470118907209252105946), (Int.ofNat 83029774534762689396812117777813), (Int.ofNat 458054866884455169603617721275), (Int.negOfNat 222197543226757626864883740513), (Int.ofNat 10605612866545107559798957802), (Int.ofNat 12796894859683373668428322339), (Int.ofNat 131910254490002203233806144), (Int.negOfNat 319112882082875796109715295), (Int.negOfNat 11716633973692065138537859), (Int.ofNat 4180625401303514069908309), (Int.ofNat 216372263247405618112613), (Int.negOfNat 32552079585852140451157), (Int.negOfNat 2030493833746771646260), (Int.ofNat 165163743700246439626), (Int.ofNat 11844618798251301677), (Int.negOfNat 535258077179684213), (Int.negOfNat 30909433156061080), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(329986585627235059453604626052973/562949953421312000000000000000000), (83029774534762689396812117777813/1125899906842624000000000000000000), (18322194675378206784144708851/45035996273704960000000000000000), (-222197543226757626864883740513/1125899906842624000000000000000000), (5302806433272553779899478901/562949953421312000000000000000000), (12796894859683373668428322339/1125899906842624000000000000000000), (2061097726406284425528221/17592186044416000000000000000000), (-63822576416575159221943059/225179981368524800000000000000000), (-11716633973692065138537859/1125899906842624000000000000000000), (4180625401303514069908309/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial139.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial139.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial139.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 826633434822563221220203736209486), (Int.ofNat 83439454450363522340433685447771), (Int.ofNat 220107534691337323652911527882), (Int.ofNat 220180065855899610296027677366), (Int.ofNat 62217574909638998405061226024), (Int.negOfNat 8605749921312577102112101090), (Int.negOfNat 2669355052057001553820502967), (Int.ofNat 101932430283119153924842164), (Int.ofNat 51887220747113878868462610), (Int.ofNat 173675614390530937505777), (Int.negOfNat 544469744036818236860019), (Int.negOfNat 13142867054385530782816), (Int.ofNat 3482471108007756428772), (Int.ofNat 125693043646609397973), (Int.negOfNat 15055549590587086601), (Int.negOfNat 686114629586026185), (Int.ofNat 74669947092036842), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(413316717411281610610101868104743/562949953421312000000000000000000), (83439454450363522340433685447771/1125899906842624000000000000000000), (110053767345668661826455763941/562949953421312000000000000000000), (110090032927949805148013838683/562949953421312000000000000000000), (7777196863704874800632653253/140737488355328000000000000000000), (-860574992131257710211210109/112589990684262400000000000000000), (-2669355052057001553820502967/1125899906842624000000000000000000), (25483107570779788481210541/281474976710656000000000000000000), (5188722074711387886846261/112589990684262400000000000000000), (173675614390530937505777/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial139.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial139.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial139.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 996729322843516165783996675521640), (Int.ofNat 87848384694276539753855058452787), (Int.ofNat 1861192276639522152610444037364), (Int.ofNat 89090248155667940103221626677), (Int.negOfNat 104048613132137187015347574178), (Int.negOfNat 12881848980547487092326746873), (Int.ofNat 2882756746560332949478799481), (Int.ofNat 459717203305893550679084033), (Int.negOfNat 30846687840236129512235134), (Int.negOfNat 7137958685101206082034591), (Int.ofNat 96673045182755708231535), (Int.ofNat 59175550525987824742913), (Int.ofNat 527921361870477464261), (Int.negOfNat 311684089298319549296), (Int.negOfNat 6526995799655826098), (Int.ofNat 1161379555801521619), (Int.ofNat 25877395331073536), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(24918233071087904144599916888041/28147497671065600000000000000000), (87848384694276539753855058452787/1125899906842624000000000000000000), (465298069159880538152611009341/281474976710656000000000000000000), (89090248155667940103221626677/1125899906842624000000000000000000), (-52024306566068593507673787089/562949953421312000000000000000000), (-12881848980547487092326746873/1125899906842624000000000000000000), (2882756746560332949478799481/1125899906842624000000000000000000), (459717203305893550679084033/1125899906842624000000000000000000), (-15423343920118064756117567/562949953421312000000000000000000), (-7137958685101206082034591/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial139.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial139.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial139.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 1178738594918984813326364139599431), (Int.ofNat 92714700419018753602627857300087), (Int.negOfNat 216593720966202041794799520042), (Int.negOfNat 629590793648327858998877759700), (Int.ofNat 9238936582560819495694373895), (Int.ofNat 34595195486367792714476955370), (Int.ofNat 2227812355638023734149846644), (Int.negOfNat 678133997803643949789154174), (Int.negOfNat 72709227878833134253161948), (Int.ofNat 5156426367374663123129219), (Int.ofNat 839504612693059723301184), (Int.negOfNat 17362864362980870337299), (Int.negOfNat 5496855936987697332821), (Int.ofNat 215945562589478677), (Int.ofNat 24047916323768356808), (Int.ofNat 332384445816379172), (Int.negOfNat 101940939123968818), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(1178738594918984813326364139599431/1125899906842624000000000000000000), (92714700419018753602627857300087/1125899906842624000000000000000000), (-108296860483101020897399760021/562949953421312000000000000000000), (-6295907936483278589988777597/11258999068426240000000000000000), (1847787316512163899138874779/225179981368524800000000000000000), (3459519548636779271447695537/112589990684262400000000000000000), (556953088909505933537461661/281474976710656000000000000000000), (-339066998901821974894577087/562949953421312000000000000000000), (-18177306969708283563290487/281474976710656000000000000000000), (5156426367374663123129219/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial139.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial139.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial139.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 1359560371110908215375194574049502), (Int.ofNat 87421830119416005876422288938453), (Int.negOfNat 1023533814050373197630796913682), (Int.ofNat 713809868342451762636787896994), (Int.ofNat 248216423821726548972568367231), (Int.negOfNat 12088653381984999449485210165), (Int.negOfNat 9686776995127867391109886389), (Int.negOfNat 513429261886110317933260877), (Int.ofNat 109363510123804431127579935), (Int.ofNat 9967972096612020780376487), (Int.negOfNat 622233174955136128507185), (Int.negOfNat 84287127582606851629247), (Int.ofNat 1966592396045118347463), (Int.ofNat 443575669860106231703), (Int.negOfNat 2512309617895972429), (Int.negOfNat 1710606839231302129), (Int.negOfNat 7209861490120004), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(679780185555454107687597287024751/562949953421312000000000000000000), (87421830119416005876422288938453/1125899906842624000000000000000000), (-511766907025186598815398456841/562949953421312000000000000000000), (356904934171225881318393948497/562949953421312000000000000000000), (248216423821726548972568367231/1125899906842624000000000000000000), (-2417730676396999889897042033/225179981368524800000000000000000), (-9686776995127867391109886389/1125899906842624000000000000000000), (-513429261886110317933260877/1125899906842624000000000000000000), (21872702024760886225515987/225179981368524800000000000000000), (9967972096612020780376487/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial139.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial139.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial139.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 1538951630705206083238943066710886), (Int.ofNat 96910259524538341293892221350818), (Int.ofNat 5812147902638519730384811413039), (Int.ofNat 615386264384208701304529766632), (Int.negOfNat 446477704449877114271051553197), (Int.negOfNat 109539833912786720235816604793), (Int.negOfNat 1056850680660700524949001273), (Int.ofNat 1724139988274931534523534872), (Int.ofNat 97546016942924070737744516), (Int.negOfNat 13159829476575854844210339), (Int.negOfNat 1134316515064001389943952), (Int.ofNat 60503365706696180105687), (Int.ofNat 7275904435587426516625), (Int.negOfNat 178523885118647004165), (Int.negOfNat 31524714817501165439), (Int.ofNat 329407503280841603), (Int.ofNat 119878164235424028), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(769475815352603041619471533355443/562949953421312000000000000000000), (48455129762269170646946110675409/562949953421312000000000000000000), (5812147902638519730384811413039/1125899906842624000000000000000000), (76923283048026087663066220829/140737488355328000000000000000000), (-446477704449877114271051553197/1125899906842624000000000000000000), (-109539833912786720235816604793/1125899906842624000000000000000000), (-1056850680660700524949001273/1125899906842624000000000000000000), (215517498534366441815441859/140737488355328000000000000000000), (24386504235731017684436129/281474976710656000000000000000000), (-13159829476575854844210339/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial139.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial139.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial139.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 1750465189157279170411058454376718), (Int.ofNat 105127118943280704979101130277473), (Int.negOfNat 8965957865056950117264414735005), (Int.negOfNat 6451673833149477583764699919847), (Int.negOfNat 1078200360644436344194614523868), (Int.ofNat 33066291611905868932484336573), (Int.ofNat 22614484342269329897714186134), (Int.ofNat 772421438385702660199150164), (Int.negOfNat 218845319429225237603777049), (Int.negOfNat 13548182778183754526730299), (Int.ofNat 1283663031678442437077756), (Int.ofNat 107612471800045506237570), (Int.negOfNat 5057651764357442175672), (Int.negOfNat 546983593627686859860), (Int.ofNat 14040544498704644796), (Int.ofNat 2038990679148590902), (Int.negOfNat 27244032914544127), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(875232594578639585205529227188359/562949953421312000000000000000000), (105127118943280704979101130277473/1125899906842624000000000000000000), (-1793191573011390023452882947001/225179981368524800000000000000000), (-6451673833149477583764699919847/1125899906842624000000000000000000), (-269550090161109086048653630967/281474976710656000000000000000000), (33066291611905868932484336573/1125899906842624000000000000000000), (11307242171134664948857093067/562949953421312000000000000000000), (193105359596425665049787541/281474976710656000000000000000000), (-218845319429225237603777049/1125899906842624000000000000000000), (-13548182778183754526730299/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial139.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial139.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial139.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 1858533866307129995443681794110862), (Int.negOfNat 35573560391642303099474257173106), (Int.negOfNat 65398167743255965087214940015673), (Int.negOfNat 10145210677413545636946239734104), (Int.ofNat 546853075476133133418003656488), (Int.ofNat 256828208998782155612309272975), (Int.ofNat 5313691555487373869509963108), (Int.negOfNat 3058596551953855377538069499), (Int.negOfNat 148002263109590236232340323), (Int.ofNat 22106890959151659352045531), (Int.ofNat 1454124171699936309810408), (Int.negOfNat 107835721194315236963351), (Int.negOfNat 8691750913950752571735), (Int.ofNat 378376600197313195209), (Int.ofNat 36323784629643791663), (Int.negOfNat 973383439331700635), (Int.negOfNat 126330757878657861), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(929266933153564997721840897055431/562949953421312000000000000000000), (-17786780195821151549737128586553/562949953421312000000000000000000), (-65398167743255965087214940015673/1125899906842624000000000000000000), (-1268151334676693204618279966763/140737488355328000000000000000000), (68356634434516641677250457061/140737488355328000000000000000000), (10273128359951286224492370919/45035996273704960000000000000000), (1328422888871843467377490777/281474976710656000000000000000000), (-3058596551953855377538069499/1125899906842624000000000000000000), (-148002263109590236232340323/1125899906842624000000000000000000), (22106890959151659352045531/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial139.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial139.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial139.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 1461523783306086868716876134786730), (Int.negOfNat 381307806017365234443503589300225), (Int.negOfNat 93528943339117804118217157481041), (Int.ofNat 3510682329941302753959279121851), (Int.ofNat 2514981275945710818508195499237), (Int.ofNat 49747200434437127585636767175), (Int.negOfNat 36341843167644248981393060355), (Int.negOfNat 1581675700770552249155412667), (Int.ofNat 321887867180665484191335674), (Int.ofNat 18356930105550555754642010), (Int.negOfNat 1911575627416052862796300), (Int.negOfNat 127647980242305126752064), (Int.ofNat 8122053967660226208663), (Int.ofNat 610060930482061555901), (Int.negOfNat 25875790411003639724), (Int.negOfNat 2194998718122313061), (Int.ofNat 61697927319208258), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(146152378330608686871687613478673/112589990684262400000000000000000), (-15252312240694609377740143572009/45035996273704960000000000000000), (-93528943339117804118217157481041/1125899906842624000000000000000000), (3510682329941302753959279121851/1125899906842624000000000000000000), (2514981275945710818508195499237/1125899906842624000000000000000000), (1989888017377485103425470687/45035996273704960000000000000000), (-7268368633528849796278612071/225179981368524800000000000000000), (-1581675700770552249155412667/1125899906842624000000000000000000), (160943933590332742095667837/562949953421312000000000000000000), (1835693010555055575464201/112589990684262400000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial139.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial139.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial139.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 392270755872626179114332890691070), (Int.negOfNat 636161528068111555335814718762820), (Int.negOfNat 17274020233231575224889128571007), (Int.ofNat 19561814098187937012265943001886), (Int.ofNat 793740210042571646381676578903), (Int.negOfNat 356199649343695681746996527881), (Int.negOfNat 17818502388287705866078249194), (Int.ofNat 3961238017004341716100506302), (Int.ofNat 222711035838844652522870870), (Int.negOfNat 28906025859683012803704203), (Int.negOfNat 1756027695047681123713527), (Int.ofNat 148047763871920524954825), (Int.ofNat 9526842693119923289785), (Int.negOfNat 561761189230243327009), (Int.negOfNat 37831008856133458809), (Int.ofNat 1610899853738323281), (Int.ofNat 132783351521891694), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(39227075587262617911433289069107/112589990684262400000000000000000), (-31808076403405577766790735938141/56294995342131200000000000000000), (-17274020233231575224889128571007/1125899906842624000000000000000000), (9780907049093968506132971500943/562949953421312000000000000000000), (793740210042571646381676578903/1125899906842624000000000000000000), (-356199649343695681746996527881/1125899906842624000000000000000000), (-8909251194143852933039124597/562949953421312000000000000000000), (1980619008502170858050253151/562949953421312000000000000000000), (22271103583884465252287087/112589990684262400000000000000000), (-28906025859683012803704203/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial139.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial139.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial139.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 791945006484822793429432837959462), (Int.negOfNat 475104309166792164574476271707652), (Int.ofNat 89286549272135033829039585704304), (Int.ofNat 11254946984110400016776183978615), (Int.negOfNat 2611711797034014717299144967140), (Int.negOfNat 204812906581946069677903938915), (Int.ofNat 39862056036077915112356808169), (Int.ofNat 2624480741732558819053017166), (Int.negOfNat 371536853843709505926641911), (Int.negOfNat 22873138557712829336899760), (Int.ofNat 2329822308661513240672385), (Int.ofNat 139302031478014341424007), (Int.negOfNat 10535184544201227654977), (Int.negOfNat 619458087509065782874), (Int.ofNat 36081080230326379352), (Int.ofNat 2086415713899152941), (Int.negOfNat 98302686271617000), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-395972503242411396714716418979731/562949953421312000000000000000000), (-118776077291698041143619067926913/281474976710656000000000000000000), (5580409329508439614314974106519/70368744177664000000000000000000), (2250989396822080003355236795723/225179981368524800000000000000000), (-130585589851700735864957248357/56294995342131200000000000000000), (-40962581316389213935580787783/225179981368524800000000000000000), (39862056036077915112356808169/1125899906842624000000000000000000), (1312240370866279409526508583/562949953421312000000000000000000), (-371536853843709505926641911/1125899906842624000000000000000000), (-285914231971410366711247/14073748835532800000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial139.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial139.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial139.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial139.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial139.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial139.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial139.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial139.reflect := by
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

end Bin139
end
end ErdosOverlap.OuterNumerics
