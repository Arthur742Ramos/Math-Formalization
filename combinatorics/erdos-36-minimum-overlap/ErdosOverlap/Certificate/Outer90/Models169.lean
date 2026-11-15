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

/-! # Exact integer weighted outer models for source bin 169

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin169

def weightDenominator : ℤ := (Int.ofNat 5000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 217271223170825250)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 869464713536947000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 592523410610060750)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 243564498540596550)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 428827590570617150)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 349387749507547800)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 246346906104623375)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 172933277899832670)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 92650084694874870)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 53113884878548530)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial169.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial169.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 4456035447219748500)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1720301399757659650)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 567553729085288950)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 456266705708275300)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 228184739557338380)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 85051202804167330)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 1458494969722667)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 19226622915851560)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 18984624868343693)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial169.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial169.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4456035447219748500)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1720301399757659650)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 567553729085288950)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 456266705708275300)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 228184739557338380)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 85051202804167330)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 1458494969722667)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 19226622915851560)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 18984624868343693)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial169.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial169.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial169.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 2004942315885116205932265347784030), (Int.ofNat 1905649948969391227093874914539237), (Int.ofNat 195335795001817525197598766967192), (Int.negOfNat 44682552698617355063102573930618), (Int.negOfNat 6064352113213713148880353571832), (Int.ofNat 755600082276856310596203327231), (Int.ofNat 103551913373962339213085454461), (Int.negOfNat 8544020278804898417528971862), (Int.negOfNat 1095252982360265304366786710), (Int.ofNat 67201599833113509083982789), (Int.ofNat 7828703343601503478742068), (Int.negOfNat 383932950966400304788394), (Int.negOfNat 40243246988886725222946), (Int.ofNat 1650648408879949775382), (Int.ofNat 155887404571602698511), (Int.negOfNat 5427875867884426181), (Int.negOfNat 491353881213531238), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-200494231588511620593226534778403/562949953421312000000000000000000), (1905649948969391227093874914539237/5629499534213120000000000000000000), (24416974375227190649699845870899/703687441776640000000000000000000), (-22341276349308677531551286965309/2814749767106560000000000000000000), (-758044014151714143610044196479/703687441776640000000000000000000), (755600082276856310596203327231/5629499534213120000000000000000000), (103551913373962339213085454461/5629499534213120000000000000000000), (-4272010139402449208764485931/2814749767106560000000000000000000), (-109525298236026530436678671/562949953421312000000000000000000), (67201599833113509083982789/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial169.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial169.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial169.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial169 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 2162684700933244428832793163832802), (Int.ofNat 2032313648754745601662069313284000), (Int.negOfNat 140321144679086374779583970525367), (Int.negOfNat 52691043261585784755241342847263), (Int.ofNat 4441357475179824201738218463970), (Int.ofNat 973712015589883204583289231064), (Int.negOfNat 74859926927081333947807264308), (Int.negOfNat 11684357570786343635991100582), (Int.ofNat 790073156155028266103235547), (Int.ofNat 95004539345022121338222010), (Int.negOfNat 5694224047529804827210879), (Int.negOfNat 551817653311735955448081), (Int.ofNat 29618546346508316030861), (Int.ofNat 2390008285569623043333), (Int.negOfNat 116099710422488812512), (Int.negOfNat 7915630757122300414), (Int.ofNat 369282156455488248), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(1081342350466622214416396581916401/2814749767106560000000000000000000), (508078412188686400415517328321/1407374883553280000000000000000), (-140321144679086374779583970525367/5629499534213120000000000000000000), (-52691043261585784755241342847263/5629499534213120000000000000000000), (444135747517982420173821846397/562949953421312000000000000000000), (121714001948735400572911153883/703687441776640000000000000000000), (-18714981731770333486951816077/1407374883553280000000000000000000), (-5842178785393171817995550291/2814749767106560000000000000000000), (790073156155028266103235547/5629499534213120000000000000000000), (9500453934502212133822201/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial169.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial169.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial169.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial169 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 5340677023449224741206669463764230), (Int.ofNat 1040142648584652684163272292043418), (Int.negOfNat 296021344722680838814461504067549), (Int.ofNat 5087188823703806048170100710029), (Int.ofNat 7587853110247513064783494148143), (Int.negOfNat 419195208254238902234992378683), (Int.negOfNat 111230037926480846641205172144), (Int.ofNat 7208922920637365749283502758), (Int.ofNat 1052341076880523635355950077), (Int.negOfNat 70166962102706190287657616), (Int.negOfNat 6947752551604059944980423), (Int.ofNat 454695589172365149959134), (Int.ofNat 33714162171812666236422), (Int.negOfNat 2117878735994579630617), (Int.negOfNat 124788400988462736445), (Int.ofNat 7454623960922393972), (Int.ofNat 350996851446229341), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(534067702344922474120666946376423/562949953421312000000000000000000), (520071324292326342081636146021709/2814749767106560000000000000000000), (-296021344722680838814461504067549/5629499534213120000000000000000000), (5087188823703806048170100710029/5629499534213120000000000000000000), (7587853110247513064783494148143/5629499534213120000000000000000000), (-419195208254238902234992378683/5629499534213120000000000000000000), (-6951877370405052915075323259/351843720888320000000000000000000), (3604461460318682874641751379/2814749767106560000000000000000000), (1052341076880523635355950077/5629499534213120000000000000000000), (-4385435131419136892978601/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial169.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial169.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial169.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial169 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 6379597284631635016680868428866227), (Int.ofNat 109138833849700994040837277834843), (Int.negOfNat 137279034102641801880002955693960), (Int.ofNat 36686562019010664314900746186859), (Int.negOfNat 434473589471094786491564344806), (Int.negOfNat 858378704136073835948052538831), (Int.ofNat 45236585166004048297309181217), (Int.ofNat 10254185068676589393149712767), (Int.negOfNat 698239527140836394758183589), (Int.negOfNat 79211656833480919844340643), (Int.ofNat 5953231205535238582554199), (Int.ofNat 434051408942231564157392), (Int.negOfNat 33854711280206162216571), (Int.negOfNat 1781086938867879018384), (Int.ofNat 139556860453081039039), (Int.ofNat 5543247391250306642), (Int.negOfNat 426236031060519327), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(6379597284631635016680868428866227/5629499534213120000000000000000000), (109138833849700994040837277834843/5629499534213120000000000000000000), (-3431975852566045047000073892349/140737488355328000000000000000000), (36686562019010664314900746186859/5629499534213120000000000000000000), (-217236794735547393245782172403/2814749767106560000000000000000000), (-858378704136073835948052538831/5629499534213120000000000000000000), (45236585166004048297309181217/5629499534213120000000000000000000), (10254185068676589393149712767/5629499534213120000000000000000000), (-698239527140836394758183589/5629499534213120000000000000000000), (-79211656833480919844340643/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial169.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial169.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial169.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial169 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 6311826821792333797482597725233625), (Int.negOfNat 69895751173997151814686341744552), (Int.ofNat 19952303395906270743685432505068), (Int.ofNat 10284288844956284530235634482027), (Int.negOfNat 4440744129097586861121154726877), (Int.ofNat 130288302242444625665658917199), (Int.ofNat 81506793813963825898193720222), (Int.negOfNat 5302929670594203551830855961), (Int.negOfNat 791059536423550311806918832), (Int.ofNat 65445033290679182398768994), (Int.ofNat 5023630511175991459162337), (Int.negOfNat 471590991159466185753601), (Int.negOfNat 22910971450376949843892), (Int.ofNat 2323165387260377748036), (Int.ofNat 79302587785512926487), (Int.negOfNat 8534460600569175988), (Int.negOfNat 191655196810583751), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(50494614574338670379860781801869/45035996273704960000000000000000), (-8736968896749643976835792718069/703687441776640000000000000000000), (4988075848976567685921358126267/1407374883553280000000000000000000), (10284288844956284530235634482027/5629499534213120000000000000000000), (-4440744129097586861121154726877/5629499534213120000000000000000000), (130288302242444625665658917199/5629499534213120000000000000000000), (40753396906981912949096860111/2814749767106560000000000000000000), (-5302929670594203551830855961/5629499534213120000000000000000000), (-49441221026471894487932427/351843720888320000000000000000000), (32722516645339591199384497/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial169.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial169.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial169.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial169 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 6271608924395529336687160198092309), (Int.ofNat 14278489479053818814894450655104), (Int.ofNat 428732263465430753957556879666), (Int.negOfNat 10969046553329789066368742883259), (Int.negOfNat 308784715534904455696225777956), (Int.ofNat 465529660691262042810992933973), (Int.negOfNat 28252799224985747641116721570), (Int.negOfNat 6508456572785980179643400686), (Int.ofNat 590816878196712367088838243), (Int.ofNat 50637256059872589975245712), (Int.negOfNat 5674197111636558128997463), (Int.negOfNat 260562453042461313706511), (Int.ofNat 34245891578979090593346), (Int.ofNat 967742527363704739382), (Int.negOfNat 146047777324580353514), (Int.negOfNat 2684943758254341950), (Int.ofNat 483189905665550406), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(6271608924395529336687160198092309/5629499534213120000000000000000000), (111550699055107959491362895743/43980465111040000000000000000000), (214366131732715376978778439833/2814749767106560000000000000000000), (-10969046553329789066368742883259/5629499534213120000000000000000000), (-77196178883726113924056444489/1407374883553280000000000000000000), (465529660691262042810992933973/5629499534213120000000000000000000), (-2825279922498574764111672157/562949953421312000000000000000000), (-3254228286392990089821700343/2814749767106560000000000000000000), (590816878196712367088838243/5629499534213120000000000000000000), (3164828503742036873452857/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial169.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial169.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial169.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial169 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 6221614569219649419648441310798107), (Int.negOfNat 95923650284582947424870380612243), (Int.negOfNat 45486572607564055769513259295867), (Int.negOfNat 1746484313721844513517836939788), (Int.ofNat 1612133287914396433695052829105), (Int.negOfNat 103267826442565978768957359216), (Int.negOfNat 39966489536349751372801502199), (Int.ofNat 4321759827711508066096324790), (Int.ofNat 419336626312729398050513140), (Int.negOfNat 58358408629326399539323178), (Int.negOfNat 2509898350737651554264816), (Int.ofNat 443987205171330027633197), (Int.ofNat 9765971187663515006750), (Int.negOfNat 2258045241491277208181), (Int.negOfNat 25914941985658207975), (Int.ofNat 8514050292908300018), (Int.ofNat 32313542174938161), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(6221614569219649419648441310798107/5629499534213120000000000000000000), (-95923650284582947424870380612243/5629499534213120000000000000000000), (-45486572607564055769513259295867/5629499534213120000000000000000000), (-436621078430461128379459234947/1407374883553280000000000000000000), (322426657582879286739010565821/1125899906842624000000000000000000), (-6454239152660373673059834951/351843720888320000000000000000000), (-39966489536349751372801502199/5629499534213120000000000000000000), (432175982771150806609632479/562949953421312000000000000000000), (20966831315636469902525657/281474976710656000000000000000000), (-29179204314663199769661589/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial169.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial169.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial169.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial169 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 5854409826970909288759822991531281), (Int.negOfNat 260951118802324102724483090509900), (Int.negOfNat 31757019440107712534934260295350), (Int.ofNat 3463769406533215763312839194363), (Int.negOfNat 388657177177837588243554815321), (Int.negOfNat 156492695808824974923473909315), (Int.ofNat 26500391991049612112562391721), (Int.ofNat 2563945454467705657020692086), (Int.negOfNat 510739303969337568883187414), (Int.negOfNat 18590515537670650948545353), (Int.ofNat 5022269445727117518506363), (Int.ofNat 69074339324983881804459), (Int.negOfNat 31060025025558383610327), (Int.negOfNat 94284061522047314603), (Int.ofNat 134192226189872294195), (Int.negOfNat 407302340737038092), (Int.negOfNat 487029895392032955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(5854409826970909288759822991531281/5629499534213120000000000000000000), (-2609511188023241027244830905099/56294995342131200000000000000000), (-635140388802154250698685205907/112589990684262400000000000000000), (3463769406533215763312839194363/5629499534213120000000000000000000), (-388657177177837588243554815321/5629499534213120000000000000000000), (-31298539161764994984694781863/1125899906842624000000000000000000), (26500391991049612112562391721/5629499534213120000000000000000000), (1281972727233852828510346043/2814749767106560000000000000000000), (-255369651984668784441593707/2814749767106560000000000000000000), (-18590515537670650948545353/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial169.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial169.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial169.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial169 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 5223852486696158310891615871662413), (Int.negOfNat 365673776945150398001429239390490), (Int.negOfNat 25681698954456265854859906855777), (Int.negOfNat 1167879866699316090569716687960), (Int.negOfNat 226060524991984620402803017376), (Int.ofNat 150088973879314473624819697332), (Int.ofNat 8837646157896579164312040381), (Int.negOfNat 3840277110737947108286899066), (Int.negOfNat 75850884346041825168509154), (Int.ofNat 49216420640975535595771283), (Int.ofNat 41619149978602728685983), (Int.negOfNat 376497092187076199299929), (Int.ofNat 3172616126369599661193), (Int.ofNat 1935503882742079750443), (Int.negOfNat 25826609701757101245), (Int.negOfNat 7315073043709631408), (Int.ofNat 111883477318846285), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(5223852486696158310891615871662413/5629499534213120000000000000000000), (-36567377694515039800142923939049/562949953421312000000000000000000), (-25681698954456265854859906855777/5629499534213120000000000000000000), (-29196996667482902264242917199/140737488355328000000000000000000), (-7064391405999519387587594293/175921860444160000000000000000000), (37522243469828618406204924333/1407374883553280000000000000000000), (8837646157896579164312040381/5629499534213120000000000000000000), (-1920138555368973554143449533/2814749767106560000000000000000000), (-37925442173020912584254577/2814749767106560000000000000000000), (49216420640975535595771283/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial169.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial169.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial169.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial169 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 4381700111441365793056738912863357), (Int.negOfNat 477633694171587067858775484145593), (Int.negOfNat 26485694026360873631207965435385), (Int.ofNat 2404954254947802406251263067039), (Int.ofNat 829019559848553673924088771269), (Int.negOfNat 11087673026952764428266854824), (Int.negOfNat 25198390244392133240952481379), (Int.ofNat 356206853149272650376431560), (Int.ofNat 415142623696236121479820370), (Int.negOfNat 8725058708831720123402882), (Int.negOfNat 3975513537106521914967096), (Int.ofNat 101244642084912651984863), (Int.ofNat 24601000948357855525810), (Int.negOfNat 685668986719181733079), (Int.negOfNat 106881478942635175255), (Int.ofNat 3165935819079334862), (Int.ofNat 418771375371623281), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(4381700111441365793056738912863357/5629499534213120000000000000000000), (-477633694171587067858775484145593/5629499534213120000000000000000000), (-5297138805272174726241593087077/1125899906842624000000000000000000), (2404954254947802406251263067039/5629499534213120000000000000000000), (829019559848553673924088771269/5629499534213120000000000000000000), (-1385959128369095553533356853/703687441776640000000000000000000), (-25198390244392133240952481379/5629499534213120000000000000000000), (8905171328731816259410789/140737488355328000000000000000000), (41514262369623612147982037/562949953421312000000000000000000), (-4362529354415860061701441/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial169.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial169.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial169.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial169 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 3351170025178908087616086697909313), (Int.negOfNat 533367571350153018111654162681502), (Int.ofNat 1807544621707887659336677815996), (Int.ofNat 5404077308856498501950681805807), (Int.negOfNat 310628899178557923451189217142), (Int.negOfNat 142047036825817540571004400666), (Int.ofNat 9792735596789524111722707260), (Int.ofNat 2968227238449188102930262226), (Int.negOfNat 174285252192368854701399657), (Int.negOfNat 35943620367351567237802572), (Int.ofNat 1906171060584562151280157), (Int.ofNat 271388774637445747128101), (Int.negOfNat 13620361446462230393134), (Int.negOfNat 1392338210438962960762), (Int.ofNat 67562267082072117906), (Int.ofNat 5174975178074881350), (Int.negOfNat 221951236802425894), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(3351170025178908087616086697909313/5629499534213120000000000000000000), (-266683785675076509055827081340751/2814749767106560000000000000000000), (451886155426971914834169453999/1407374883553280000000000000000000), (5404077308856498501950681805807/5629499534213120000000000000000000), (-155314449589278961725594608571/2814749767106560000000000000000000), (-71023518412908770285502200333/2814749767106560000000000000000000), (489636779839476205586135363/281474976710656000000000000000000), (1484113619224594051465131113/2814749767106560000000000000000000), (-174285252192368854701399657/5629499534213120000000000000000000), (-8985905091837891809450643/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial169.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial169.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial169.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial169 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 2326328201661860861183571881400622), (Int.negOfNat 479631247535828232220323661623805), (Int.ofNat 19308597311947665217562519207639), (Int.negOfNat 483588403483480564232747364), (Int.negOfNat 617627480364370971180316664064), (Int.ofNat 95893498230770405463130894128), (Int.ofNat 17042276339636138137313009132), (Int.negOfNat 2195006126863622822828549679), (Int.negOfNat 268874858985380194207095772), (Int.ofNat 27533556484093114054832626), (Int.ofNat 2520186739656860342425937), (Int.negOfNat 222852235385981183682929), (Int.negOfNat 15456944847714058708052), (Int.ofNat 1246135358364651031284), (Int.ofNat 66813325925438780327), (Int.negOfNat 5084808613574580132), (Int.negOfNat 259429720735977691), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(1163164100830930430591785940700311/2814749767106560000000000000000000), (-95926249507165646444064732324761/1125899906842624000000000000000000), (19308597311947665217562519207639/5629499534213120000000000000000000), (-120897100870870141058186841/1407374883553280000000000000000000), (-2412607345173324106173111969/21990232555520000000000000000000), (5993343639423150341445680883/351843720888320000000000000000000), (4260569084909034534328252283/1407374883553280000000000000000000), (-2195006126863622822828549679/5629499534213120000000000000000000), (-67218714746345048551773943/1407374883553280000000000000000000), (13766778242046557027416313/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial169.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial169.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial169.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial169 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 1438239861595991857238637368729357), (Int.negOfNat 412408311100773582180333869973854), (Int.ofNat 14436200940011034651538808880514), (Int.ofNat 85954325210472487750613194789), (Int.ofNat 582126569657406880686211174047), (Int.ofNat 63700675922027823882685502361), (Int.negOfNat 20729265517327815924058412840), (Int.negOfNat 1524204145974392307738234097), (Int.ofNat 323289963115810949861197601), (Int.ofNat 18415836348906831408859843), (Int.negOfNat 3095032086812095930066771), (Int.negOfNat 137271991849265870777472), (Int.ofNat 20031930699870693945829), (Int.ofNat 695330265896696935784), (Int.negOfNat 92785133458056418481), (Int.negOfNat 2509434783701798922), (Int.ofNat 278905111407456973), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(1438239861595991857238637368729357/5629499534213120000000000000000000), (-206204155550386791090166934986927/2814749767106560000000000000000000), (7218100470005517325769404440257/2814749767106560000000000000000000), (85954325210472487750613194789/5629499534213120000000000000000000), (582126569657406880686211174047/5629499534213120000000000000000000), (63700675922027823882685502361/5629499534213120000000000000000000), (-518231637933195398101460321/140737488355328000000000000000000), (-1524204145974392307738234097/5629499534213120000000000000000000), (323289963115810949861197601/5629499534213120000000000000000000), (18415836348906831408859843/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial169.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial169.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial169.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial169 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 681775180226273569160527175493659), (Int.negOfNat 334214209170687655056852995394694), (Int.ofNat 28645833822024120049775288067550), (Int.ofNat 3748145617032837496381930549471), (Int.negOfNat 59764975656349385795722118971), (Int.negOfNat 157980965420560219419714263489), (Int.negOfNat 4650873390985529712455375084), (Int.ofNat 3145273384176374116955473562), (Int.ofNat 84906516143119680331920107), (Int.negOfNat 36749997887540748966990444), (Int.negOfNat 795971676980648616563883), (Int.ofNat 281232601274932563897166), (Int.ofNat 4738520638973222201402), (Int.negOfNat 1507984660088013336903), (Int.negOfNat 19617352493484502045), (Int.ofNat 5979372960235542188), (Int.ofNat 100088066100332101), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(681775180226273569160527175493659/5629499534213120000000000000000000), (-167107104585343827528426497697347/2814749767106560000000000000000000), (572916676440482400995505761351/112589990684262400000000000000000), (3748145617032837496381930549471/5629499534213120000000000000000000), (-59764975656349385795722118971/5629499534213120000000000000000000), (-157980965420560219419714263489/5629499534213120000000000000000000), (-1162718347746382428113843771/1407374883553280000000000000000000), (1572636692088187058477736781/2814749767106560000000000000000000), (84906516143119680331920107/5629499534213120000000000000000000), (-9187499471885187241747611/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial169.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial169.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial169.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial169 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 152011258588496673547390656204915), (Int.negOfNat 188686568071648819313912035596895), (Int.ofNat 38040920554676402838358447548033), (Int.negOfNat 2077673203392642282475088429788), (Int.negOfNat 1089804756528264372837943108537), (Int.ofNat 16240199397971375705718593023), (Int.ofNat 25628952615963764608695046802), (Int.negOfNat 111788007180538598987628148), (Int.negOfNat 372110359750302067746406063), (Int.ofNat 916815857338688813216690), (Int.ofNat 3436178724585905549395341), (Int.negOfNat 8249556522635788248279), (Int.negOfNat 21650338250297445250539), (Int.ofNat 60334001233370217447), (Int.ofNat 98244832921175570228), (Int.negOfNat 429570338281060306), (Int.negOfNat 335858986012488052), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(30402251717699334709478131240983/1125899906842624000000000000000000), (-37737313614329763862782407119379/1125899906842624000000000000000000), (38040920554676402838358447548033/5629499534213120000000000000000000), (-519418300848160570618772107447/1407374883553280000000000000000000), (-1089804756528264372837943108537/5629499534213120000000000000000000), (16240199397971375705718593023/5629499534213120000000000000000000), (12814476307981882304347523401/2814749767106560000000000000000000), (-27947001795134649746907037/1407374883553280000000000000000000), (-372110359750302067746406063/5629499534213120000000000000000000), (91681585733868881321669/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial169.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial169.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial169.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial169 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 105202202279537572032269702742824), (Int.negOfNat 90520768855259103845992479966080), (Int.ofNat 6169947803792348739939005874922), (Int.negOfNat 6720283602826556454234672592676), (Int.ofNat 209176662203229015561916894352), (Int.ofNat 174927781135834325534800721823), (Int.negOfNat 6767603896503116086463158089), (Int.negOfNat 3179610633552872136335606478), (Int.ofNat 100629744376161000938334170), (Int.ofNat 36150772538176383591939131), (Int.negOfNat 937216942752054068882142), (Int.negOfNat 272070519590374157992936), (Int.ofNat 6001455789689632142494), (Int.ofNat 1442364751954795819638), (Int.negOfNat 27854339022666166209), (Int.negOfNat 5696293365145748819), (Int.ofNat 78238213403657182), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-13150275284942196504033712842853/703687441776640000000000000000000), (-141438701336342349759363249947/8796093022208000000000000000000), (3084973901896174369969502937461/2814749767106560000000000000000000), (-1680070900706639113558668148169/1407374883553280000000000000000000), (13073541387701813472619805897/351843720888320000000000000000000), (174927781135834325534800721823/5629499534213120000000000000000000), (-6767603896503116086463158089/5629499534213120000000000000000000), (-1589805316776436068167803239/2814749767106560000000000000000000), (10062974437616100093833417/562949953421312000000000000000000), (36150772538176383591939131/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial169.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial169.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial169.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial169 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 307179029555809286365957743357189), (Int.negOfNat 128341657862619249089270625654941), (Int.negOfNat 18569140731494851794467304250509), (Int.negOfNat 563302869749269083970373609690), (Int.ofNat 897729095376260604457030282529), (Int.negOfNat 69972144071529560453451501141), (Int.negOfNat 22252712493625886176706409431), (Int.ofNat 1589716516526971993845579772), (Int.ofNat 320935830925793852454722630), (Int.negOfNat 18746477960111060213631049), (Int.negOfNat 2940665322235648524881668), (Int.ofNat 142663999820495581399204), (Int.ofNat 18448652467169172388296), (Int.negOfNat 760265358818575035392), (Int.negOfNat 83755398789920923301), (Int.ofNat 3078325090955680261), (Int.ofNat 267600465992078378), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-307179029555809286365957743357189/5629499534213120000000000000000000), (-128341657862619249089270625654941/5629499534213120000000000000000000), (-18569140731494851794467304250509/5629499534213120000000000000000000), (-56330286974926908397037360969/562949953421312000000000000000000), (897729095376260604457030282529/5629499534213120000000000000000000), (-69972144071529560453451501141/5629499534213120000000000000000000), (-22252712493625886176706409431/5629499534213120000000000000000000), (397429129131742998461394943/1407374883553280000000000000000000), (32093583092579385245472263/562949953421312000000000000000000), (-18746477960111060213631049/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial169.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial169.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial169.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial169 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 631671553743951490160742012702144), (Int.negOfNat 189536222156043375274264698566472), (Int.negOfNat 9813621244928387522639876221023), (Int.ofNat 1586444559578256932388321103617), (Int.negOfNat 439684620746321814094114959455), (Int.negOfNat 115431980800559190885763703284), (Int.ofNat 16448357281390162507989969058), (Int.ofNat 2309091595503834396659944762), (Int.negOfNat 255527276465032044620446247), (Int.negOfNat 26460049014251359541217090), (Int.ofNat 2392542916972722579001499), (Int.ofNat 200070379563229492672251), (Int.negOfNat 15078006003552222424201), (Int.negOfNat 1067800150163221726773), (Int.ofNat 68230957250209189532), (Int.ofNat 4335576113579054654), (Int.negOfNat 222435232897441628), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-9869868027249242033761593948471/87960930222080000000000000000000), (-23692027769505421909283087320809/703687441776640000000000000000000), (-9813621244928387522639876221023/5629499534213120000000000000000000), (1586444559578256932388321103617/5629499534213120000000000000000000), (-87936924149264362818822991891/1125899906842624000000000000000000), (-28857995200139797721440925821/1407374883553280000000000000000000), (8224178640695081253994984529/2814749767106560000000000000000000), (1154545797751917198329972381/2814749767106560000000000000000000), (-255527276465032044620446247/5629499534213120000000000000000000), (-2646004901425135954121709/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial169.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial169.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial169.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial169 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 1046763617369813286388468821018584), (Int.negOfNat 229173820253847862133911220652444), (Int.negOfNat 15130425658008997902030344929131), (Int.negOfNat 3180390338844186665244832977319), (Int.negOfNat 315049776025464093175994311558), (Int.ofNat 131501734351823760675870794163), (Int.ofNat 12307148514432535026161214434), (Int.negOfNat 2700417505352051450666599108), (Int.negOfNat 184751995402633133900540527), (Int.ofNat 31974545543234840504877336), (Int.ofNat 1725750934618633293481233), (Int.negOfNat 243780121265665662635824), (Int.negOfNat 11071459998366314381132), (Int.ofNat 1293157549471422937957), (Int.ofNat 51143086960921706525), (Int.negOfNat 5105073183993648052), (Int.negOfNat 127243436224776481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-130845452171226660798558602627323/703687441776640000000000000000000), (-57293455063461965533477805163111/1407374883553280000000000000000000), (-15130425658008997902030344929131/5629499534213120000000000000000000), (-3180390338844186665244832977319/5629499534213120000000000000000000), (-157524888012732046587997155779/2814749767106560000000000000000000), (131501734351823760675870794163/5629499534213120000000000000000000), (6153574257216267513080607217/2814749767106560000000000000000000), (-675104376338012862666649777/1407374883553280000000000000000000), (-184751995402633133900540527/5629499534213120000000000000000000), (3996818192904355063109667/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial169.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial169.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial169.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial169 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 1591496511797283903882826928458167), (Int.negOfNat 326378101002246809477467687179007), (Int.negOfNat 30286036686888924758431430052159), (Int.negOfNat 127619447236061447196095569094), (Int.ofNat 916283545284126792254196452651), (Int.ofNat 40092288678937530105552307508), (Int.negOfNat 22854681093910568647249452567), (Int.negOfNat 807574336254233250409899127), (Int.ofNat 350546939884817914592050179), (Int.ofNat 9683715398262658375384983), (Int.negOfNat 3313613955728086157008909), (Int.negOfNat 78395298718419926945002), (Int.ofNat 20987271865222119722781), (Int.ofNat 448482423781293530034), (Int.negOfNat 94814372559665231219), (Int.negOfNat 1963192747707060882), (Int.ofNat 279389107502472707), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-1591496511797283903882826928458167/5629499534213120000000000000000000), (-326378101002246809477467687179007/5629499534213120000000000000000000), (-30286036686888924758431430052159/5629499534213120000000000000000000), (-63809723618030723598047784547/2814749767106560000000000000000000), (916283545284126792254196452651/5629499534213120000000000000000000), (10023072169734382526388076877/1407374883553280000000000000000000), (-22854681093910568647249452567/5629499534213120000000000000000000), (-807574336254233250409899127/5629499534213120000000000000000000), (350546939884817914592050179/5629499534213120000000000000000000), (9683715398262658375384983/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial169.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial169.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial169.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial169 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 2351949162842526455226639931592556), (Int.negOfNat 420911165558997250009496136859726), (Int.negOfNat 11247502680803482445890887268434), (Int.ofNat 5325803685727711652072060079193), (Int.ofNat 106339244923797884682469372260), (Int.negOfNat 152296493558193688934443700626), (Int.ofNat 579755064045221762010992118), (Int.ofNat 3138912936094915767433545191), (Int.negOfNat 9099739077458597402153048), (Int.negOfNat 37969327652261874722701044), (Int.negOfNat 3944085131488676619457), (Int.ofNat 293621779249343567680811), (Int.ofNat 734066834801034489842), (Int.negOfNat 1570567732663455173066), (Int.negOfNat 6777536978767210267), (Int.ofNat 6184909823640430068), (Int.negOfNat 32098218410869109), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-587987290710631613806659982898139/1407374883553280000000000000000000), (-210455582779498625004748068429863/2814749767106560000000000000000000), (-5623751340401741222945443634217/2814749767106560000000000000000000), (5325803685727711652072060079193/5629499534213120000000000000000000), (5316962246189894234123468613/281474976710656000000000000000000), (-76148246779096844467221850313/2814749767106560000000000000000000), (289877532022610881005496059/2814749767106560000000000000000000), (3138912936094915767433545191/5629499534213120000000000000000000), (-1137467384682324675269131/703687441776640000000000000000000), (-9492331913065468680675261/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial169.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial169.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial169.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial169 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 3198909432188923413580868004993132), (Int.negOfNat 409348426871306178465836154049588), (Int.ofNat 13140987626488258642034578856760), (Int.ofNat 1726751316835390490761392626631), (Int.negOfNat 654350872565387713050107815488), (Int.ofNat 45925312476531277780627023552), (Int.ofNat 22026533746711903459250580580), (Int.negOfNat 1074564766929697985428214334), (Int.negOfNat 360872590698072200248795363), (Int.ofNat 11353663428931466230192978), (Int.ofNat 3512827739838287042010113), (Int.negOfNat 73332525983344316848299), (Int.negOfNat 22662196759098626982716), (Int.ofNat 317899325520481038958), (Int.ofNat 104126576708043205994), (Int.negOfNat 895110885288903810), (Int.negOfNat 336342982107503786), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-799727358047230853395217001248283/1407374883553280000000000000000000), (-102337106717826544616459038512397/1407374883553280000000000000000000), (328524690662206466050864471419/140737488355328000000000000000000), (1726751316835390490761392626631/5629499534213120000000000000000000), (-10224232383834183016407934617/87960930222080000000000000000000), (717583007445801215322297243/87960930222080000000000000000000), (1101326687335595172962529029/281474976710656000000000000000000), (-537282383464848992714107167/2814749767106560000000000000000000), (-360872590698072200248795363/5629499534213120000000000000000000), (5676831714465733115096489/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial169.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial169.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial169.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial169 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 3959039386913900091950227482141492), (Int.negOfNat 349907717587338704504544562248349), (Int.ofNat 15477953256543462116493384999936), (Int.ofNat 714273491600600343758122738737), (Int.ofNat 508677434414089154898137317201), (Int.ofNat 105265216806766015066896228233), (Int.negOfNat 16282263374268635215527115421), (Int.negOfNat 2725880316175032941624352040), (Int.ofNat 230664626514610648236247130), (Int.ofNat 35084839078751274045582618), (Int.negOfNat 1953060923694768689364504), (Int.negOfNat 281265223607808585286617), (Int.ofNat 10975198120563752824470), (Int.ofNat 1540624365611005028301), (Int.negOfNat 43824048353440362405), (Int.negOfNat 6164499515979554098), (Int.ofNat 191439873046514699), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-989759846728475022987556870535373/1407374883553280000000000000000000), (-349907717587338704504544562248349/5629499534213120000000000000000000), (15115188727093224723138071289/5497558138880000000000000000000), (714273491600600343758122738737/5629499534213120000000000000000000), (508677434414089154898137317201/5629499534213120000000000000000000), (105265216806766015066896228233/5629499534213120000000000000000000), (-16282263374268635215527115421/5629499534213120000000000000000000), (-68147007904375823540608801/140737488355328000000000000000000), (23066462651461064823624713/562949953421312000000000000000000), (17542419539375637022791309/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial169.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial169.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial169.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial169 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 4581037978490041105150374264377087), (Int.negOfNat 258768902823006154240151077637815), (Int.ofNat 35199104092516261436573382083796), (Int.ofNat 5424378206517940386719316121447), (Int.ofNat 184718121395272545255172862876), (Int.negOfNat 167534885396162036437274444178), (Int.negOfNat 14814048851827006403872797091), (Int.ofNat 3076093736310048833499891574), (Int.ofNat 276925882952098590544636254), (Int.negOfNat 33385463830817319956418447), (Int.negOfNat 2900728078719153712377903), (Int.ofNat 232411373909232069729131), (Int.ofNat 19646552891526443849137), (Int.negOfNat 1118225708283352813367), (Int.negOfNat 92798946194775907885), (Int.ofNat 3987356984280283852), (Int.ofNat 340182971833986335), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-4581037978490041105150374264377087/5629499534213120000000000000000000), (-51753780564601230848030215527563/1125899906842624000000000000000000), (8799776023129065359143345520949/1407374883553280000000000000000000), (5424378206517940386719316121447/5629499534213120000000000000000000), (46179530348818136313793215719/1407374883553280000000000000000000), (-83767442698081018218637222089/2814749767106560000000000000000000), (-14814048851827006403872797091/5629499534213120000000000000000000), (1538046868155024416749945787/2814749767106560000000000000000000), (138462941476049295272318127/2814749767106560000000000000000000), (-33385463830817319956418447/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial169.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial169.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial169.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial169 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 4917292952394945295965457126180167), (Int.negOfNat 61643134412086827717196316236542), (Int.ofNat 57604238427785988401528369382271), (Int.negOfNat 163049893144314293061882365245), (Int.negOfNat 1369791215278707271442478891144), (Int.negOfNat 45130759409603346279197396115), (Int.ofNat 31378630316734734271017308199), (Int.ofNat 1484253158750851935552239486), (Int.negOfNat 443522589857669226177112876), (Int.negOfNat 22783353170968894444818013), (Int.ofNat 3863006456486673611065437), (Int.ofNat 204622124140500176993269), (Int.negOfNat 22381380225958460547623), (Int.negOfNat 1199347503734393585553), (Int.ofNat 92421721357376099235), (Int.ofNat 4965522266780885488), (Int.negOfNat 335636892540299145), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-4917292952394945295965457126180167/5629499534213120000000000000000000), (-30821567206043413858598158118271/2814749767106560000000000000000000), (57604238427785988401528369382271/5629499534213120000000000000000000), (-32609978628862858612376473049/1125899906842624000000000000000000), (-171223901909838408930309861393/703687441776640000000000000000000), (-9026151881920669255839479223/1125899906842624000000000000000000), (31378630316734734271017308199/5629499534213120000000000000000000), (742126579375425967776119743/2814749767106560000000000000000000), (-110880647464417306544278219/1407374883553280000000000000000000), (-22783353170968894444818013/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial169.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial169.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial169.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial169 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 4832750225567084774774601518416120), (Int.ofNat 125577904630922095203734074221571), (Int.ofNat 27817598336377161767696671150333), (Int.negOfNat 7926939593762136624170558104217), (Int.negOfNat 54004668784692285886296574290), (Int.ofNat 246105442817835256985371643694), (Int.ofNat 1672294876062297114288069809), (Int.negOfNat 4756063826270845926013345450), (Int.negOfNat 94057852831498569674663950), (Int.ofNat 53405483184898948806525942), (Int.ofNat 1494917274963915457702236), (Int.negOfNat 377771803714693273939583), (Int.negOfNat 12217414660461217393510), (Int.ofNat 1840783947685217328159), (Int.ofNat 63705139508925893835), (Int.negOfNat 6745990462622580622), (Int.negOfNat 271924451813576661), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-120818755639177119369365037960403/140737488355328000000000000000000), (125577904630922095203734074221571/5629499534213120000000000000000000), (27817598336377161767696671150333/5629499534213120000000000000000000), (-7926939593762136624170558104217/5629499534213120000000000000000000), (-5400466878469228588629657429/562949953421312000000000000000000), (123052721408917628492685821847/2814749767106560000000000000000000), (1672294876062297114288069809/5629499534213120000000000000000000), (-95121276525416918520266909/112589990684262400000000000000000), (-1881157056629971393493279/112589990684262400000000000000000), (26702741592449474403262971/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial169.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial169.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial169.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial169 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 4527226001773543812518603050669770), (Int.ofNat 157905605969272199818760132836395), (Int.negOfNat 4062829805012194011815165266332), (Int.negOfNat 785829608360004312865404293465), (Int.ofNat 1288981289642717008356504736176), (Int.negOfNat 67512626067758646183655121014), (Int.negOfNat 40408307538189368009140582760), (Int.ofNat 778468979005296329249044494), (Int.ofNat 622966816835125216157161367), (Int.ofNat 1488235053260823394876092), (Int.negOfNat 5515912942219267269930437), (Int.negOfNat 72290158138728109436211), (Int.ofNat 32026685357899647441924), (Int.ofNat 594060345078174318342), (Int.negOfNat 132644070491831861186), (Int.negOfNat 2825424401146135430), (Int.ofNat 445704652023878754), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-452722600177354381251860305066977/562949953421312000000000000000000), (31581121193854439963752026567279/1125899906842624000000000000000000), (-1015707451253048502953791316583/1407374883553280000000000000000000), (-157165921672000862573080858693/1125899906842624000000000000000000), (80561330602669813022281546011/351843720888320000000000000000000), (-33756313033879323091827560507/2814749767106560000000000000000000), (-1010207688454734200228514569/140737488355328000000000000000000), (389234489502648164624522247/2814749767106560000000000000000000), (622966816835125216157161367/5629499534213120000000000000000000), (372058763315205848719023/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial169.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial169.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial169.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial169 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 4217821358029012300037301152521942), (Int.ofNat 161274175878438687124008039076692), (Int.ofNat 8641714383172673107284100591760), (Int.ofNat 1836387587069790139706619705544), (Int.negOfNat 962001053688035382389020444986), (Int.negOfNat 248247822495809404243661096865), (Int.ofNat 23579032201593412306842895911), (Int.ofNat 6099733347389490037579583549), (Int.negOfNat 186839335980912165189120438), (Int.negOfNat 70347206714058574222127146), (Int.ofNat 532905640837412926687613), (Int.ofNat 494246190509612774011139), (Int.ofNat 1504245647740328578282), (Int.negOfNat 2390963696111053087174), (Int.negOfNat 20510721212865683747), (Int.ofNat 8664863257117825892), (Int.ofNat 112582797177931071), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-2108910679014506150018650576260971/2814749767106560000000000000000000), (40318543969609671781002009769173/1407374883553280000000000000000000), (108021429789658413841051257397/70368744177664000000000000000000), (229548448383723767463327463193/703687441776640000000000000000000), (-481000526844017691194510222493/2814749767106560000000000000000000), (-49649564499161880848732219373/1125899906842624000000000000000000), (23579032201593412306842895911/5629499534213120000000000000000000), (6099733347389490037579583549/5629499534213120000000000000000000), (-93419667990456082594560219/2814749767106560000000000000000000), (-35173603357029287111063573/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial169.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial169.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial169.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial169 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 3867143475496052184252119260643234), (Int.ofNat 174148481331419005796080941932935), (Int.negOfNat 14169022026982592966156548156125), (Int.negOfNat 9285508005905965095703067879682), (Int.negOfNat 787354100194773171612454507667), (Int.ofNat 339835889350002189142665572926), (Int.ofNat 49443753123656978401198530910), (Int.negOfNat 4117684415398001335226113153), (Int.negOfNat 788153553203858602652149531), (Int.ofNat 25771231402865321704771217), (Int.ofNat 6819521319848401956953661), (Int.negOfNat 93376186513065751581388), (Int.negOfNat 38802698308336803562859), (Int.ofNat 174961374929775191726), (Int.ofNat 158987200088611475461), (Int.ofNat 159884006773053002), (Int.negOfNat 502658526628909833), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-1933571737748026092126059630321617/2814749767106560000000000000000000), (34829696266283801159216188386587/1125899906842624000000000000000000), (-113352176215860743729252385249/45035996273704960000000000000000), (-4642754002952982547851533939841/2814749767106560000000000000000000), (-787354100194773171612454507667/5629499534213120000000000000000000), (169917944675001094571332786463/2814749767106560000000000000000000), (4944375312365697840119853091/562949953421312000000000000000000), (-4117684415398001335226113153/5629499534213120000000000000000000), (-788153553203858602652149531/5629499534213120000000000000000000), (25771231402865321704771217/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial169.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial169.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial169.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial169 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 3649074180950137903971984960218800), (Int.ofNat 14971560603376509295438810872295), (Int.negOfNat 53712502568911111468633868327669), (Int.ofNat 2436967486231955910389029261959), (Int.ofNat 3728872582272792672390422648486), (Int.ofNat 334651886058343502913387957936), (Int.negOfNat 59763459650476542866989564616), (Int.negOfNat 7860469082841039314411696652), (Int.ofNat 508889480135956964349809183), (Int.ofNat 84830090305251780490470334), (Int.negOfNat 2769699447482973140156807), (Int.negOfNat 571193816207606763840056), (Int.ofNat 10537224744969505303728), (Int.ofNat 2696235282851699533003), (Int.negOfNat 29506539495967254835), (Int.negOfNat 9559427603778787948), (Int.ofNat 46758857457714519), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-9122685452375344759929962400547/14073748835532800000000000000000), (2994312120675301859087762174459/1125899906842624000000000000000000), (-53712502568911111468633868327669/5629499534213120000000000000000000), (2436967486231955910389029261959/5629499534213120000000000000000000), (1864436291136396336195211324243/2814749767106560000000000000000000), (20915742878646468932086747371/351843720888320000000000000000000), (-7470432456309567858373695577/703687441776640000000000000000000), (-1965117270710259828602924163/1407374883553280000000000000000000), (508889480135956964349809183/5629499534213120000000000000000000), (42415045152625890245235167/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial169.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial169.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial169.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial169 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 3748775742725633063034116812362833), (Int.negOfNat 38838507301771486666507505309940), (Int.ofNat 58804888773790050163340429210337), (Int.ofNat 32993251353311467752135117347322), (Int.ofNat 2141558002363337331498664877087), (Int.negOfNat 681114829591166491406511976960), (Int.negOfNat 72389912897443100212637293742), (Int.ofNat 7357859579003751822004425218), (Int.ofNat 964810855019455861272647953), (Int.negOfNat 51528235335939588641035640), (Int.negOfNat 7678506668603395077437141), (Int.ofNat 257264727120651835981249), (Int.ofNat 41811173702534847207399), (Int.negOfNat 969342797961608309847), (Int.negOfNat 167232960019377773048), (Int.ofNat 2779121115209806226), (Int.ofNat 559612401233940912), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-3748775742725633063034116812362833/5629499534213120000000000000000000), (-1941925365088574333325375265497/281474976710656000000000000000000), (58804888773790050163340429210337/5629499534213120000000000000000000), (16496625676655733876067558673661/2814749767106560000000000000000000), (2141558002363337331498664877087/5629499534213120000000000000000000), (-266060480309049410705668741/2199023255552000000000000000000), (-36194956448721550106318646871/2814749767106560000000000000000000), (3678929789501875911002212609/2814749767106560000000000000000000), (964810855019455861272647953/5629499534213120000000000000000000), (-1288205883398489716025891/140737488355328000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial169.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial169.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial169.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial169 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 3318295652404483783242920736243771), (Int.ofNat 596571978401503141383268653017291), (Int.ofNat 242656404239760526737219772983205), (Int.ofNat 16768296361720126088721109687873), (Int.negOfNat 6167506684651573886683658113517), (Int.negOfNat 653930920985139508728105321743), (Int.ofNat 84197933360881735912196658356), (Int.ofNat 10249012146504797290118922378), (Int.negOfNat 742242898337336196279668280), (Int.negOfNat 95117054715900584776617711), (Int.ofNat 4631879095818325056628122), (Int.ofNat 595657667541143963357246), (Int.negOfNat 21551411875375842612464), (Int.negOfNat 2703637701336717033508), (Int.ofNat 77506151633558684299), (Int.ofNat 9276348008688994579), (Int.negOfNat 225085136961703802), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-3318295652404483783242920736243771/5629499534213120000000000000000000), (596571978401503141383268653017291/5629499534213120000000000000000000), (48531280847952105347443954596641/1125899906842624000000000000000000), (16768296361720126088721109687873/5629499534213120000000000000000000), (-6167506684651573886683658113517/5629499534213120000000000000000000), (-653930920985139508728105321743/5629499534213120000000000000000000), (21049483340220433978049164589/1407374883553280000000000000000000), (5124506073252398645059461189/2814749767106560000000000000000000), (-18556072458433404906991707/140737488355328000000000000000000), (-95117054715900584776617711/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial169.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial169.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial169.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial169.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial169 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial169 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial169 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 4791232656376489026347151101697310), (Int.negOfNat 820146744259745921848715823574377), (Int.ofNat 285858412907358054549554255678068), (Int.negOfNat 14895705384448342332477266435752), (Int.negOfNat 6396650293496539106393132191628), (Int.ofNat 648599991076863358996090883939), (Int.ofNat 84708095332276101301598364049), (Int.negOfNat 10241087746307043161227724628), (Int.negOfNat 742867225710094149883777280), (Int.ofNat 95109782862364456444991961), (Int.ofNat 4632360108905326157092372), (Int.negOfNat 595652927353859082871246), (Int.negOfNat 21551411875375842612464), (Int.ofNat 2703637701336717033508), (Int.ofNat 77506151633558684299), (Int.negOfNat 9276348008688994579), (Int.negOfNat 225085136961703802), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-479123265637648902634715110169731/562949953421312000000000000000000), (-820146744259745921848715823574377/5629499534213120000000000000000000), (71464603226839513637388563919517/1407374883553280000000000000000000), (-1861963173056042791559658304469/703687441776640000000000000000000), (-1599162573374134776598283047907/1407374883553280000000000000000000), (648599991076863358996090883939/5629499534213120000000000000000000), (84708095332276101301598364049/5629499534213120000000000000000000), (-2560271936576760790306931157/1407374883553280000000000000000000), (-580365020086011054596701/4398046511104000000000000000000), (95109782862364456444991961/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial169.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial169.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial169.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 5484876901784516488948022477198352), (Int.ofNat 2884645639470484552593871646270), (Int.ofNat 107443139723481605563102510850177), (Int.negOfNat 33082133193982812127357503105177), (Int.ofNat 1891211707640554805797765343920), (Int.ofNat 682281124498316753856441351896), (Int.negOfNat 71841951370897315138224382242), (Int.negOfNat 7360492081253480459452123218), (Int.ofNat 964146187350839752561818453), (Int.ofNat 51531122283553456617077140), (Int.negOfNat 7677996383568775913398141), (Int.negOfNat 257266504690883666163499), (Int.ofNat 41811173702534847207399), (Int.ofNat 969342797961608309847), (Int.negOfNat 167232960019377773048), (Int.negOfNat 2779121115209806226), (Int.ofNat 559612401233940912), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-342804806361532280559251404824897/351843720888320000000000000000000), (288464563947048455259387164627/562949953421312000000000000000000), (107443139723481605563102510850177/5629499534213120000000000000000000), (-33082133193982812127357503105177/5629499534213120000000000000000000), (23640146345506935072472066799/70368744177664000000000000000000), (85285140562289594232055168987/703687441776640000000000000000000), (-35920975685448657569112191121/2814749767106560000000000000000000), (-3680246040626740229726061609/2814749767106560000000000000000000), (964146187350839752561818453/5629499534213120000000000000000000), (2576556114177672830853857/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial169.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial169.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial169.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 5267174769120827772005839933793890), (Int.ofNat 134746579474183760933665372423722), (Int.negOfNat 11393980395423012903875556605941), (Int.negOfNat 4396936084071162337751058817279), (Int.ofNat 3521603782544452981783414994137), (Int.negOfNat 327419103152165899450022153087), (Int.negOfNat 59323185491115223054802094696), (Int.ofNat 7848090645679884487850632652), (Int.ofNat 508364010233107520253856433), (Int.negOfNat 84817879363965652127464584), (Int.negOfNat 2769298817920121593644807), (Int.ofNat 571186113403268833050306), (Int.ofNat 10537224744969505303728), (Int.negOfNat 2696235282851699533003), (Int.negOfNat 29506539495967254835), (Int.ofNat 9559427603778787948), (Int.ofNat 46758857457714519), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-526717476912082777200583993379389/562949953421312000000000000000000), (67373289737091880466832686211861/2814749767106560000000000000000000), (-11393980395423012903875556605941/5629499534213120000000000000000000), (-4396936084071162337751058817279/5629499534213120000000000000000000), (3521603782544452981783414994137/5629499534213120000000000000000000), (-327419103152165899450022153087/5629499534213120000000000000000000), (-7415398186389402881850261837/703687441776640000000000000000000), (1962022661419971121962658163/1407374883553280000000000000000000), (508364010233107520253856433/5629499534213120000000000000000000), (-10602234920495706515933073/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial169.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial169.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial169.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 5035271830111886104065836010422147), (Int.ofNat 115348624415754711555098753015357), (Int.ofNat 12090326491187077589844667922020), (Int.ofNat 6019342067105611882867278222801), (Int.negOfNat 899878851290132443764589560984), (Int.negOfNat 328567422227611667908974285469), (Int.ofNat 49661299777907861524929178853), (Int.ofNat 4098994799075230673341427153), (Int.negOfNat 788399033762827921040097031), (Int.negOfNat 25753065311263493956759217), (Int.ofNat 6819702715749327780988161), (Int.ofNat 93364928568264160427138), (Int.negOfNat 38802698308336803562859), (Int.negOfNat 174961374929775191726), (Int.ofNat 158987200088611475461), (Int.negOfNat 159884006773053002), (Int.negOfNat 502658526628909833), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-5035271830111886104065836010422147/5629499534213120000000000000000000), (115348624415754711555098753015357/5629499534213120000000000000000000), (604516324559353879492233396101/281474976710656000000000000000000), (6019342067105611882867278222801/5629499534213120000000000000000000), (-112484856411266555470573695123/703687441776640000000000000000000), (-328567422227611667908974285469/5629499534213120000000000000000000), (49661299777907861524929178853/5629499534213120000000000000000000), (4098994799075230673341427153/5629499534213120000000000000000000), (-788399033762827921040097031/5629499534213120000000000000000000), (-25753065311263493956759217/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial169.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial169.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial169.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 4729475762323023039996383953027365), (Int.ofNat 191400205299386174803258702250862), (Int.ofNat 13544247954014454895539723133632), (Int.negOfNat 5528011521466481459654526499137), (Int.negOfNat 954221179905434180562916039233), (Int.ofNat 260484682178346331219867877861), (Int.ofNat 23520072035505411497995047748), (Int.negOfNat 6119623507076135857121073799), (Int.negOfNat 186740981628913363782978688), (Int.ofNat 70366349767484179406165146), (Int.ofNat 532819254797547759551363), (Int.negOfNat 494258633501235585286889), (Int.ofNat 1504245647740328578282), (Int.ofNat 2390963696111053087174), (Int.negOfNat 20510721212865683747), (Int.negOfNat 8664863257117825892), (Int.ofNat 112582797177931071), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-945895152464604607999276790605473/1125899906842624000000000000000000), (95700102649693087401629351125431/2814749767106560000000000000000000), (211628874281475857742808173963/87960930222080000000000000000000), (-5528011521466481459654526499137/5629499534213120000000000000000000), (-954221179905434180562916039233/5629499534213120000000000000000000), (260484682178346331219867877861/5629499534213120000000000000000000), (5880018008876352874498761937/1407374883553280000000000000000000), (-6119623507076135857121073799/5629499534213120000000000000000000), (-1458913918975885654554521/43980465111040000000000000000000), (35183174883742089703082573/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial169.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial169.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial169.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 4342944727937252592412294945896389), (Int.ofNat 171287240115899693738259102311986), (Int.negOfNat 20171627589095010046436305571956), (Int.negOfNat 2374375727546765301801112723021), (Int.ofNat 1410208586539779088913130834606), (Int.ofNat 77452799700575703535283048837), (Int.negOfNat 40722314486793914131880316010), (Int.negOfNat 794173698006864612424211244), (Int.ofNat 623378846292806716074159367), (Int.negOfNat 1473337082118570407672092), (Int.negOfNat 5516241631693267195625187), (Int.ofNat 72280677764158348464211), (Int.ofNat 32026685357899647441924), (Int.negOfNat 594060345078174318342), (Int.negOfNat 132644070491831861186), (Int.ofNat 2825424401146135430), (Int.ofNat 445704652023878754), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-4342944727937252592412294945896389/5629499534213120000000000000000000), (85643620057949846869129551155993/2814749767106560000000000000000000), (-5042906897273752511609076392989/1407374883553280000000000000000000), (-2374375727546765301801112723021/5629499534213120000000000000000000), (705104293269889544456565417303/2814749767106560000000000000000000), (77452799700575703535283048837/5629499534213120000000000000000000), (-4072231448679391413188031601/562949953421312000000000000000000), (-198543424501716153106052811/1407374883553280000000000000000000), (623378846292806716074159367/5629499534213120000000000000000000), (-368334270529642601918023/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial169.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial169.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial169.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 4077564364973656267899511834197347), (Int.ofNat 105864903090517507626822583777893), (Int.negOfNat 3632874714339144826306921690793), (Int.ofNat 6075936852214484957694935812258), (Int.ofNat 143903381118014705780439196305), (Int.negOfNat 241040832253144796069181668384), (Int.ofNat 1193349593003875324330588309), (Int.ofNat 4748736928548060916934452950), (Int.negOfNat 93447611917936687045816700), (Int.negOfNat 53398865129347678134451192), (Int.ofNat 1494437253719711795918236), (Int.ofNat 377768248574229613575083), (Int.negOfNat 12217414660461217393510), (Int.negOfNat 1840783947685217328159), (Int.ofNat 63705139508925893835), (Int.ofNat 6745990462622580622), (Int.negOfNat 271924451813576661), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-4077564364973656267899511834197347/5629499534213120000000000000000000), (105864903090517507626822583777893/5629499534213120000000000000000000), (-3632874714339144826306921690793/5629499534213120000000000000000000), (3037968426107242478847467906129/2814749767106560000000000000000000), (28780676223602941156087839261/1125899906842624000000000000000000), (-7532526007910774877161927137/175921860444160000000000000000000), (1193349593003875324330588309/5629499534213120000000000000000000), (94974738570961218338689059/112589990684262400000000000000000), (-934476119179366870458167/56294995342131200000000000000000), (-6674858141168459766806399/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial169.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial169.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial169.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 3836534225387234812644942992811551), (Int.ofNat 151715641166728403871750526133200), (Int.ofNat 20083958847839538514924916556480), (Int.ofNat 18283280072243162554123732347), (Int.negOfNat 1151321744197567019505981302579), (Int.ofNat 44115332790797129842549821285), (Int.ofNat 30868245468576051190518212949), (Int.negOfNat 1481338773786754044669433236), (Int.negOfNat 442882896617066030396838376), (Int.ofNat 22779943611530837885094763), (Int.ofNat 3862507551774939939913937), (Int.negOfNat 204619161523447126689519), (Int.negOfNat 22381380225958460547623), (Int.ofNat 1199347503734393585553), (Int.ofNat 92421721357376099235), (Int.negOfNat 4965522266780885488), (Int.negOfNat 335636892540299145), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-3836534225387234812644942992811551/5629499534213120000000000000000000), (379289102916821009679376315333/14073748835532800000000000000000), (62762371399498557859140364239/17592186044416000000000000000000), (18283280072243162554123732347/5629499534213120000000000000000000), (-1151321744197567019505981302579/5629499534213120000000000000000000), (8823066558159425968509964257/1125899906842624000000000000000000), (30868245468576051190518212949/5629499534213120000000000000000000), (-370334693446688511167358309/1407374883553280000000000000000000), (-55360362077133253799604797/703687441776640000000000000000000), (22779943611530837885094763/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial169.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial169.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial169.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 3467942601390623355918291086704293), (Int.ofNat 203836837266172543965516419178610), (Int.ofNat 1852849064240361113577813730647), (Int.negOfNat 3940915176255342779440892152610), (Int.ofNat 363922393845154070340503888066), (Int.ofNat 160915427376983451319255420558), (Int.negOfNat 15215905381771864710671978311), (Int.negOfNat 3063895564660604593986732824), (Int.ofNat 277419479109861047762168004), (Int.ofNat 33373035768761466446588447), (Int.negOfNat 2901109586513977078924403), (Int.negOfNat 232403078581483528878631), (Int.ofNat 19646552891526443849137), (Int.ofNat 1118225708283352813367), (Int.negOfNat 92798946194775907885), (Int.negOfNat 3987356984280283852), (Int.ofNat 340182971833986335), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-3467942601390623355918291086704293/5629499534213120000000000000000000), (20383683726617254396551641917861/562949953421312000000000000000000), (1852849064240361113577813730647/5629499534213120000000000000000000), (-394091517625534277944089215261/562949953421312000000000000000000), (181961196922577035170251944033/2814749767106560000000000000000000), (80457713688491725659627710279/2814749767106560000000000000000000), (-15215905381771864710671978311/5629499534213120000000000000000000), (-382986945582575574248341603/703687441776640000000000000000000), (69354869777465261940542001/1407374883553280000000000000000000), (33373035768761466446588447/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial169.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial169.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial169.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 3074694048924545847570868349804777), (Int.ofNat 184525951634634937340820016686243), (Int.negOfNat 5283602988256241753750215806315), (Int.ofNat 1881391542081120605946250889471), (Int.ofNat 601489178442111687439186025971), (Int.negOfNat 115489048937138409770764541316), (Int.negOfNat 16467565557127361058638240671), (Int.ofNat 2743867571784779454405252040), (Int.ofNat 230877973618517495481694130), (Int.negOfNat 35102806139935672222539868), (Int.negOfNat 1953219880987700843667004), (Int.ofNat 281277074076020786501617), (Int.ofNat 10975198120563752824470), (Int.negOfNat 1540624365611005028301), (Int.negOfNat 43824048353440362405), (Int.ofNat 6164499515979554098), (Int.ofNat 191439873046514699), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-3074694048924545847570868349804777/5629499534213120000000000000000000), (184525951634634937340820016686243/5629499534213120000000000000000000), (-1056720597651248350750043161263/1125899906842624000000000000000000), (1881391542081120605946250889471/5629499534213120000000000000000000), (601489178442111687439186025971/5629499534213120000000000000000000), (-28872262234284602442691135329/1407374883553280000000000000000000), (-16467565557127361058638240671/5629499534213120000000000000000000), (68596689294619486360131301/140737488355328000000000000000000), (23087797361851749548169413/562949953421312000000000000000000), (-8775701534983918055634967/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial169.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial169.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial169.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 2706460217230824730386067159801483), (Int.ofNat 194193142241242291409703817955282), (Int.ofNat 9330909803141331827001687823484), (Int.ofNat 1183162674594497580214001460923), (Int.negOfNat 669694287175820867306939011878), (Int.negOfNat 56803419041442909731073516304), (Int.ofNat 22104513838670163878936875580), (Int.ofNat 1093288066133836204577103584), (Int.negOfNat 360995593752627829519814613), (Int.negOfNat 11372182007219484553820728), (Int.ofNat 3512932809685988804204113), (Int.ofNat 73344376451556518063299), (Int.negOfNat 22662196759098626982716), (Int.negOfNat 317899325520481038958), (Int.ofNat 104126576708043205994), (Int.ofNat 895110885288903810), (Int.negOfNat 336342982107503786), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-2706460217230824730386067159801483/5629499534213120000000000000000000), (97096571120621145704851908977641/2814749767106560000000000000000000), (2332727450785332956750421955871/1407374883553280000000000000000000), (1183162674594497580214001460923/5629499534213120000000000000000000), (-334847143587910433653469505939/2814749767106560000000000000000000), (-3550213690090181858192094769/351843720888320000000000000000000), (1105225691933508193946843779/281474976710656000000000000000000), (34165252066682381393034487/175921860444160000000000000000000), (-360995593752627829519814613/5629499534213120000000000000000000), (-1421522750902435569227591/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial169.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial169.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial169.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 2282357764080304807024905416536312), (Int.ofNat 224096492006354763936547479499065), (Int.ofNat 1194406038465493660417188345251), (Int.negOfNat 2951117273811962807581972901236), (Int.negOfNat 8074425232891554861239471516), (Int.ofNat 143835661217931591340519171932), (Int.ofNat 894166228083945890888557898), (Int.negOfNat 3124662338109418648161319441), (Int.negOfNat 9522063052258854462747548), (Int.ofNat 37955374337832427300704794), (Int.negOfNat 3603190966364110246957), (Int.negOfNat 293612891398184416769561), (Int.ofNat 734066834801034489842), (Int.ofNat 1570567732663455173066), (Int.negOfNat 6777536978767210267), (Int.negOfNat 6184909823640430068), (Int.negOfNat 32098218410869109), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-285294720510038100878113177067039/703687441776640000000000000000000), (44819298401270952787309495899813/1125899906842624000000000000000000), (1194406038465493660417188345251/5629499534213120000000000000000000), (-737779318452990701895493225309/1407374883553280000000000000000000), (-2018606308222888715309867879/1407374883553280000000000000000000), (35958915304482897835129792983/1407374883553280000000000000000000), (447083114041972945444278949/2814749767106560000000000000000000), (-3124662338109418648161319441/5629499534213120000000000000000000), (-2380515763064713615686887/1407374883553280000000000000000000), (18977687168916213650352397/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial169.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial169.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial169.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 1848848867827712978061340357226087), (Int.ofNat 203555483677207061810209393032944), (Int.negOfNat 6934586032114417368269372435384), (Int.ofNat 1306023085843404499621758692481), (Int.ofNat 739592048942433197200987199193), (Int.negOfNat 43797481531615453071123264241), (Int.negOfNat 22396175534175843516533470790), (Int.ofNat 813427028177836967718220877), (Int.ofNat 349944852511254808371369679), (Int.negOfNat 9689266151304009873467983), (Int.negOfNat 3313134095502771153246409), (Int.ofNat 78398853858883587309502), (Int.ofNat 20987271865222119722781), (Int.negOfNat 448482423781293530034), (Int.negOfNat 94814372559665231219), (Int.ofNat 1963192747707060882), (Int.ofNat 279389107502472707), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-1848848867827712978061340357226087/5629499534213120000000000000000000), (12722217729825441363138087064559/351843720888320000000000000000000), (-866823254014302171033671554423/703687441776640000000000000000000), (1306023085843404499621758692481/5629499534213120000000000000000000), (739592048942433197200987199193/5629499534213120000000000000000000), (-43797481531615453071123264241/5629499534213120000000000000000000), (-2239617553417584351653347079/562949953421312000000000000000000), (813427028177836967718220877/5629499534213120000000000000000000), (349944852511254808371369679/5629499534213120000000000000000000), (-9689266151304009873467983/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial169.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial169.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial169.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 1449843869413586898885359985770669), (Int.ofNat 208037334137032863378301098550644), (Int.ofNat 10867310921929407076928135659210), (Int.ofNat 2872591397679072103230909751489), (Int.negOfNat 500334267477690001748205501939), (Int.negOfNat 129490212784892407654558810071), (Int.ofNat 12778076724689880942299751684), (Int.ofNat 2696310082390155065801155108), (Int.negOfNat 185365064114060772916265777), (Int.negOfNat 31970191520567641284155836), (Int.ofNat 1726237273960660251623733), (Int.ofNat 243777158648612612332074), (Int.negOfNat 11071459998366314381132), (Int.negOfNat 1293157549471422937957), (Int.ofNat 51143086960921706525), (Int.ofNat 5105073183993648052), (Int.negOfNat 127243436224776481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-1449843869413586898885359985770669/5629499534213120000000000000000000), (52009333534258215844575274637661/1407374883553280000000000000000000), (1086731092192940707692813565921/562949953421312000000000000000000), (2872591397679072103230909751489/5629499534213120000000000000000000), (-500334267477690001748205501939/5629499534213120000000000000000000), (-129490212784892407654558810071/5629499534213120000000000000000000), (3194519181172470235574937921/1407374883553280000000000000000000), (674077520597538766450288777/1407374883553280000000000000000000), (-185365064114060772916265777/5629499534213120000000000000000000), (-7992547880141910321038959/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial169.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial169.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial169.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 978366946973223480077492535844515), (Int.ofNat 263016875858954310776199798344655), (Int.ofNat 10160605156927459427378286450357), (Int.negOfNat 3224078095067715696476685212772), (Int.negOfNat 578410972962401966638116968523), (Int.ofNat 122487556113433385768878170817), (Int.ofNat 16797622283457236227101877308), (Int.negOfNat 2321935318194507764340193512), (Int.negOfNat 255980125102406278389096997), (Int.ofNat 26473068788260923229743840), (Int.ofNat 2392901509558555934619999), (Int.negOfNat 200079267414388643583501), (Int.negOfNat 15078006003552222424201), (Int.ofNat 1067800150163221726773), (Int.ofNat 68230957250209189532), (Int.negOfNat 4335576113579054654), (Int.negOfNat 222435232897441628), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-195673389394644696015498507168903/1125899906842624000000000000000000), (52603375171790862155239959668931/1125899906842624000000000000000000), (10160605156927459427378286450357/5629499534213120000000000000000000), (-806019523766928924119171303193/1407374883553280000000000000000000), (-578410972962401966638116968523/5629499534213120000000000000000000), (122487556113433385768878170817/5629499534213120000000000000000000), (4199405570864309056775469327/1407374883553280000000000000000000), (-290241914774313470542524189/703687441776640000000000000000000), (-255980125102406278389096997/5629499534213120000000000000000000), (165456679926630770185899/35184372088832000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial169.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial169.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial169.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 442090521231354079909312315408956), (Int.ofNat 258253690411797313017145044403810), (Int.negOfNat 11111256978109396817305176171342), (Int.negOfNat 1853964931256413900359417077534), (Int.ofNat 846467902702350759617594933678), (Int.ofNat 79966024425952841227865605847), (Int.negOfNat 22124158874227004161755166181), (Int.negOfNat 1607635464407769652604279272), (Int.ofNat 320769431261462341080227880), (Int.ofNat 18764525617204214542741799), (Int.negOfNat 2940533743397688335106918), (Int.negOfNat 142675850288707782614204), (Int.ofNat 18448652467169172388296), (Int.ofNat 760265358818575035392), (Int.negOfNat 83755398789920923301), (Int.negOfNat 3078325090955680261), (Int.ofNat 267600465992078378), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-110522630307838519977328078852239/1407374883553280000000000000000000), (25825369041179731301714504440381/562949953421312000000000000000000), (-5555628489054698408652588085671/2814749767106560000000000000000000), (-926982465628206950179708538767/2814749767106560000000000000000000), (423233951351175379808797466839/2814749767106560000000000000000000), (79966024425952841227865605847/5629499534213120000000000000000000), (-22124158874227004161755166181/5629499534213120000000000000000000), (-200954433050971206575534909/703687441776640000000000000000000), (8019235781536558527005697/140737488355328000000000000000000), (18764525617204214542741799/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial169.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial169.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial169.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 29709289396337228417248619423839), (Int.ofNat 220432801404583119200677671185631), (Int.negOfNat 1287935949519919418131192830711), (Int.ofNat 4303015801818675342809310931150), (Int.ofNat 260437854877531620118234670661), (Int.negOfNat 164933900781407643774352156049), (Int.negOfNat 6896157515901998101414401339), (Int.ofNat 3161691685672074477576906978), (Int.ofNat 100796144040492512312828920), (Int.negOfNat 36132724881083229262828381), (Int.negOfNat 937348521590014258656892), (Int.ofNat 272058669122161956777936), (Int.ofNat 6001455789689632142494), (Int.negOfNat 1442364751954795819638), (Int.negOfNat 27854339022666166209), (Int.ofNat 5696293365145748819), (Int.ofNat 78238213403657182), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(29709289396337228417248619423839/5629499534213120000000000000000000), (220432801404583119200677671185631/5629499534213120000000000000000000), (-1287935949519919418131192830711/5629499534213120000000000000000000), (86060316036373506856186218623/112589990684262400000000000000000), (260437854877531620118234670661/5629499534213120000000000000000000), (-164933900781407643774352156049/5629499534213120000000000000000000), (-6896157515901998101414401339/5629499534213120000000000000000000), (1580845842836037238788453489/2814749767106560000000000000000000), (2519903601012312807820723/140737488355328000000000000000000), (-36132724881083229262828381/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial169.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial169.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial169.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 498706651818633762282075623545674), (Int.ofNat 262167221774927546434858182389292), (Int.ofNat 18066694152863216570671950485893), (Int.ofNat 440039667899180210815576940623), (Int.negOfNat 951078404311922155464246467095), (Int.negOfNat 9184624084885708181224642376), (Int.ofNat 25279687613896690889583138552), (Int.ofNat 98944284489865231307379398), (Int.negOfNat 371657511112927833977755313), (Int.negOfNat 903796083329125124689940), (Int.ofNat 3435820132000072193776841), (Int.ofNat 8240668671476637337029), (Int.negOfNat 21650338250297445250539), (Int.negOfNat 60334001233370217447), (Int.ofNat 98244832921175570228), (Int.ofNat 429570338281060306), (Int.negOfNat 335858986012488052), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(249353325909316881141037811772837/2814749767106560000000000000000000), (65541805443731886608714545597323/1407374883553280000000000000000000), (18066694152863216570671950485893/5629499534213120000000000000000000), (440039667899180210815576940623/5629499534213120000000000000000000), (-190215680862384431092849293419/1125899906842624000000000000000000), (-1148078010610713522653080297/703687441776640000000000000000000), (3159960951737086361197892319/703687441776640000000000000000000), (49472142244932615653689699/2814749767106560000000000000000000), (-371657511112927833977755313/5629499534213120000000000000000000), (-45189804166456256234497/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial169.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial169.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial169.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1084855432271783877736035273796234), (Int.ofNat 313077723054357140878373223954004), (Int.ofNat 2648097242099006504131437109061), (Int.negOfNat 4055944558200754127497346261621), (Int.ofNat 125519515796475151960436014658), (Int.ofNat 159992486987452635199099528727), (Int.negOfNat 5121801601242875628593912334), (Int.negOfNat 3149380807138270501820917562), (Int.ofNat 85519584854547319347645357), (Int.ofNat 36754351910207948187711944), (Int.negOfNat 796458016322675574706383), (Int.negOfNat 281235563891985614200916), (Int.ofNat 4738520638973222201402), (Int.ofNat 1507984660088013336903), (Int.negOfNat 19617352493484502045), (Int.negOfNat 5979372960235542188), (Int.ofNat 100088066100332101), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(542427716135891938868017636898117/2814749767106560000000000000000000), (78269430763589285219593305988501/1407374883553280000000000000000000), (2648097242099006504131437109061/5629499534213120000000000000000000), (-4055944558200754127497346261621/5629499534213120000000000000000000), (62759757898237575980218007329/2814749767106560000000000000000000), (159992486987452635199099528727/5629499534213120000000000000000000), (-2560900800621437814296956167/2814749767106560000000000000000000), (-1574690403569135250910458781/2814749767106560000000000000000000), (85519584854547319347645357/5629499534213120000000000000000000), (4594293988775993523463993/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial169.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial169.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial169.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 1695592217629141194695144679264737), (Int.ofNat 289585693776236067913914834280587), (Int.negOfNat 8915249714768113540855021590771), (Int.ofNat 1092449313395683826439015704164), (Int.ofNat 758818065999395438346105822499), (Int.negOfNat 67405868774747117084027607548), (Int.negOfNat 21187771077100510304511082003), (Int.ofNat 1530056837897996025046555847), (Int.ofNat 323892050489374056081878101), (Int.negOfNat 18421387101948182906942843), (Int.negOfNat 3095511947037410933829271), (Int.ofNat 137275546989729531141972), (Int.ofNat 20031930699870693945829), (Int.negOfNat 695330265896696935784), (Int.negOfNat 92785133458056418481), (Int.ofNat 2509434783701798922), (Int.ofNat 278905111407456973), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(1695592217629141194695144679264737/5629499534213120000000000000000000), (289585693776236067913914834280587/5629499534213120000000000000000000), (-8915249714768113540855021590771/5629499534213120000000000000000000), (273112328348920956609753926041/1407374883553280000000000000000000), (758818065999395438346105822499/5629499534213120000000000000000000), (-16851467193686779271006901887/1407374883553280000000000000000000), (-21187771077100510304511082003/5629499534213120000000000000000000), (1530056837897996025046555847/5629499534213120000000000000000000), (323892050489374056081878101/5629499534213120000000000000000000), (-18421387101948182906942843/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial169.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial169.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial169.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 2256736802903332801021688100491796), (Int.ofNat 282816573983645938670231114024256), (Int.ofNat 6866688592663140568953003499544), (Int.ofNat 2375170000315033960388904476067), (Int.negOfNat 503213810209174468825309729020), (Int.negOfNat 104354330571031535064865391354), (Int.ofNat 16727865175597414008435443352), (Int.ofNat 2209256724849119942100775429), (Int.negOfNat 268452535010579937146501272), (Int.negOfNat 27547509798522561476828876), (Int.ofNat 2519845845491735776053437), (Int.ofNat 222861123237140334594179), (Int.negOfNat 15456944847714058708052), (Int.negOfNat 1246135358364651031284), (Int.ofNat 66813325925438780327), (Int.ofNat 5084808613574580132), (Int.negOfNat 259429720735977691), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(564184200725833200255422025122949/1407374883553280000000000000000000), (4419008968494467791722361156629/87960930222080000000000000000000), (858336074082892571119125437443/703687441776640000000000000000000), (2375170000315033960388904476067/5629499534213120000000000000000000), (-25160690510458723441265486451/281474976710656000000000000000000), (-52177165285515767532432695677/2814749767106560000000000000000000), (2090983146949676751054430419/703687441776640000000000000000000), (2209256724849119942100775429/5629499534213120000000000000000000), (-33556566876322492143312659/703687441776640000000000000000000), (-6886877449630640369207219/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial169.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial169.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial169.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 2858720810225319384277113541389742), (Int.ofNat 318212286720402447301080172079038), (Int.ofNat 5617622444994032150273497205960), (Int.negOfNat 2494163317437385985632168269081), (Int.negOfNat 295285484567425508468562821122), (Int.ofNat 131168930260988165096005189088), (Int.ofNat 9714755504831263692036412260), (Int.negOfNat 2949503939245049883781372976), (Int.negOfNat 174162249137813225430380407), (Int.ofNat 35925101789063548914174822), (Int.ofNat 1906065990736860389086157), (Int.negOfNat 271376924169233545913101), (Int.negOfNat 13620361446462230393134), (Int.ofNat 1392338210438962960762), (Int.ofNat 67562267082072117906), (Int.negOfNat 5174975178074881350), (Int.negOfNat 221951236802425894), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(1429360405112659692138556770694871/2814749767106560000000000000000000), (159106143360201223650540086039519/2814749767106560000000000000000000), (140440561124850803756837430149/140737488355328000000000000000000), (-2494163317437385985632168269081/5629499534213120000000000000000000), (-147642742283712754234281410561/2814749767106560000000000000000000), (4099029070655880159250162159/175921860444160000000000000000000), (485737775241563184601820613/281474976710656000000000000000000), (-184343996202815617736335811/351843720888320000000000000000000), (-174162249137813225430380407/5629499534213120000000000000000000), (17962550894531774457087411/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial169.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial169.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial169.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 3497354773456810199125410153694442), (Int.ofNat 312251928218835737228125662646329), (Int.negOfNat 5724137781674613530136446667876), (Int.ofNat 190710778730372689234377232813), (Int.ofNat 736207815820885248098318813469), (Int.ofNat 863840896711534888080157547), (Int.negOfNat 25013088061533407397841356129), (Int.negOfNat 338219597539526137595531560), (Int.ofNat 414929276592329274234373370), (Int.ofNat 8707091647647321946445632), (Int.negOfNat 3975354579813589760664596), (Int.negOfNat 101232791616700450769863), (Int.ofNat 24601000948357855525810), (Int.ofNat 685668986719181733079), (Int.negOfNat 106881478942635175255), (Int.negOfNat 3165935819079334862), (Int.ofNat 418771375371623281), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(1748677386728405099562705076847221/2814749767106560000000000000000000), (312251928218835737228125662646329/5629499534213120000000000000000000), (-1431034445418653382534111666969/1407374883553280000000000000000000), (190710778730372689234377232813/5629499534213120000000000000000000), (736207815820885248098318813469/5629499534213120000000000000000000), (863840896711534888080157547/5629499534213120000000000000000000), (-25013088061533407397841356129/5629499534213120000000000000000000), (-8455489938488153439888289/140737488355328000000000000000000), (41492927659232927423437337/562949953421312000000000000000000), (136048306994489405413213/87960930222080000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial169.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial169.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial169.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 4110757109600974535243317490975097), (Int.ofNat 310741711387805724144186130307225), (Int.ofNat 7664556073711506119318299398974), (Int.ofNat 2651342896966072155419016648543), (Int.negOfNat 405264797441626702451345905006), (Int.negOfNat 156708431898572398228346556792), (Int.ofNat 9239502687841437471111221601), (Int.ofNat 3852475282387391347800057816), (Int.negOfNat 76344480503804282386040904), (Int.negOfNat 49228848703031389105601283), (Int.ofNat 42000657773426095232483), (Int.ofNat 376505387514824740150429), (Int.ofNat 3172616126369599661193), (Int.negOfNat 1935503882742079750443), (Int.negOfNat 25826609701757101245), (Int.ofNat 7315073043709631408), (Int.ofNat 111883477318846285), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(4110757109600974535243317490975097/5629499534213120000000000000000000), (12429668455512228965767445212289/225179981368524800000000000000000), (3832278036855753059659149699487/2814749767106560000000000000000000), (2651342896966072155419016648543/5629499534213120000000000000000000), (-202632398720813351225672952503/2814749767106560000000000000000000), (-19588553987321549778543319599/703687441776640000000000000000000), (9239502687841437471111221601/5629499534213120000000000000000000), (481559410298423918475007227/703687441776640000000000000000000), (-9543060062975535298255113/703687441776640000000000000000000), (-49228848703031389105601283/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial169.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial169.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial169.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 4773651099966017525216520115768007), (Int.ofNat 351023625556077316356342669949712), (Int.ofNat 5763260139766286467624148036119), (Int.negOfNat 3608536019599507780994665942975), (Int.negOfNat 607126648258107942956521270586), (Int.ofNat 155477269190054778738813608005), (Int.ofNat 27010776839208295193061486971), (Int.negOfNat 2561031069503607766137885836), (Int.negOfNat 511378997209940764663461914), (Int.ofNat 18587105978232594388822103), (Int.ofNat 5022768350438851189657863), (Int.negOfNat 69071376707930831500709), (Int.negOfNat 31060025025558383610327), (Int.ofNat 94284061522047314603), (Int.ofNat 134192226189872294195), (Int.ofNat 407302340737038092), (Int.negOfNat 487029895392032955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(4773651099966017525216520115768007/5629499534213120000000000000000000), (21938976597254832272271416871857/351843720888320000000000000000000), (5763260139766286467624148036119/5629499534213120000000000000000000), (-144341440783980311239786637719/225179981368524800000000000000000), (-303563324129053971478260635293/2814749767106560000000000000000000), (31095453838010955747762721601/1125899906842624000000000000000000), (27010776839208295193061486971/5629499534213120000000000000000000), (-640257767375901941534471459/1407374883553280000000000000000000), (-255689498604970382331730957/2814749767106560000000000000000000), (18587105978232594388822103/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial169.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial169.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial169.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 5466428708627027998124524285755820), (Int.ofNat 327366458004944434926222837737549), (Int.negOfNat 14036099556864861427658796287833), (Int.negOfNat 104518427820261008583784910913), (Int.ofNat 1414225238011648835680960591260), (Int.ofNat 108332437007165676765046835706), (Int.negOfNat 39487544253291329582844020699), (Int.negOfNat 4329086725434293075175217290), (Int.ofNat 418726385399167515421665890), (Int.ofNat 58365026684877670211397928), (Int.negOfNat 2509418329493447892480816), (Int.negOfNat 443990760311793687997697), (Int.ofNat 9765971187663515006750), (Int.ofNat 2258045241491277208181), (Int.negOfNat 25914941985658207975), (Int.negOfNat 8514050292908300018), (Int.ofNat 32313542174938161), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(273321435431351399906226214287791/281474976710656000000000000000000), (327366458004944434926222837737549/5629499534213120000000000000000000), (-14036099556864861427658796287833/5629499534213120000000000000000000), (-104518427820261008583784910913/5629499534213120000000000000000000), (70711261900582441784048029563/281474976710656000000000000000000), (54166218503582838382523417853/2814749767106560000000000000000000), (-39487544253291329582844020699/5629499534213120000000000000000000), (-432908672543429307517521729/562949953421312000000000000000000), (41872638539916751542166589/562949953421312000000000000000000), (7295628335609708776424741/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial169.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial169.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial169.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 6087327650557878782285665505138210), (Int.ofNat 314914356605062625827511574546585), (Int.ofNat 16537530047585607292035251748822), (Int.ofNat 7808841217430412159316078071145), (Int.negOfNat 430012012432953366747650295096), (Int.negOfNat 455589487058480521715257263936), (Int.negOfNat 27938792276381201518376988320), (Int.ofNat 6492751853784411896468233936), (Int.ofNat 590404848739030867171840243), (Int.negOfNat 50622358088730336988041712), (Int.negOfNat 5673868422162558203302713), (Int.ofNat 260552972667891552734511), (Int.ofNat 34245891578979090593346), (Int.negOfNat 967742527363704739382), (Int.negOfNat 146047777324580353514), (Int.ofNat 2684943758254341950), (Int.ofNat 483189905665550406), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(608732765055787878228566550513821/562949953421312000000000000000000), (62982871321012525165502314909317/1125899906842624000000000000000000), (8268765023792803646017625874411/2814749767106560000000000000000000), (1561768243486082431863215614229/1125899906842624000000000000000000), (-53751501554119170843456286887/703687441776640000000000000000000), (-7118585735288758151800894749/87960930222080000000000000000000), (-174617451727382509489856177/35184372088832000000000000000000), (405796990861525743529264621/351843720888320000000000000000000), (590404848739030867171840243/5629499534213120000000000000000000), (-3163897380545646061752607/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial169.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial169.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial169.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 6823481226083091035084939372608222), (Int.ofNat 422570132351006199388029667083858), (Int.ofNat 15049769825147583936755871502600), (Int.negOfNat 13975912779350280324876098078734), (Int.negOfNat 4448524002880637105416221654644), (Int.negOfNat 118051442560022090434757214095), (Int.ofNat 81565753980013857457304880999), (Int.ofNat 5283039510907557732289365711), (Int.negOfNat 791157890775549113213060582), (Int.negOfNat 65425890237253577214730994), (Int.ofNat 5023716897215856626298587), (Int.ofNat 471578548167843374477851), (Int.negOfNat 22910971450376949843892), (Int.negOfNat 2323165387260377748036), (Int.ofNat 79302587785512926487), (Int.ofNat 8534460600569175988), (Int.negOfNat 191655196810583751), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(3411740613041545517542469686304111/2814749767106560000000000000000000), (211285066175503099694014833541929/2814749767106560000000000000000000), (75248849125737919683779357513/28147497671065600000000000000000), (-6987956389675140162438049039367/2814749767106560000000000000000000), (-1112131000720159276354055413661/1407374883553280000000000000000000), (-23610288512004418086951442819/1125899906842624000000000000000000), (81565753980013857457304880999/5629499534213120000000000000000000), (5283039510907557732289365711/5629499534213120000000000000000000), (-395578945387774556606530291/2814749767106560000000000000000000), (-32712945118626788607365497/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial169.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial169.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial169.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 7547725639242900211363018840843494), (Int.ofNat 180358271896969963047908252926345), (Int.negOfNat 163538382620735794340403181158975), (Int.negOfNat 39952727957815234479960903656508), (Int.negOfNat 321948838377086408319845186143), (Int.ofNat 869647171258499893437636084074), (Int.ofNat 45019038511791134423315220660), (Int.negOfNat 10272874684999360055034398767), (Int.negOfNat 697994046581867076370236089), (Int.ofNat 79229822925082747592352643), (Int.ofNat 5953049809634312758519699), (Int.negOfNat 434062666887033155311642), (Int.negOfNat 33854711280206162216571), (Int.ofNat 1781086938867879018384), (Int.ofNat 139556860453081039039), (Int.negOfNat 5543247391250306642), (Int.negOfNat 426236031060519327), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(3773862819621450105681509420421747/2814749767106560000000000000000000), (36071654379393992609581650585269/1125899906842624000000000000000000), (-6541535304829431773616127246359/225179981368524800000000000000000), (-9988181989453808619990225914127/1407374883553280000000000000000000), (-321948838377086408319845186143/5629499534213120000000000000000000), (434823585629249946718818042037/2814749767106560000000000000000000), (2250951925589556721165761033/281474976710656000000000000000000), (-10272874684999360055034398767/5629499534213120000000000000000000), (-697994046581867076370236089/5629499534213120000000000000000000), (79229822925082747592352643/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial169.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial169.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial169.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 6958777611614567940086223772778570), (Int.negOfNat 890424508507383420757054649374945), (Int.negOfNat 338339866896137292650488370123461), (Int.negOfNat 7047157421549641222063534463549), (Int.ofNat 7795121909976758343413735485584), (Int.ofNat 426427991160569350689494964544), (Int.negOfNat 111670312085842166453392642064), (Int.negOfNat 7221301357798520575844566758), (Int.ofNat 1052866546783373079451902827), (Int.ofNat 70179173043992318650663366), (Int.negOfNat 6948153181166911491492423), (Int.negOfNat 454703291976703080748884), (Int.ofNat 33714162171812666236422), (Int.ofNat 2117878735994579630617), (Int.negOfNat 124788400988462736445), (Int.negOfNat 7454623960922393972), (Int.ofNat 350996851446229341), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(695877761161456794008622377277857/562949953421312000000000000000000), (-178084901701476684151410929874989/1125899906842624000000000000000000), (-338339866896137292650488370123461/5629499534213120000000000000000000), (-7047157421549641222063534463549/5629499534213120000000000000000000), (487195119373547396463358467849/351843720888320000000000000000000), (6662937361883896104523358821/87960930222080000000000000000000), (-6979394505365135403337040129/351843720888320000000000000000000), (-3610650678899260287922283379/2814749767106560000000000000000000), (1052866546783373079451902827/5629499534213120000000000000000000), (35089586521996159325331683/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial169.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial169.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial169.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 3898785859986295269818281857951233), (Int.negOfNat 2068267510417249844579493366575850), (Int.negOfNat 188959395628748646765445078470807), (Int.ofNat 52602161420916579597369216123178), (Int.ofNat 4691703769904289559257027240843), (Int.negOfNat 972545720682806447638988801300), (Int.negOfNat 75407888453627119022220175808), (Int.ofNat 11681725068536614998543402582), (Int.ofNat 790737823823644374814065047), (Int.negOfNat 95001652397408253362180510), (Int.negOfNat 5694734332564423991249879), (Int.ofNat 551815875741504125265831), (Int.ofNat 29618546346508316030861), (Int.negOfNat 2390008285569623043333), (Int.negOfNat 116099710422488812512), (Int.ofNat 7915630757122300414), (Int.ofNat 369282156455488248), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(3898785859986295269818281857951233/5629499534213120000000000000000000), (-41365350208344996891589867331517/112589990684262400000000000000000), (-188959395628748646765445078470807/5629499534213120000000000000000000), (26301080710458289798684608061589/2814749767106560000000000000000000), (4691703769904289559257027240843/5629499534213120000000000000000000), (-9725457206828064476389888013/56294995342131200000000000000000), (-1178248257087923734722190247/87960930222080000000000000000000), (5840862534268307499271701291/2814749767106560000000000000000000), (790737823823644374814065047/5629499534213120000000000000000000), (-9500165239740825336218051/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial169.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial169.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial169.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 532005311919259439337047872127759), (Int.negOfNat 2129224714827724274691184999885821), (Int.ofNat 152133786334260315582231429405655), (Int.ofNat 46555143675892071661578978009657), (Int.negOfNat 5835208504369603640513688810713), (Int.negOfNat 760931012185244419079678413327), (Int.ofNat 103041751402605943073420436154), (Int.ofNat 8551944679002652546420169612), (Int.negOfNat 1094628654987507350762677710), (Int.negOfNat 67208871686649637415608539), (Int.ofNat 7828222330514502378277818), (Int.ofNat 383937691153685185274394), (Int.negOfNat 40243246988886725222946), (Int.negOfNat 1650648408879949775382), (Int.ofNat 155887404571602698511), (Int.ofNat 5427875867884426181), (Int.negOfNat 491353881213531238), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-532005311919259439337047872127759/5629499534213120000000000000000000), (-2129224714827724274691184999885821/5629499534213120000000000000000000), (30426757266852063116446285881131/1125899906842624000000000000000000), (46555143675892071661578978009657/5629499534213120000000000000000000), (-5835208504369603640513688810713/5629499534213120000000000000000000), (-760931012185244419079678413327/5629499534213120000000000000000000), (51520875701302971536710218077/2814749767106560000000000000000000), (2137986169750663136605042403/1407374883553280000000000000000000), (-109462865498750735076267771/562949953421312000000000000000000), (-67208871686649637415608539/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial169.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial169.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial169.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial169.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial169.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial169.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial169.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial169.reflect := by
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

end Bin169
end
end ErdosOverlap.OuterNumerics
