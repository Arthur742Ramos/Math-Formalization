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

/-! # Exact integer weighted outer models for source bin 137

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin137

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 3395555336259411000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 3107578896524343400)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 2210407820222132200)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 1204187383291012000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 573594578300457640)⟩, ⟨(19494472361809/1000000000000), (Int.negOfNat 598561146797435200)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 802809704052947100)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 125224701897935080)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 404123826088561700)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 84807045917867350)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial137.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial137.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9794205938015115000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1671391400763822800)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1650672304785242600)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 594660788379798650)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 103824347411274610)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 140159916506898580)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 74496649458571035)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 1550342573467309)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 20918040814657640)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial137.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial137.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9794205938015115000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1671391400763822800)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1650672304785242600)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 594660788379798650)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 103824347411274610)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 140159916506898580)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 74496649458571035)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 1550342573467309)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 20918040814657640)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial137.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial137.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial137.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 10534671137532949061033953800965038), (Int.ofNat 4627193789004413065763806914230543), (Int.ofNat 961346146008188254855245706919844), (Int.negOfNat 146904977761442656875251130878197), (Int.negOfNat 25340279818668311555852718645723), (Int.ofNat 2899725240007473919746021865528), (Int.ofNat 360959330678141061244169710638), (Int.negOfNat 34543439634722242167541438717), (Int.negOfNat 3190210292863318584564448283), (Int.ofNat 269836421512410728035290611), (Int.ofNat 19144151603924312708375331), (Int.negOfNat 1486705363226483967103060), (Int.negOfNat 83395704940553272091344), (Int.ofNat 6098597425916432709588), (Int.ofNat 276212633197318436395), (Int.negOfNat 19046277860077060394), (Int.negOfNat 701100468216485301), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-5267335568766474530516976900482519/5629499534213120000000000000000000), (4627193789004413065763806914230543/11258999068426240000000000000000000), (240336536502047063713811426729961/2814749767106560000000000000000000), (-146904977761442656875251130878197/11258999068426240000000000000000000), (-25340279818668311555852718645723/11258999068426240000000000000000000), (362465655000934239968252733191/1407374883553280000000000000000000), (180479665339070530622084855319/5629499534213120000000000000000000), (-34543439634722242167541438717/11258999068426240000000000000000000), (-3190210292863318584564448283/11258999068426240000000000000000000), (269836421512410728035290611/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial137.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial137.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial137.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial137 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 1095225503375240886114431823944183), (Int.ofNat 6182070936920370274493312052108665), (Int.negOfNat 237154721266220252216620147794721), (Int.negOfNat 199271440431322008171060978091380), (Int.ofNat 13343703336510614725966770254381), (Int.ofNat 3548558067740672115560170390627), (Int.negOfNat 259710839073945992807512023927), (Int.negOfNat 37559010271826173075907857828), (Int.ofNat 2776560780275640498621539732), (Int.ofNat 259444360430009782343582509), (Int.negOfNat 19290079824217577265106019), (Int.negOfNat 1260575148766969433971820), (Int.ofNat 95137356904467333710166), (Int.ofNat 4559656862077855268672), (Int.negOfNat 352385856394575163330), (Int.negOfNat 12403822043229981881), (Int.ofNat 1082995653345731019), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(1095225503375240886114431823944183/11258999068426240000000000000000000), (1236414187384074054898662410421733/2251799813685248000000000000000000), (-237154721266220252216620147794721/11258999068426240000000000000000000), (-9963572021566100408553048904569/562949953421312000000000000000000), (13343703336510614725966770254381/11258999068426240000000000000000000), (3548558067740672115560170390627/11258999068426240000000000000000000), (-259710839073945992807512023927/11258999068426240000000000000000000), (-9389752567956543268976964457/2814749767106560000000000000000000), (694140195068910124655384933/2814749767106560000000000000000000), (259444360430009782343582509/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial137.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial137.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial137.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial137 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 11223022754523827217216267522182069), (Int.ofNat 3489717532789254909099327477216779), (Int.negOfNat 910299679660606995428966428448463), (Int.negOfNat 7133673388525131750532523821971), (Int.ofNat 26586769427996926870471579310893), (Int.negOfNat 1138061452902091253985455896483), (Int.negOfNat 377333670565524604981024623393), (Int.ofNat 21794129820686720932765853127), (Int.ofNat 3177025583840994936011231868), (Int.negOfNat 209136463435818403195165186), (Int.negOfNat 17780097468904423852021126), (Int.ofNat 1294847074146237244901145), (Int.ofNat 71206567561954749292539), (Int.negOfNat 5718590189791467911413), (Int.negOfNat 214442349229877087300), (Int.ofNat 19076468373242104409), (Int.ofNat 425761289648225611), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(11223022754523827217216267522182069/11258999068426240000000000000000000), (3489717532789254909099327477216779/11258999068426240000000000000000000), (-910299679660606995428966428448463/11258999068426240000000000000000000), (-7133673388525131750532523821971/11258999068426240000000000000000000), (26586769427996926870471579310893/11258999068426240000000000000000000), (-1138061452902091253985455896483/11258999068426240000000000000000000), (-377333670565524604981024623393/11258999068426240000000000000000000), (21794129820686720932765853127/11258999068426240000000000000000000), (794256395960248734002807967/2814749767106560000000000000000000), (-104568231717909201597582593/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial137.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial137.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial137.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial137 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 14872491280065893589473577619654182), (Int.ofNat 462658544950282167361069308646132), (Int.negOfNat 477413594399188298338530616456875), (Int.ofNat 116226076728433974770524902684962), (Int.ofNat 1206017033768543650596717520269), (Int.negOfNat 2933586712012169115397611840842), (Int.ofNat 105314553284944934966542943522), (Int.ofNat 33394381379934467085015781888), (Int.negOfNat 1774768734428221661194318577), (Int.negOfNat 227205906866635197206918944), (Int.ofNat 14942747627105079617118754), (Int.ofNat 1040072839969052101767940), (Int.negOfNat 81806907969804315023766), (Int.negOfNat 3427474002839952478887), (Int.ofNat 322502022017351357925), (Int.ofNat 7775202485658178746), (Int.negOfNat 1020241530901758099), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(7436245640032946794736788809827091/5629499534213120000000000000000000), (115664636237570541840267327161533/2814749767106560000000000000000000), (-763861751038701277341648986331/18014398509481984000000000000000), (58113038364216987385262451342481/5629499534213120000000000000000000), (1206017033768543650596717520269/11258999068426240000000000000000000), (-1466793356006084557698805920421/5629499534213120000000000000000000), (52657276642472467483271471761/5629499534213120000000000000000000), (65223401132684506025421449/21990232555520000000000000000000), (-1774768734428221661194318577/11258999068426240000000000000000000), (-7100184589582349912716217/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial137.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial137.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial137.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial137 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 14753845119735069597316654809345306), (Int.negOfNat 215451004512902434738829536616836), (Int.ofNat 57884982521379988978095728265167), (Int.ofNat 39943568370717674900839243930419), (Int.negOfNat 15130896720232147875028954605697), (Int.ofNat 24348705965368912350435587893), (Int.ofNat 281634284295656245021424449598), (Int.negOfNat 10182947945016474884605431492), (Int.negOfNat 2525302186907547074114289358), (Int.ofNat 139181303479860305236579331), (Int.ofNat 13852504967809132223316856), (Int.negOfNat 1007440348360258555835635), (Int.negOfNat 51359196401039792932084), (Int.ofNat 4837733006050225604648), (Int.ofNat 134834424316011056495), (Int.negOfNat 17484731074518361699), (Int.negOfNat 171340151894623561), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(7376922559867534798658327404672653/5629499534213120000000000000000000), (-53862751128225608684707384154209/2814749767106560000000000000000000), (57884982521379988978095728265167/11258999068426240000000000000000000), (39943568370717674900839243930419/11258999068426240000000000000000000), (-15130896720232147875028954605697/11258999068426240000000000000000000), (24348705965368912350435587893/11258999068426240000000000000000000), (140817142147828122510712224799/5629499534213120000000000000000000), (-2545736986254118721151357873/2814749767106560000000000000000000), (-1262651093453773537057144679/5629499534213120000000000000000000), (139181303479860305236579331/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial137.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial137.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial137.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial137 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 14648874311773215007281968527534794), (Int.ofNat 60476117194510982276385769805171), (Int.negOfNat 6653390650476883527072490648079), (Int.negOfNat 44381805453007497061988490725675), (Int.negOfNat 2968761749402307711673144202520), (Int.ofNat 1776237342981401838700463515982), (Int.negOfNat 20495917521776393889817326042), (Int.negOfNat 23306175500575302278927985608), (Int.ofNat 947756770990493589309021777), (Int.ofNat 162672433867227059216366199), (Int.negOfNat 10285571134657619612754599), (Int.negOfNat 707511018529481586545780), (Int.ofNat 63317458097992384378201), (Int.ofNat 2028846556550089737302), (Int.negOfNat 265527865553521361865), (Int.negOfNat 3520554354441728791), (Int.ofNat 957487408457785179), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(7324437155886607503640984263767397/5629499534213120000000000000000000), (60476117194510982276385769805171/11258999068426240000000000000000000), (-6653390650476883527072490648079/11258999068426240000000000000000000), (-1775272218120299882479539629027/450359962737049600000000000000000), (-74219043735057692791828605063/281474976710656000000000000000000), (888118671490700919350231757991/5629499534213120000000000000000000), (-10247958760888196944908663021/5629499534213120000000000000000000), (-2913271937571912784865998201/1407374883553280000000000000000000), (947756770990493589309021777/11258999068426240000000000000000000), (162672433867227059216366199/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial137.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial137.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial137.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial137 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 14393517221905124100898628793352575), (Int.negOfNat 464710580250303891936239532964547), (Int.negOfNat 220362223712140075399828837624547), (Int.negOfNat 11020649902639451392099987624886), (Int.ofNat 8595877185001025369876151062227), (Int.ofNat 228059086374706837581146435347), (Int.negOfNat 172353853639836200300634813108), (Int.ofNat 3382614255221669888825377137), (Int.ofNat 1624199052681200888678004573), (Int.negOfNat 81050447707968429316522696), (Int.negOfNat 8690969727245177693233436), (Int.ofNat 701086608558095954219255), (Int.ofNat 28308403209121246422569), (Int.negOfNat 3660477203335637042688), (Int.negOfNat 51116601141771882010), (Int.ofNat 13514903090371216989), (Int.negOfNat 83080985858978489), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(575740688876204964035945151734103/450359962737049600000000000000000), (-464710580250303891936239532964547/11258999068426240000000000000000000), (-220362223712140075399828837624547/11258999068426240000000000000000000), (-5510324951319725696049993812443/5629499534213120000000000000000000), (8595877185001025369876151062227/11258999068426240000000000000000000), (228059086374706837581146435347/11258999068426240000000000000000000), (-43088463409959050075158703277/2814749767106560000000000000000000), (3382614255221669888825377137/11258999068426240000000000000000000), (1624199052681200888678004573/11258999068426240000000000000000000), (-10131305963496053664565337/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial137.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial137.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial137.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial137 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 12629083140012051992294916596488821), (Int.negOfNat 1215230668762666566424194519933454), (Int.negOfNat 98574124271814336033412650213366), (Int.ofNat 43559439539988803965081298196537), (Int.ofNat 2889715032958993687989488049305), (Int.negOfNat 1039506867925600833865009584916), (Int.negOfNat 15525663921768188786905353748), (Int.ofNat 13371180435135545910493144983), (Int.negOfNat 399478954381430927733250052), (Int.negOfNat 91902059247463959253242674), (Int.ofNat 6209977156139231746754834), (Int.ofNat 354777091769527856865340), (Int.negOfNat 43248358980080404711916), (Int.negOfNat 659689944123165831787), (Int.ofNat 190889911900672966330), (Int.negOfNat 860149792823181524), (Int.negOfNat 809926240095944909), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(12629083140012051992294916596488821/11258999068426240000000000000000000), (-607615334381333283212097259966727/5629499534213120000000000000000000), (-49287062135907168016706325106683/5629499534213120000000000000000000), (43559439539988803965081298196537/11258999068426240000000000000000000), (577943006591798737597897609861/2251799813685248000000000000000000), (-259876716981400208466252396229/2814749767106560000000000000000000), (-3881415980442047196726338437/2814749767106560000000000000000000), (13371180435135545910493144983/11258999068426240000000000000000000), (-99869738595357731933312513/2814749767106560000000000000000000), (-45951029623731979626621337/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial137.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial137.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial137.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial137 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 10166347496740477928931123480128075), (Int.negOfNat 1075080292380389058663996878792480), (Int.ofNat 153173618168836194119246071865901), (Int.ofNat 28996153506056337666048027539874), (Int.negOfNat 5418012146555676766137483970796), (Int.negOfNat 410721766786257721873961142667), (Int.ofNat 88720255866013232543405604098), (Int.ofNat 491776682826007135155612703), (Int.negOfNat 802810179132818269277511468), (Int.ofNat 37964845595293606139498616), (Int.ofNat 3823621751858175848744506), (Int.negOfNat 417293923829026852591080), (Int.negOfNat 7438227104665831113104), (Int.ofNat 2367058656265658036563), (Int.negOfNat 18878219406539719390), (Int.negOfNat 9518847246067887904), (Int.ofNat 210858996065397909), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(406653899869619117157244939205123/450359962737049600000000000000000), (-6719251827377431616649980492453/70368744177664000000000000000000), (153173618168836194119246071865901/11258999068426240000000000000000000), (14498076753028168833024013769937/5629499534213120000000000000000000), (-1354503036638919191534370992699/2814749767106560000000000000000000), (-410721766786257721873961142667/11258999068426240000000000000000000), (44360127933006616271702802049/5629499534213120000000000000000000), (491776682826007135155612703/11258999068426240000000000000000000), (-200702544783204567319377867/2814749767106560000000000000000000), (4745605699411700767437327/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial137.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial137.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial137.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial137 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 8766577333309301478494921612158250), (Int.negOfNat 304131293693193788381408150074214), (Int.ofNat 184652306042742818523877988300467), (Int.negOfNat 17499785355248550276417961595489), (Int.negOfNat 4776745892566457651443914429176), (Int.ofNat 430584910179842688120581002876), (Int.ofNat 37925484533219540942930866078), (Int.negOfNat 5368975241989616835578053943), (Int.ofNat 46431220436072682235647897), (Int.ofNat 32948899249913468766176034), (Int.negOfNat 2919534686072270009273084), (Int.negOfNat 65585740009025160395355), (Int.ofNat 23920151665096845283321), (Int.negOfNat 400137498907353405348), (Int.negOfNat 111332741856478219670), (Int.ofNat 3763256034141226319), (Int.ofNat 598476066630894929), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(35066309333237205913979686448633/45035996273704960000000000000000), (-152065646846596894190704075037107/5629499534213120000000000000000000), (184652306042742818523877988300467/11258999068426240000000000000000000), (-17499785355248550276417961595489/11258999068426240000000000000000000), (-597093236570807206430489303647/1407374883553280000000000000000000), (107646227544960672030145250719/2814749767106560000000000000000000), (18962742266609770471465433039/5629499534213120000000000000000000), (-5368975241989616835578053943/11258999068426240000000000000000000), (46431220436072682235647897/11258999068426240000000000000000000), (16474449624956734383088017/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial137.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial137.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial137.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial137 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 8696042197602644400784960835068336), (Int.ofNat 111056150527802985995582987941152), (Int.ofNat 5153718604256389458030227830454), (Int.negOfNat 35213678542375397288916520802487), (Int.ofNat 446946413669281921995900390550), (Int.ofNat 498633589989288028053912000757), (Int.negOfNat 19424564342847731511149333448), (Int.negOfNat 2509353095794917672137419278), (Int.ofNat 182951486968538756724753033), (Int.negOfNat 7901303149433365597574701), (Int.negOfNat 257285226719611884382111), (Int.ofNat 174667371065959177510440), (Int.negOfNat 6988892568876371137211), (Int.negOfNat 1106560608358398027758), (Int.ofNat 63941951684899612615), (Int.ofNat 4116009655089302579), (Int.negOfNat 232911919539292339), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(543502637350165275049060052191771/703687441776640000000000000000000), (3470504703993843312361968373161/351843720888320000000000000000000), (2576859302128194729015113915227/5629499534213120000000000000000000), (-35213678542375397288916520802487/11258999068426240000000000000000000), (8938928273385638439918007811/225179981368524800000000000000000), (498633589989288028053912000757/11258999068426240000000000000000000), (-2428070542855966438893666681/1407374883553280000000000000000000), (-1254676547897458836068709639/5629499534213120000000000000000000), (182951486968538756724753033/11258999068426240000000000000000000), (-7901303149433365597574701/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial137.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial137.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial137.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial137 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 8678645840755829743356905404887445), (Int.negOfNat 241384286340558237239862660340059), (Int.negOfNat 161566360156929250369933568521462), (Int.negOfNat 15918191596632709296916507664994), (Int.ofNat 3740940917780474154775683512567), (Int.ofNat 122878239525068800663127231464), (Int.negOfNat 38256225382602052654655787998), (Int.negOfNat 310393326365782955823922362), (Int.ofNat 138653309095839687735149978), (Int.ofNat 5359299666144037171583611), (Int.ofNat 462151610046075937639944), (Int.negOfNat 107520190232246013065205), (Int.negOfNat 6967146599565805521116), (Int.ofNat 956676515565499684268), (Int.ofNat 34639911595711001715), (Int.negOfNat 5516055234924671949), (Int.negOfNat 344054928877292879), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(1735729168151165948671381080977489/2251799813685248000000000000000000), (-241384286340558237239862660340059/11258999068426240000000000000000000), (-80783180078464625184966784260731/5629499534213120000000000000000000), (-7959095798316354648458253832497/5629499534213120000000000000000000), (3740940917780474154775683512567/11258999068426240000000000000000000), (15359779940633600082890903933/1407374883553280000000000000000000), (-19128112691301026327327893999/5629499534213120000000000000000000), (-155196663182891477911961181/5629499534213120000000000000000000), (69326654547919843867574989/5629499534213120000000000000000000), (5359299666144037171583611/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial137.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial137.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial137.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial137 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 7483603796211495677691556472525209), (Int.negOfNat 956456542676902285815001745510664), (Int.negOfNat 166577597766645921560193106311240), (Int.ofNat 12908996184289728482498718345450), (Int.ofNat 2765498424895729744084948556385), (Int.negOfNat 289172108989885881017233555832), (Int.negOfNat 23696240254183920819779019292), (Int.ofNat 2490989562981654453582462778), (Int.ofNat 163012034835609862618034047), (Int.negOfNat 9801117920054963832008234), (Int.negOfNat 1491547222464856449738254), (Int.ofNat 14123511876373043232220), (Int.ofNat 12638510913271361171446), (Int.ofNat 7515056238052222703), (Int.negOfNat 74325008072192051295), (Int.ofNat 449274989152451866), (Int.ofNat 170157797095319419), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(7483603796211495677691556472525209/11258999068426240000000000000000000), (-119557067834612785726875218188833/1407374883553280000000000000000000), (-4164439944166148039004827657781/281474976710656000000000000000000), (258179923685794569649974366909/225179981368524800000000000000000), (553099684979145948816989711277/2251799813685248000000000000000000), (-36146513623735735127154194479/1407374883553280000000000000000000), (-5924060063545980204944754823/2814749767106560000000000000000000), (1245494781490827226791231389/5629499534213120000000000000000000), (163012034835609862618034047/11258999068426240000000000000000000), (-4900558960027481916004117/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial137.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial137.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial137.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial137 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 5041484308971846387564324176281696), (Int.negOfNat 1405793345981088484170692119060368), (Int.negOfNat 49667582701808299032280100398982), (Int.ofNat 21288139541263435326487897726791), (Int.negOfNat 725384474420857714085374825062), (Int.negOfNat 321413853038282862759399263214), (Int.ofNat 18739995457616166230135743673), (Int.ofNat 2620667863371718955765297167), (Int.negOfNat 176164793397627904335542408), (Int.negOfNat 18529560706766305417808656), (Int.ofNat 1131006704833704610796046), (Int.ofNat 143044832691589968841475), (Int.negOfNat 6265617451035405555809), (Int.negOfNat 935423010058680851803), (Int.ofNat 30445027399228482180), (Int.ofNat 4458979844024519979), (Int.ofNat 89633791123690829), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(157546384655370199611385130508803/351843720888320000000000000000000), (-87862084123818030260668257441273/703687441776640000000000000000000), (-24833791350904149516140050199491/5629499534213120000000000000000000), (21288139541263435326487897726791/11258999068426240000000000000000000), (-362692237210428857042687412531/5629499534213120000000000000000000), (-160706926519141431379699631607/5629499534213120000000000000000000), (18739995457616166230135743673/11258999068426240000000000000000000), (2620667863371718955765297167/11258999068426240000000000000000000), (-22020599174703488041942801/1407374883553280000000000000000000), (-1158097544172894088613041/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial137.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial137.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial137.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial137 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 2181122645932629574120107259711637), (Int.negOfNat 1393375157511880009282133499466944), (Int.ofNat 40813034477568178174258246737346), (Int.ofNat 6701645822564647327632146522748), (Int.negOfNat 2333202870351165299004553982466), (Int.ofNat 19775012116275868204241595082), (Int.ofNat 28619596514309243907891988607), (Int.negOfNat 1266907310356452132342029558), (Int.negOfNat 196460288104313541525721552), (Int.ofNat 16959093376410892323906809), (Int.ofNat 1307293080901636684950469), (Int.negOfNat 139742750394630940571060), (Int.negOfNat 9156633186911342206506), (Int.ofNat 819389440396957514772), (Int.ofNat 51925683417329174870), (Int.negOfNat 4301360023367383731), (Int.negOfNat 107403674651346499), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(2181122645932629574120107259711637/11258999068426240000000000000000000), (-21771486836123125145033335929171/175921860444160000000000000000000), (20406517238784089087129123368673/5629499534213120000000000000000000), (1675411455641161831908036630687/2814749767106560000000000000000000), (-1166601435175582649502276991233/5629499534213120000000000000000000), (9887506058137934102120797541/5629499534213120000000000000000000), (28619596514309243907891988607/11258999068426240000000000000000000), (-633453655178226066171014779/5629499534213120000000000000000000), (-12278768006519596345357597/703687441776640000000000000000000), (16959093376410892323906809/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial137.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial137.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial137.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial137 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 423831908468398911520830939833062), (Int.negOfNat 1218013531269472639986334797535065), (Int.ofNat 32362126475463877534616463689611), (Int.negOfNat 7550776944561963505543495166739), (Int.negOfNat 913818611319506744278429443902), (Int.ofNat 208757757758532051812403546704), (Int.ofNat 2270242817690584562037891112), (Int.negOfNat 1577140569639616242802180437), (Int.ofNat 127380793762479619446772593), (Int.ofNat 7573371072236418521699151), (Int.negOfNat 1896544561969612056386821), (Int.negOfNat 49428637975835541263660), (Int.ofNat 14659798563840088313104), (Int.ofNat 376788239762618454988), (Int.negOfNat 74673669723411373185), (Int.negOfNat 2230111575095895934), (Int.ofNat 143869305815253581), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-211915954234199455760415469916531/5629499534213120000000000000000000), (-243602706253894527997266959507013/2251799813685248000000000000000000), (32362126475463877534616463689611/11258999068426240000000000000000000), (-7550776944561963505543495166739/11258999068426240000000000000000000), (-456909305659753372139214721951/5629499534213120000000000000000000), (13047359859908253238275221669/703687441776640000000000000000000), (283780352211323070254736389/1407374883553280000000000000000000), (-1577140569639616242802180437/11258999068426240000000000000000000), (127380793762479619446772593/11258999068426240000000000000000000), (7573371072236418521699151/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial137.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial137.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial137.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial137 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 2798779603053178015633978003014208), (Int.negOfNat 1191848604840505532256075522897903), (Int.negOfNat 18447595701888253664896311991111), (Int.negOfNat 6791511039147785703311132610460), (Int.ofNat 1015913011829733282390561315491), (Int.ofNat 160628622437497041204315767168), (Int.negOfNat 6668651534672380286191870492), (Int.negOfNat 152341131162058086029184817), (Int.negOfNat 26645054169835329058040373), (Int.negOfNat 16216363495070966698701349), (Int.ofNat 486379980945525686593401), (Int.ofNat 195779316803570507171240), (Int.negOfNat 1924722972600521401144), (Int.negOfNat 1281295066006561894552), (Int.negOfNat 1011687407325587495), (Int.ofNat 6315153866688002266), (Int.negOfNat 104046498813703481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-43730931297705906494280906297097/175921860444160000000000000000000), (-1191848604840505532256075522897903/11258999068426240000000000000000000), (-18447595701888253664896311991111/11258999068426240000000000000000000), (-339575551957389285165556630523/562949953421312000000000000000000), (1015913011829733282390561315491/11258999068426240000000000000000000), (1254911112792945634408716931/87960930222080000000000000000000), (-1667162883668095071547967623/2814749767106560000000000000000000), (-152341131162058086029184817/11258999068426240000000000000000000), (-26645054169835329058040373/11258999068426240000000000000000000), (-16216363495070966698701349/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial137.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial137.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial137.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial137 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 5289665096225164684638970731968433), (Int.negOfNat 1303186309636988091171123394214122), (Int.negOfNat 23778996443878983682034072823466), (Int.ofNat 6488873814645156291424765513682), (Int.ofNat 2098306268562485672769571844207), (Int.ofNat 32289019596538890124273456366), (Int.negOfNat 18536006961497274877202048067), (Int.negOfNat 1593862232260788162598217438), (Int.negOfNat 36170199802061093129504708), (Int.ofNat 20242757146732826388022449), (Int.ofNat 1860046783751715900300131), (Int.negOfNat 137629938066768513495100), (Int.negOfNat 17317121908248175803314), (Int.ofNat 579700685134850950632), (Int.ofNat 95186549139028871550), (Int.negOfNat 979428236844778951), (Int.negOfNat 271647316021673001), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-5289665096225164684638970731968433/11258999068426240000000000000000000), (-651593154818494045585561697107061/5629499534213120000000000000000000), (-11889498221939491841017036411733/5629499534213120000000000000000000), (3244436907322578145712382756841/5629499534213120000000000000000000), (2098306268562485672769571844207/11258999068426240000000000000000000), (16144509798269445062136728183/5629499534213120000000000000000000), (-18536006961497274877202048067/11258999068426240000000000000000000), (-796931116130394081299108719/5629499534213120000000000000000000), (-9042549950515273282376177/2814749767106560000000000000000000), (20242757146732826388022449/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial137.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial137.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial137.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial137 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 7906024217805952694037450690953197), (Int.negOfNat 1254962661304874857475377624285195), (Int.ofNat 62621970611511850094240437916217), (Int.ofNat 20773611005358912653325149829447), (Int.ofNat 921156357571462467739260552328), (Int.negOfNat 289967598426872197689347335012), (Int.negOfNat 27913604842415522532243978613), (Int.ofNat 1463215979800397444934325687), (Int.ofNat 383894544413729671878470828), (Int.ofNat 8408289413905021908425504), (Int.negOfNat 3211825961263069449110986), (Int.negOfNat 174913809052767126251785), (Int.ofNat 17669680570387677018929), (Int.ofNat 1307868519336367746397), (Int.negOfNat 68300571890798362440), (Int.negOfNat 6470569081750981361), (Int.ofNat 379385677381963171), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-7906024217805952694037450690953197/11258999068426240000000000000000000), (-250992532260974971495075524857039/2251799813685248000000000000000000), (62621970611511850094240437916217/11258999068426240000000000000000000), (20773611005358912653325149829447/11258999068426240000000000000000000), (115144544696432808467407569041/1407374883553280000000000000000000), (-72491899606718049422336833753/2814749767106560000000000000000000), (-27913604842415522532243978613/11258999068426240000000000000000000), (1463215979800397444934325687/11258999068426240000000000000000000), (95973636103432417969617707/2814749767106560000000000000000000), (262759044184531934638297/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial137.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial137.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial137.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial137 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 9995313393726516679907150636678208), (Int.negOfNat 753221182013171623101620181876936), (Int.ofNat 181144128743355321273836824123285), (Int.ofNat 13576114158764282924099895063300), (Int.negOfNat 2827694038838380779715776219561), (Int.negOfNat 342021224462433228841752643256), (Int.ofNat 29106463456108717146015238242), (Int.ofNat 5362365117501209376878592418), (Int.negOfNat 97230964833415735420615727), (Int.negOfNat 54176147035752708338180314), (Int.negOfNat 938342899978850949225006), (Int.ofNat 365835220860766559898920), (Int.ofNat 13473824988629142092294), (Int.negOfNat 1723670954410270781397), (Int.negOfNat 84672866623039954865), (Int.ofNat 5482823092518647006), (Int.ofNat 208893193577700081), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-156176771776976823123549228698097/175921860444160000000000000000000), (-94152647751646452887702522734617/1407374883553280000000000000000000), (36228825748671064254767364824657/2251799813685248000000000000000000), (135761141587642829240998950633/112589990684262400000000000000000), (-2827694038838380779715776219561/11258999068426240000000000000000000), (-42752653057804153605219080407/1407374883553280000000000000000000), (14553231728054358573007619121/5629499534213120000000000000000000), (2681182558750604688439296209/5629499534213120000000000000000000), (-97230964833415735420615727/11258999068426240000000000000000000), (-27088073517876354169090157/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial137.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial137.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial137.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial137 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 10722261717963732229413461109630609), (Int.ofNat 24186737608440525018731929799008), (Int.ofNat 177539739512619548349934935377067), (Int.negOfNat 15529815101958585265632891945164), (Int.negOfNat 3323543037778281983737783336083), (Int.ofNat 308898859370174884797237328542), (Int.ofNat 59509743292077425355265306228), (Int.negOfNat 2837457409828804397103497642), (Int.negOfNat 733152500608216954176799698), (Int.ofNat 8398850199192967927797971), (Int.ofNat 6065554519034596944555916), (Int.ofNat 66833421688565835094455), (Int.negOfNat 34560196185317053856764), (Int.negOfNat 854313150407706923012), (Int.ofNat 140894498309878210845), (Int.ofNat 5004056484925173731), (Int.negOfNat 633806815135565221), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-10722261717963732229413461109630609/11258999068426240000000000000000000), (755835550263766406835372806219/351843720888320000000000000000000), (177539739512619548349934935377067/11258999068426240000000000000000000), (-3882453775489646316408222986291/2814749767106560000000000000000000), (-3323543037778281983737783336083/11258999068426240000000000000000000), (154449429685087442398618664271/5629499534213120000000000000000000), (14877435823019356338816326557/2814749767106560000000000000000000), (-1418728704914402198551748821/5629499534213120000000000000000000), (-366576250304108477088399849/5629499534213120000000000000000000), (8398850199192967927797971/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial137.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial137.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial137.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial137 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 10127991486536596290727974651237262), (Int.ofNat 475800669297502920250154804411954), (Int.ofNat 40477525235670976901757556262620), (Int.negOfNat 23006320386551905923157276801032), (Int.ofNat 1834081915603456877362885494981), (Int.ofNat 520408040491780083872716925406), (Int.negOfNat 37429880519145566599245223592), (Int.negOfNat 8085265894804564669235818338), (Int.ofNat 318632304461844033219840607), (Int.ofNat 83678442434720261219509359), (Int.negOfNat 1073839766857566210542929), (Int.negOfNat 583057797299073911514220), (Int.negOfNat 2600649161416192111229), (Int.ofNat 2841288804088402227282), (Int.ofNat 44072517236213659805), (Int.negOfNat 9612246521837161881), (Int.negOfNat 146139071133727161), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-5063995743268298145363987325618631/5629499534213120000000000000000000), (237900334648751460125077402205977/5629499534213120000000000000000000), (2023876261783548845087877813131/562949953421312000000000000000000), (-2875790048318988240394659600129/1407374883553280000000000000000000), (1834081915603456877362885494981/11258999068426240000000000000000000), (260204020245890041936358462703/5629499534213120000000000000000000), (-4678735064893195824905652949/1407374883553280000000000000000000), (-4042632947402282334617909169/5629499534213120000000000000000000), (318632304461844033219840607/11258999068426240000000000000000000), (83678442434720261219509359/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial137.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial137.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial137.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial137 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 9155840536015291992195798237814651), (Int.ofNat 451656552787462159607065356928314), (Int.negOfNat 25398182617695353097942443534657), (Int.ofNat 2946400914146178290216318209766), (Int.ofNat 3184420021535273541934331241232), (Int.negOfNat 321684183333908921466440600852), (Int.negOfNat 70456016520075980108927725578), (Int.ofNat 5201040666564962766692844037), (Int.ofNat 958015992038384696922945643), (Int.negOfNat 38737404839696477834974666), (Int.negOfNat 8403434453656710016667396), (Int.ofNat 138639599207156167204425), (Int.ofNat 49559482051385606419819), (Int.negOfNat 74715952145105434048), (Int.negOfNat 207570930366610156330), (Int.negOfNat 1758014349473399301), (Int.ofNat 888227952889167271), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-9155840536015291992195798237814651/11258999068426240000000000000000000), (225828276393731079803532678464157/5629499534213120000000000000000000), (-25398182617695353097942443534657/11258999068426240000000000000000000), (1473200457073089145108159104883/5629499534213120000000000000000000), (199026251345954596370895702577/703687441776640000000000000000000), (-80421045833477230366610150213/2814749767106560000000000000000000), (-35228008260037990054463862789/5629499534213120000000000000000000), (5201040666564962766692844037/11258999068426240000000000000000000), (958015992038384696922945643/11258999068426240000000000000000000), (-19368702419848238917487333/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial137.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial137.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial137.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial137 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 8293518282625900294918949653355989), (Int.ofNat 451241334014612850311743742074898), (Int.ofNat 31005843514323962583586484824014), (Int.ofNat 8584711672737439940352119413010), (Int.negOfNat 1987748039256163949718408030585), (Int.negOfNat 438050570660095794872875887271), (Int.ofNat 60194996443346268402404098492), (Int.ofNat 8773673109274598355013901403), (Int.negOfNat 718502903030819164435612772), (Int.negOfNat 102794858423447115510531264), (Int.ofNat 4413148089955975211170234), (Int.ofNat 755483027755264199841400), (Int.negOfNat 15185157832665647208716), (Int.negOfNat 3770073135269707726977), (Int.ofNat 24713756230489405930), (Int.ofNat 13742501265306202036), (Int.negOfNat 1422097228113109), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-8293518282625900294918949653355989/11258999068426240000000000000000000), (225620667007306425155871871037449/5629499534213120000000000000000000), (15502921757161981291793242412007/5629499534213120000000000000000000), (858471167273743994035211941301/1125899906842624000000000000000000), (-397549607851232789943681606117/2251799813685248000000000000000000), (-438050570660095794872875887271/11258999068426240000000000000000000), (15048749110836567100601024623/2814749767106560000000000000000000), (8773673109274598355013901403/11258999068426240000000000000000000), (-179625725757704791108903193/2814749767106560000000000000000000), (-1606169662866361179852051/175921860444160000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial137.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial137.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial137.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial137 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 7239411217776281554047369920577225), (Int.ofNat 594175261028478045122630922014629), (Int.ofNat 18416092558319062309811234928811), (Int.negOfNat 12038095169194072869750612390089), (Int.negOfNat 1431135060032562249225445313967), (Int.ofNat 547364730205180697117419499487), (Int.ofNat 57800197015167567392139621408), (Int.negOfNat 10065475325969218940209930877), (Int.negOfNat 1037146844976864780646748988), (Int.ofNat 87576059107105934639876926), (Int.ofNat 10026773137284498807789746), (Int.negOfNat 440788969301053749675260), (Int.negOfNat 61008395875930144934864), (Int.ofNat 1404680734531038121993), (Int.ofNat 257625255797960847250), (Int.negOfNat 2238041494829929784), (Int.negOfNat 1016005963095586691), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-289576448711051262161894796823089/450359962737049600000000000000000), (594175261028478045122630922014629/11258999068426240000000000000000000), (18416092558319062309811234928811/11258999068426240000000000000000000), (-12038095169194072869750612390089/11258999068426240000000000000000000), (-1431135060032562249225445313967/11258999068426240000000000000000000), (547364730205180697117419499487/11258999068426240000000000000000000), (1806256156723986481004363169/351843720888320000000000000000000), (-10065475325969218940209930877/11258999068426240000000000000000000), (-259286711244216195161687247/2814749767106560000000000000000000), (43788029553552967319938463/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial137.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial137.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial137.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial137 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 6076884284922139943059272333019960), (Int.ofNat 527148363537045358684945094214355), (Int.negOfNat 38618220827414141202013388645923), (Int.ofNat 760136270320044333459398197723), (Int.ofNat 3992868593214076082062000175810), (Int.ofNat 169728650996979560640931933201), (Int.negOfNat 116366671698063764457821441472), (Int.negOfNat 8038154112170495734580214603), (Int.ofNat 1381649594372739222986802767), (Int.ofNat 114357676482737061965914484), (Int.negOfNat 9084184940764094133764964), (Int.negOfNat 879706101142477565851525), (Int.ofNat 38394517763892873672011), (Int.ofNat 4426313037486086243692), (Int.negOfNat 111753173757722781270), (Int.negOfNat 16645607506624246831), (Int.ofNat 212872270693163089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-151922107123053498576481808325499/281474976710656000000000000000000), (105429672707409071736989018842871/2251799813685248000000000000000000), (-38618220827414141202013388645923/11258999068426240000000000000000000), (760136270320044333459398197723/11258999068426240000000000000000000), (399286859321407608206200017581/1125899906842624000000000000000000), (169728650996979560640931933201/11258999068426240000000000000000000), (-1818229245282246319653460023/175921860444160000000000000000000), (-8038154112170495734580214603/11258999068426240000000000000000000), (1381649594372739222986802767/11258999068426240000000000000000000), (28589419120684265491478621/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial137.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial137.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial137.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial137 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 5109737146636828074071089728948870), (Int.ofNat 498826740302811903513037749883473), (Int.ofNat 44896794931426324712758311892864), (Int.ofNat 19291716901619262330116393732611), (Int.negOfNat 1686913106890791357913342416584), (Int.negOfNat 1146429451411851852762480307862), (Int.negOfNat 37718235141919508371111364958), (Int.ofNat 18555529765676280221508009892), (Int.ofNat 1096525061704285943629571903), (Int.negOfNat 154401638442108525593491141), (Int.negOfNat 11296046103278254108178281), (Int.ofNat 809641397346860110951640), (Int.ofNat 68808463377691208009039), (Int.negOfNat 2960615954450709728538), (Int.negOfNat 288697518062026137475), (Int.ofNat 8239440232605950309), (Int.ofNat 1038058886569481121), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-510973714663682807407108972894887/1125899906842624000000000000000000), (498826740302811903513037749883473/11258999068426240000000000000000000), (350756210401768161818424311663/87960930222080000000000000000000), (19291716901619262330116393732611/11258999068426240000000000000000000), (-210864138361348919739167802073/1407374883553280000000000000000000), (-573214725705925926381240153931/5629499534213120000000000000000000), (-18859117570959754185555682479/5629499534213120000000000000000000), (4638882441419070055377002473/2814749767106560000000000000000000), (1096525061704285943629571903/11258999068426240000000000000000000), (-154401638442108525593491141/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial137.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial137.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial137.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial137 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 3841685961540905914561561719854145), (Int.ofNat 766009810517235974335364793160787), (Int.ofNat 33014002729756825996897512322993), (Int.negOfNat 34702298347420424051941771487401), (Int.negOfNat 9723444298422779591117553446554), (Int.ofNat 78169894133665171912014709824), (Int.ofNat 218351048199513743194108973972), (Int.ofNat 8606601061730132253130693308), (Int.negOfNat 2270493934434721368383853442), (Int.negOfNat 129743335593813121606434349), (Int.ofNat 14449545417931991292955924), (Int.ofNat 976148616551289665419625), (Int.negOfNat 63440506239040250297636), (Int.negOfNat 4787041640733622587512), (Int.ofNat 205589673608254296705), (Int.ofNat 17549396156814387101), (Int.negOfNat 467293408446765139), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-768337192308181182912312343970829/2251799813685248000000000000000000), (766009810517235974335364793160787/11258999068426240000000000000000000), (33014002729756825996897512322993/11258999068426240000000000000000000), (-34702298347420424051941771487401/11258999068426240000000000000000000), (-4861722149211389795558776723277/5629499534213120000000000000000000), (1221404595838518311125229841/175921860444160000000000000000000), (54587762049878435798527243493/2814749767106560000000000000000000), (2151650265432533063282673327/2814749767106560000000000000000000), (-1135246967217360684191926721/5629499534213120000000000000000000), (-129743335593813121606434349/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial137.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial137.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial137.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial137 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 2593857451250499020613886549364106), (Int.ofNat 219980049715745885457393354970915), (Int.negOfNat 348598569185725833691612458598885), (Int.negOfNat 74118606438342406395603436350823), (Int.ofNat 3728983663464474323344404678864), (Int.ofNat 2280225673318880029260876484952), (Int.ofNat 55735675282558631871809858438), (Int.negOfNat 29397807589471463003336451192), (Int.negOfNat 1364722388533162062663728183), (Int.ofNat 225196546744455101843313976), (Int.ofNat 12788927218554768955538186), (Int.negOfNat 1172344910257293414736840), (Int.negOfNat 73527625483933811570414), (Int.ofNat 4469346151154648725653), (Int.ofNat 297090981519016698715), (Int.negOfNat 12929949578745639834), (Int.negOfNat 975304764125508201), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-1296928725625249510306943274682053/5629499534213120000000000000000000), (43996009943149177091478670994183/2251799813685248000000000000000000), (-69719713837145166738322491719777/2251799813685248000000000000000000), (-74118606438342406395603436350823/11258999068426240000000000000000000), (233061478966529645209025292429/703687441776640000000000000000000), (285028209164860003657609560619/1407374883553280000000000000000000), (27867837641279315935904929219/5629499534213120000000000000000000), (-3674725948683932875417056399/1407374883553280000000000000000000), (-1364722388533162062663728183/11258999068426240000000000000000000), (28149568343056887730414247/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial137.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial137.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial137.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial137 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 4009028989631956933626393776230979), (Int.negOfNat 1765388828801301997497348164640589), (Int.negOfNat 529073029715205801861239392317857), (Int.ofNat 38282437973106859706463899071929), (Int.ofNat 21138442261873393539773425919524), (Int.ofNat 384980364265483517178748411025), (Int.negOfNat 334889627233925298499325361327), (Int.negOfNat 13985900974466274865479176313), (Int.ofNat 3088865516066263786799367512), (Int.ofNat 158533714856297456054153454), (Int.negOfNat 19054676046712410676599654), (Int.negOfNat 1058310635689030207664235), (Int.ofNat 84928629266149806541981), (Int.ofNat 4853921435001959429107), (Int.negOfNat 287396531423199046640), (Int.negOfNat 16965657210813735251), (Int.ofNat 721714546200367189), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-4009028989631956933626393776230979/11258999068426240000000000000000000), (-1765388828801301997497348164640589/11258999068426240000000000000000000), (-529073029715205801861239392317857/11258999068426240000000000000000000), (38282437973106859706463899071929/11258999068426240000000000000000000), (5284610565468348384943356479881/2814749767106560000000000000000000), (15399214570619340687149936441/450359962737049600000000000000000), (-334889627233925298499325361327/11258999068426240000000000000000000), (-13985900974466274865479176313/11258999068426240000000000000000000), (386108189508282973349920939/1407374883553280000000000000000000), (79266857428148728027076727/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial137.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial137.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial137.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial137 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 9021677324075685149908469994176548), (Int.negOfNat 2782206514264847243134012315065713), (Int.ofNat 154993459435136102222329796609131), (Int.ofNat 167435633665394998469210775221235), (Int.ofNat 4788959833767417583626841923330), (Int.negOfNat 3280173123702176346758081884827), (Int.negOfNat 152042218867335176650925119533), (Int.ofNat 36921563605929607122265940212), (Int.ofNat 1922277451612161019300596088), (Int.negOfNat 272762548012805263812481571), (Int.negOfNat 14526267028855840836465541), (Int.ofNat 1429508152020392802439460), (Int.ofNat 74850343715249924656214), (Int.negOfNat 5610974750495653484188), (Int.negOfNat 282854681258470926530), (Int.ofNat 16907259314858506779), (Int.ofNat 912550641681535281), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-2255419331018921287477117498544137/2814749767106560000000000000000000), (-2782206514264847243134012315065713/11258999068426240000000000000000000), (154993459435136102222329796609131/11258999068426240000000000000000000), (33487126733078999693842155044247/2251799813685248000000000000000000), (478895983376741758362684192333/1125899906842624000000000000000000), (-3280173123702176346758081884827/11258999068426240000000000000000000), (-152042218867335176650925119533/11258999068426240000000000000000000), (9230390901482401780566485053/2814749767106560000000000000000000), (240284681451520127412574511/1407374883553280000000000000000000), (-272762548012805263812481571/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial137.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial137.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial137.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial137 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 12659637612087945547382431815300016), (Int.negOfNat 273540245667605077777970615695099), (Int.ofNat 1002514422646070245808358998140206), (Int.ofNat 72711929061533458946230425007154), (Int.negOfNat 25871750814377491521709864408783), (Int.negOfNat 1761341041667791476640604938445), (Int.ofNat 372209951502442045322751230142), (Int.ofNat 23191477581015845417680312583), (Int.negOfNat 3391601983879421784672191137), (Int.negOfNat 192969254396632784331700489), (Int.ofNat 21263909012913493770935769), (Int.ofNat 1102037672236217024164960), (Int.negOfNat 97556698518038793682936), (Int.negOfNat 4591860494919146455952), (Int.ofNat 341972356090289664405), (Int.ofNat 14611564239987176126), (Int.negOfNat 955217643139311599), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-791227350755496596711401988456251/703687441776640000000000000000000), (-273540245667605077777970615695099/11258999068426240000000000000000000), (501257211323035122904179499070103/5629499534213120000000000000000000), (36355964530766729473115212503577/5629499534213120000000000000000000), (-25871750814377491521709864408783/11258999068426240000000000000000000), (-352268208333558295328120987689/2251799813685248000000000000000000), (186104975751221022661375615071/5629499534213120000000000000000000), (23191477581015845417680312583/11258999068426240000000000000000000), (-3391601983879421784672191137/11258999068426240000000000000000000), (-192969254396632784331700489/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial137.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial137.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial137.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial137.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial137 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial137 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial137 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 15240079624881605643307953970841542), (Int.ofNat 19187154931951888901370351456997), (Int.ofNat 1105770359672449531784358434868236), (Int.negOfNat 101530036895194757859030769010543), (Int.negOfNat 27361197838230639241052143188917), (Int.ofNat 2548441036963388383321229649512), (Int.ofNat 386222097448890876858856126702), (Int.negOfNat 31762981384245412592001376703), (Int.negOfNat 3484231124610587967675825337), (Int.ofNat 246211418925444430049879649), (Int.ofNat 21707379809948600468013209), (Int.negOfNat 1320262704735222747395480), (Int.negOfNat 99123624606329113824696), (Int.ofNat 5232505101065129723872), (Int.ofNat 345729097147227716805), (Int.negOfNat 15738586557068591846), (Int.negOfNat 955217643139311599), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-7620039812440802821653976985420771/5629499534213120000000000000000000), (19187154931951888901370351456997/11258999068426240000000000000000000), (276442589918112382946089608717059/2814749767106560000000000000000000), (-101530036895194757859030769010543/11258999068426240000000000000000000), (-27361197838230639241052143188917/11258999068426240000000000000000000), (318555129620423547915153706189/1407374883553280000000000000000000), (193111048724445438429428063351/5629499534213120000000000000000000), (-31762981384245412592001376703/11258999068426240000000000000000000), (-3484231124610587967675825337/11258999068426240000000000000000000), (246211418925444430049879649/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial137.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial137.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial137.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 11927187407601303532710204336162763), (Int.ofNat 2609243496809466199630418364304895), (Int.ofNat 110243194014056393486564257078981), (Int.negOfNat 179125572346633315305891174079300), (Int.ofNat 9718927372378434993028526787079), (Int.ofNat 3578427092705992130620959605013), (Int.negOfNat 234315164438744439668349370373), (Int.negOfNat 40004501605280644140721200252), (Int.ofNat 2593424643104598385497640928), (Int.ofNat 291261109300307403027385051), (Int.negOfNat 17897845748034095800966141), (Int.negOfNat 1503421541321585916836540), (Int.ofNat 86524341191832211047414), (Int.ofNat 5824253264670193576548), (Int.negOfNat 312898410741977788170), (Int.negOfNat 17282933420552312019), (Int.ofNat 912550641681535281), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-11927187407601303532710204336162763/11258999068426240000000000000000000), (521848699361893239926083672860979/2251799813685248000000000000000000), (110243194014056393486564257078981/11258999068426240000000000000000000), (-1791255723466333153058911740793/112589990684262400000000000000000), (9718927372378434993028526787079/11258999068426240000000000000000000), (3578427092705992130620959605013/11258999068426240000000000000000000), (-234315164438744439668349370373/11258999068426240000000000000000000), (-10001125401320161035180300063/2814749767106560000000000000000000), (81044520097018699546801279/351843720888320000000000000000000), (291261109300307403027385051/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial137.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial137.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial137.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 7450044426028804771195045416563949), (Int.ofNat 1438299277537593136444045206834301), (Int.negOfNat 522352803390584221309177507841317), (Int.negOfNat 12244005306104064117107299282729), (Int.ofNat 24030710775822206164685648428047), (Int.negOfNat 1023153315010341609504720936817), (Int.negOfNat 384431979370004159580663911067), (Int.ofNat 20983849399080514395577532353), (Int.ofNat 3483843117169019300507012312), (Int.negOfNat 202717500121765370745926294), (Int.negOfNat 20974651390410793410480574), (Int.ofNat 1242459294428403691206155), (Int.ofNat 91346049127189852934381), (Int.negOfNat 5404962861081321331987), (Int.negOfNat 303274894341110269960), (Int.ofNat 17842230124099280811), (Int.ofNat 721714546200367189), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-7450044426028804771195045416563949/11258999068426240000000000000000000), (1438299277537593136444045206834301/11258999068426240000000000000000000), (-522352803390584221309177507841317/11258999068426240000000000000000000), (-12244005306104064117107299282729/11258999068426240000000000000000000), (24030710775822206164685648428047/11258999068426240000000000000000000), (-1023153315010341609504720936817/11258999068426240000000000000000000), (-384431979370004159580663911067/11258999068426240000000000000000000), (20983849399080514395577532353/11258999068426240000000000000000000), (435480389646127412563376539/1407374883553280000000000000000000), (-101358750060882685372963147/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial137.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial137.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial137.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 6430206910062740147635171086714522), (Int.negOfNat 172310769452200027345011535960072), (Int.negOfNat 173987072124922680334662133841525), (Int.ofNat 94209451943680090364705238466738), (Int.negOfNat 526793594960113414196533638089), (Int.negOfNat 2846784210202681034246530643018), (Int.ofNat 115231898550743535865293368678), (Int.ofNat 35579558743508527798277845872), (Int.negOfNat 1841334814958380434512770503), (Int.negOfNat 262848456485406368711548496), (Int.ofNat 15231851429638572894830906), (Int.ofNat 1322316386578108688470280), (Int.negOfNat 82241506867606532908774), (Int.negOfNat 4896935872021908014133), (Int.ofNat 320189839533186942195), (Int.ofNat 13430848386337380154), (Int.negOfNat 975304764125508201), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-3215103455031370073817585543357261/5629499534213120000000000000000000), (-21538846181525003418126441995009/1407374883553280000000000000000000), (-6959482884996907213386485353661/450359962737049600000000000000000), (47104725971840045182352619233369/5629499534213120000000000000000000), (-526793594960113414196533638089/11258999068426240000000000000000000), (-1423392105101340517123265321509/5629499534213120000000000000000000), (57615949275371767932646684339/5629499534213120000000000000000000), (2223722421469282987392365367/703687441776640000000000000000000), (-1841334814958380434512770503/11258999068426240000000000000000000), (-16428028530337898044471781/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial137.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial137.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial137.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 6805285915078405374886843206650286), (Int.ofNat 53317910024712792946293765249936), (Int.ofNat 198144594186171370598639651248073), (Int.ofNat 10052024358360502869409493439161), (Int.negOfNat 14991829102886607841398860460763), (Int.ofNat 322200366423467913431581582507), (Int.ofNat 295544825439638118147934464202), (Int.negOfNat 12591990026356898858738823028), (Int.negOfNat 2868779489890481072603710202), (Int.ofNat 155404898423290972036319149), (Int.ofNat 17342488542386967975876964), (Int.negOfNat 1089116064506456264030185), (Int.negOfNat 73119895594391970180636), (Int.ofNat 5146662353558076121432), (Int.ofNat 229720279739865969385), (Int.negOfNat 18425969070099932661), (Int.negOfNat 467293408446765139), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-3402642957539202687443421603325143/5629499534213120000000000000000000), (3332369376544549559143360328121/703687441776640000000000000000000), (198144594186171370598639651248073/11258999068426240000000000000000000), (10052024358360502869409493439161/11258999068426240000000000000000000), (-14991829102886607841398860460763/11258999068426240000000000000000000), (322200366423467913431581582507/11258999068426240000000000000000000), (147772412719819059073967232101/5629499534213120000000000000000000), (-3147997506589224714684705757/2814749767106560000000000000000000), (-1434389744945240536301855101/5629499534213120000000000000000000), (155404898423290972036319149/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial137.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial137.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial137.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 6038550849480344966133696735233334), (Int.ofNat 561156919158925409979403371119349), (Int.negOfNat 17361869547094694099964688072381), (Int.negOfNat 60850549237569018050199876201325), (Int.ofNat 30545531868925837514958380540), (Int.ofNat 1941200684536788441952184485878), (Int.negOfNat 58511117037368847031359493598), (Int.negOfNat 26434625000097427786229787172), (Int.ofNat 1273601821828681118403162703), (Int.ofNat 201331634898247077139690901), (Int.negOfNat 12342236857378527641866721), (Int.negOfNat 997031566729272885719640), (Int.ofNat 73099600684292889033439), (Int.ofNat 3500408650615348849458), (Int.negOfNat 301427900041794301155), (Int.negOfNat 9116013145891495869), (Int.ofNat 1038058886569481121), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-3019275424740172483066848367616667/5629499534213120000000000000000000), (561156919158925409979403371119349/11258999068426240000000000000000000), (-17361869547094694099964688072381/11258999068426240000000000000000000), (-2434021969502760722007995048053/450359962737049600000000000000000), (1527276593446291875747919027/562949953421312000000000000000000), (970600342268394220976092242939/5629499534213120000000000000000000), (-29255558518684423515679746799/5629499534213120000000000000000000), (-6608656250024356946557446793/2814749767106560000000000000000000), (1273601821828681118403162703/11258999068426240000000000000000000), (201331634898247077139690901/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial137.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial137.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial137.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 5416595309912213898844447415202655), (Int.negOfNat 103604924422200882539355486203053), (Int.negOfNat 255197600558621719115485688035533), (Int.negOfNat 3981342427218586418188516076634), (Int.ofNat 10570616742546267170200671859593), (Int.negOfNat 125755521284734857199452582907), (Int.negOfNat 202023118267499858291556701992), (Int.ofNat 7917155776750631333796471403), (Int.ofNat 2020718709108509756560479567), (Int.negOfNat 116987173436535550800035924), (Int.negOfNat 12182479085428515734403324), (Int.ofNat 906364269576717479881005), (Int.ofNat 48960881838082780897491), (Int.negOfNat 4551468634247974366812), (Int.negOfNat 138819072758371441190), (Int.ofNat 16547945167418551951), (Int.ofNat 212872270693163089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-1083319061982442779768889483040531/2251799813685248000000000000000000), (-103604924422200882539355486203053/11258999068426240000000000000000000), (-255197600558621719115485688035533/11258999068426240000000000000000000), (-1990671213609293209094258038317/5629499534213120000000000000000000), (10570616742546267170200671859593/11258999068426240000000000000000000), (-125755521284734857199452582907/11258999068426240000000000000000000), (-25252889783437482286444587749/1407374883553280000000000000000000), (7917155776750631333796471403/11258999068426240000000000000000000), (2020718709108509756560479567/11258999068426240000000000000000000), (-29246793359133887700008981/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial137.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial137.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial137.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 6522809743378759987473906158563961), (Int.negOfNat 877465233073062319672184112655746), (Int.negOfNat 75646738163145710920063748001174), (Int.ofNat 50510755315949560668347201179303), (Int.ofNat 1078985436020333748218498762495), (Int.negOfNat 1283623245852919578705021000904), (Int.ofNat 30820477092422988499382975928), (Int.ofNat 17200513629668089774547328517), (Int.negOfNat 894062268211058586966983988), (Int.negOfNat 130668038843012605422276886), (Int.ofNat 9649071236465458593584986), (Int.ofNat 618556885771567474284060), (Int.negOfNat 60798813355912298287024), (Int.negOfNat 1936391686363993425153), (Int.ofNat 259583925274940885690), (Int.ofNat 3838400256810845624), (Int.negOfNat 1016005963095586691), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-6522809743378759987473906158563961/11258999068426240000000000000000000), (-438732616536531159836092056327873/5629499534213120000000000000000000), (-37823369081572855460031874000587/5629499534213120000000000000000000), (50510755315949560668347201179303/11258999068426240000000000000000000), (215797087204066749643699752499/2251799813685248000000000000000000), (-160452905731614947338127625113/1407374883553280000000000000000000), (3852559636552873562422871991/1407374883553280000000000000000000), (17200513629668089774547328517/11258999068426240000000000000000000), (-223515567052764646741745997/2814749767106560000000000000000000), (-65334019421506302711138443/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial137.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial137.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial137.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 8196164015343540303033756919917255), (Int.negOfNat 629623861113540231705107252469860), (Int.ofNat 167499222606238170105857096494859), (Int.ofNat 20223761801452180257221831321166), (Int.negOfNat 6472407859230493999493856408604), (Int.negOfNat 43331073420484254489291682873), (Int.ofNat 121432440955159983678216792762), (Int.negOfNat 5028897093682804525079250483), (Int.negOfNat 1203347292722421480359161852), (Int.ofNat 86027091701246704256595584), (Int.ofNat 6922785865928793998083834), (Int.negOfNat 709226555809781993827280), (Int.negOfNat 24307349669050910293236), (Int.ofNat 3693974923121558941377), (Int.ofNat 49495660094717285850), (Int.negOfNat 14118175371000007276), (Int.negOfNat 1422097228113109), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-1639232803068708060606751383983451/2251799813685248000000000000000000), (-31481193055677011585255362623493/562949953421312000000000000000000), (167499222606238170105857096494859/11258999068426240000000000000000000), (10111880900726090128610915660583/5629499534213120000000000000000000), (-1618101964807623499873464102151/2814749767106560000000000000000000), (-43331073420484254489291682873/11258999068426240000000000000000000), (60716220477579991839108396381/5629499534213120000000000000000000), (-5028897093682804525079250483/11258999068426240000000000000000000), (-300836823180605370089790463/2814749767106560000000000000000000), (672086653915989877004653/87960930222080000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial137.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial137.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial137.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 8721700338982757256365430212377290), (Int.ofNat 92529752658953070199560674819114), (Int.ofNat 154100633017571335921125521356733), (Int.negOfNat 18294920952992365422339408647971), (Int.negOfNat 1967381697286554244899256108944), (Int.ofNat 659378918313189566747462495324), (Int.negOfNat 13783867910744290033082006898), (Int.negOfNat 9203972762357251461275842797), (Int.ofNat 613305200642130888182433323), (Int.ofNat 66915496469547348617297586), (Int.negOfNat 7088204071584918217106796), (Int.negOfNat 269519472266385802614465), (Int.ofNat 46191280749447492339099), (Int.ofNat 504976884493675136808), (Int.negOfNat 201597906010199070250), (Int.ofNat 630992032391983581), (Int.ofNat 888227952889167271), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-872170033898275725636543021237729/1125899906842624000000000000000000), (46264876329476535099780337409557/5629499534213120000000000000000000), (154100633017571335921125521356733/11258999068426240000000000000000000), (-18294920952992365422339408647971/11258999068426240000000000000000000), (-122961356080409640306203506809/703687441776640000000000000000000), (164844729578297391686865623831/2814749767106560000000000000000000), (-6891933955372145016541003449/5629499534213120000000000000000000), (-9203972762357251461275842797/11258999068426240000000000000000000), (613305200642130888182433323/11258999068426240000000000000000000), (33457748234773674308648793/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial137.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial137.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial137.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 8078852280395263326887900957371876), (Int.ofNat 473161459746284897512415462631388), (Int.ofNat 41692334656520222081355595330046), (Int.negOfNat 13674735887906507825996187637733), (Int.ofNat 2078155599391288713278043836010), (Int.ofNat 70022083261916486393460647643), (Int.negOfNat 54089275005507641388707330352), (Int.ofNat 3158951941008939440921800258), (Int.ofNat 536431893718400325543557847), (Int.negOfNat 58947634713091234507631239), (Int.negOfNat 2546812929233962538446089), (Int.ofNat 500579888726782833608220), (Int.ofNat 3740603368381995055731), (Int.negOfNat 2645853141174994692602), (Int.ofNat 24998213073472021525), (Int.ofNat 9612246521837161881), (Int.negOfNat 146139071133727161), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-2019713070098815831721975239342969/2814749767106560000000000000000000), (118290364936571224378103865657847/2814749767106560000000000000000000), (20846167328260111040677797665023/5629499534213120000000000000000000), (-13674735887906507825996187637733/11258999068426240000000000000000000), (207815559939128871327804383601/1125899906842624000000000000000000), (70022083261916486393460647643/11258999068426240000000000000000000), (-3380579687844227586794208147/703687441776640000000000000000000), (1579475970504469720460900129/5629499534213120000000000000000000), (536431893718400325543557847/11258999068426240000000000000000000), (-58947634713091234507631239/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial137.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial137.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial137.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 7042618523896216325960806212400265), (Int.ofNat 539372829122072805077976518089559), (Int.ofNat 4937069609809649431473860684082), (Int.negOfNat 507787881037405185482019331426), (Int.ofNat 767124747744524377764263291213), (Int.negOfNat 198390073198692962313183194704), (Int.ofNat 9128787862550891670692874338), (Int.ofNat 3281111250586168786593317602), (Int.negOfNat 389743520893728188620846818), (Int.negOfNat 19146558829207197849250811), (Int.ofNat 4582494308197711304431196), (Int.ofNat 6734250474647154227225), (Int.negOfNat 30100909141992494605284), (Int.ofNat 558073945144641533572), (Int.ofNat 131527819890659611685), (Int.negOfNat 4475595314641193211), (Int.negOfNat 633806815135565221), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-1408523704779243265192161242480053/2251799813685248000000000000000000), (539372829122072805077976518089559/11258999068426240000000000000000000), (2468534804904824715736930342041/5629499534213120000000000000000000), (-253893940518702592741009665713/5629499534213120000000000000000000), (767124747744524377764263291213/11258999068426240000000000000000000), (-12399379574918310144573949669/703687441776640000000000000000000), (4564393931275445835346437169/5629499534213120000000000000000000), (1640555625293084393296658801/5629499534213120000000000000000000), (-194871760446864094310423409/5629499534213120000000000000000000), (-19146558829207197849250811/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial137.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial137.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial137.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 5941362139814200084528241456841229), (Int.ofNat 564506735218266274403735376540124), (Int.ofNat 8090378176513126195692856372960), (Int.ofNat 257816643048735068819781690570), (Int.negOfNat 205665125865623450855387777145), (Int.ofNat 7968278700950040732003170012), (Int.ofNat 12473887854985254633366361252), (Int.negOfNat 1929533620043178622615879018), (Int.negOfNat 95179202129921036099972327), (Int.ofNat 34058155234525918875194394), (Int.negOfNat 378332868189532498167966), (Int.negOfNat 287595581883318161795600), (Int.ofNat 9752291562903406671014), (Int.ofNat 1502795473708684553957), (Int.negOfNat 70790288103063843625), (Int.negOfNat 5107148986824841766), (Int.ofNat 208893193577700081), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-5941362139814200084528241456841229/11258999068426240000000000000000000), (141126683804566568600933844135031/2814749767106560000000000000000000), (50564863603207038723080352331/70368744177664000000000000000000), (25781664304873506881978169057/1125899906842624000000000000000000), (-41133025173124690171077555429/2251799813685248000000000000000000), (1992069675237510183000792503/2814749767106560000000000000000000), (3118471963746313658341590313/2814749767106560000000000000000000), (-964766810021589311307939509/5629499534213120000000000000000000), (-95179202129921036099972327/11258999068426240000000000000000000), (17029077617262959437597197/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial137.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial137.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial137.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 4780416785683066413933666026303896), (Int.ofNat 595524921598548030968418324459728), (Int.ofNat 7010654081014175051906575085922), (Int.negOfNat 157436922363873918876318437431), (Int.ofNat 97370555026498882211237342282), (Int.ofNat 11437509908179579761500806554), (Int.negOfNat 6994755045989678504498822973), (Int.negOfNat 55784859702588135906478647), (Int.ofNat 192242925877581066306874628), (Int.negOfNat 8212683075677993567855384), (Int.negOfNat 2172328226264653722822266), (Int.ofNat 139929012932540839280545), (Int.ofNat 13823534228885987460329), (Int.negOfNat 1112707939086120651437), (Int.negOfNat 57586372252960425960), (Int.ofNat 5593996168465435801), (Int.ofNat 379385677381963171), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-597552098210383301741708253287987/1407374883553280000000000000000000), (37220307599909251935526145278733/703687441776640000000000000000000), (3505327040507087525953287542961/5629499534213120000000000000000000), (-157436922363873918876318437431/11258999068426240000000000000000000), (48685277513249441105618671141/5629499534213120000000000000000000), (5718754954089789880750403277/5629499534213120000000000000000000), (-6994755045989678504498822973/11258999068426240000000000000000000), (-55784859702588135906478647/11258999068426240000000000000000000), (48060731469395266576718657/2814749767106560000000000000000000), (-1026585384459749195981923/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial137.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial137.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial137.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 3561071578955304397988269265054417), (Int.ofNat 624509832785730856033770918918984), (Int.ofNat 7888008779186305855696342983494), (Int.ofNat 202718767100363935722095767972), (Int.negOfNat 63344108458102670742115232274), (Int.negOfNat 20003381286844967017670583722), (Int.ofNat 3550426803285767418603326093), (Int.ofNat 703595243713731847800796038), (Int.negOfNat 104373437086861186702231428), (Int.negOfNat 11047837914499882109458929), (Int.ofNat 1660412329629820595855131), (Int.ofNat 86168475250082740527020), (Int.negOfNat 14877392602077553551394), (Int.negOfNat 390717953752702784032), (Int.ofNat 85005586950606332310), (Int.ofNat 478529429253038631), (Int.negOfNat 271647316021673001), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-3561071578955304397988269265054417/11258999068426240000000000000000000), (78063729098216357004221364864873/1407374883553280000000000000000000), (3944004389593152927848171491747/5629499534213120000000000000000000), (50679691775090983930523941993/2814749767106560000000000000000000), (-31672054229051335371057616137/5629499534213120000000000000000000), (-10001690643422483508835291861/5629499534213120000000000000000000), (3550426803285767418603326093/11258999068426240000000000000000000), (351797621856865923900398019/5629499534213120000000000000000000), (-26093359271715296675557857/2814749767106560000000000000000000), (-11047837914499882109458929/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial137.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial137.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial137.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 2280245016646655301117483037327078), (Int.ofNat 655740866476561923701389405727425), (Int.ofNat 7091283671568428498145364222249), (Int.negOfNat 361100654992910365572042301721), (Int.ofNat 9226429846217222412612441082), (Int.ofNat 27060040426362241201443151496), (Int.ofNat 239538427687618054793276188), (Int.negOfNat 891052528679191139009243383), (Int.negOfNat 8385632799268999584393613), (Int.ofNat 15779247681952023647063429), (Int.ofNat 34469335639656829022841), (Int.negOfNat 166118767733949833270160), (Int.ofNat 805942684371207095336), (Int.ofNat 1119296792760440512952), (Int.negOfNat 9322189228711933215), (Int.negOfNat 5438580953402456706), (Int.negOfNat 104046498813703481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1140122508323327650558741518663539/5629499534213120000000000000000000), (26229634659062476948055576229097/450359962737049600000000000000000), (7091283671568428498145364222249/11258999068426240000000000000000000), (-361100654992910365572042301721/11258999068426240000000000000000000), (4613214923108611206306220541/5629499534213120000000000000000000), (3382505053295280150180393937/1407374883553280000000000000000000), (59884606921904513698319047/2814749767106560000000000000000000), (-891052528679191139009243383/11258999068426240000000000000000000), (-8385632799268999584393613/11258999068426240000000000000000000), (15779247681952023647063429/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial137.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial137.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial137.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 942366494871396124830016576021352), (Int.ofNat 681905792905857608331323991129123), (Int.ofNat 6823247102164048826273221696951), (Int.ofNat 398165250410310118390938267180), (Int.ofNat 92867970663264776977090132089), (Int.negOfNat 21069094894485040711245105308), (Int.negOfNat 4637947144669413778947255568), (Int.ofNat 533746909798367017763752237), (Int.ofNat 109121372391913289973125833), (Int.negOfNat 8010486885355361573337071), (Int.negOfNat 1444633916663743198816261), (Int.ofNat 79089187045456215164740), (Int.ofNat 11929132906868359816624), (Int.negOfNat 538786513008739836588), (Int.negOfNat 66363167902025027465), (Int.ofNat 3106684488381441494), (Int.ofNat 143869305815253581), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-117795811858924515603752072002669/1407374883553280000000000000000000), (681905792905857608331323991129123/11258999068426240000000000000000000), (6823247102164048826273221696951/11258999068426240000000000000000000), (19908262520515505919546913359/562949953421312000000000000000000), (92867970663264776977090132089/11258999068426240000000000000000000), (-5267273723621260177811276327/2814749767106560000000000000000000), (-289871696541838361184203473/703687441776640000000000000000000), (533746909798367017763752237/11258999068426240000000000000000000), (109121372391913289973125833/11258999068426240000000000000000000), (-8010486885355361573337071/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial137.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial137.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial137.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 452529128667415011095612328951333), (Int.ofNat 714698680661339566864845248891922), (Int.ofNat 9146029254549580786388913171266), (Int.negOfNat 10053240837820090777577211162), (Int.negOfNat 171552493329435716059101745147), (Int.negOfNat 7489373806155732650854717826), (Int.ofNat 6533162749526201612086614447), (Int.ofNat 376640321809395817544608158), (Int.negOfNat 128257050819513447952994832), (Int.negOfNat 7764174144177948045343289), (Int.ofNat 1506927535023531989395469), (Int.ofNat 88281287577945167602980), (Int.negOfNat 11596362493081964458426), (Int.negOfNat 630406709014809348172), (Int.ofNat 62106645605751714110), (Int.ofNat 3800461215775643411), (Int.negOfNat 107403674651346499), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(452529128667415011095612328951333/11258999068426240000000000000000000), (357349340330669783432422624445961/5629499534213120000000000000000000), (4573014627274790393194456585633/5629499534213120000000000000000000), (-5026620418910045388788605581/5629499534213120000000000000000000), (-171552493329435716059101745147/11258999068426240000000000000000000), (-3744686903077866325427358913/5629499534213120000000000000000000), (6533162749526201612086614447/11258999068426240000000000000000000), (188320160904697908772304079/5629499534213120000000000000000000), (-8016065676219590497062177/703687441776640000000000000000000), (-7764174144177948045343289/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial137.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial137.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial137.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1915876876855110530875461270192117), (Int.ofNat 746355606275492200791072015071035), (Int.ofNat 5943733828651028069784688593823), (Int.negOfNat 671965458273849543754880019587), (Int.ofNat 98401328126105052877495792212), (Int.ofNat 42883764519554610120217288712), (Int.negOfNat 2178854338809677797609411967), (Int.negOfNat 1213236743273909646737450127), (Int.ofNat 15486825138520701236053792), (Int.ofNat 18725167044993333758378776), (Int.ofNat 91508969835288884507326), (Int.negOfNat 178029628811816255812715), (Int.negOfNat 2419471109533715997209), (Int.ofNat 1130583590308927946763), (Int.ofNat 19730827761390545700), (Int.negOfNat 5335552757310065539), (Int.ofNat 89633791123690829), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(1915876876855110530875461270192117/11258999068426240000000000000000000), (149271121255098440158214403014207/2251799813685248000000000000000000), (5943733828651028069784688593823/11258999068426240000000000000000000), (-671965458273849543754880019587/11258999068426240000000000000000000), (24600332031526263219373948053/2814749767106560000000000000000000), (5360470564944326265027161089/1407374883553280000000000000000000), (-2178854338809677797609411967/11258999068426240000000000000000000), (-1213236743273909646737450127/11258999068426240000000000000000000), (483963285578771913626681/351843720888320000000000000000000), (2340645880624166719797347/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial137.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial137.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial137.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3429652542306569271741509195630328), (Int.ofNat 767742095882520047948264742867676), (Int.ofNat 6476152800139111158157695382875), (Int.ofNat 924934617524640930679970927160), (Int.ofNat 143469511923077279104958455541), (Int.negOfNat 44880836771743199706286124864), (Int.negOfNat 7063664653018622225500827022), (Int.ofNat 941841934476376300680250622), (Int.ofNat 160960272132115163297390647), (Int.negOfNat 10316873881171825630977686), (Int.negOfNat 2051557254254174900795294), (Int.ofNat 64116127101075354871100), (Int.ofNat 16360044338997096592726), (Int.negOfNat 228390536939638450143), (Int.negOfNat 88207586592168162535), (Int.negOfNat 73600883458646626), (Int.ofNat 170157797095319419), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(428706567788321158967688649453791/1407374883553280000000000000000000), (191935523970630011987066185716919/2814749767106560000000000000000000), (51809222401112889265261563063/90071992547409920000000000000000), (23123365438116023266999273179/281474976710656000000000000000000), (143469511923077279104958455541/11258999068426240000000000000000000), (-701263074558487495410720701/175921860444160000000000000000000), (-3531832326509311112750413511/5629499534213120000000000000000000), (470920967238188150340125311/5629499534213120000000000000000000), (160960272132115163297390647/11258999068426240000000000000000000), (-5158436940585912815488843/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial137.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial137.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial137.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4999002646696524291224443077679509), (Int.ofNat 804943853071359566185465057287512), (Int.ofNat 11036309745824828821878395659273), (Int.negOfNat 119411386367946704693157062656), (Int.negOfNat 349726867745073045578439060977), (Int.negOfNat 12369453353509407386108336302), (Int.ofNat 12124730046924481029916643892), (Int.ofNat 754047167123147345313742322), (Int.negOfNat 204755670618649077820802902), (Int.negOfNat 16107008296158267093036451), (Int.ofNat 1945211820882961577764664), (Int.ofNat 181087862395459002386885), (Int.negOfNat 11426433642890364772596), (Int.negOfNat 1252915720828565073708), (Int.ofNat 44006590014929600875), (Int.ofNat 6044516405208652469), (Int.negOfNat 344054928877292879), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(4999002646696524291224443077679509/11258999068426240000000000000000000), (100617981633919945773183132160939/1407374883553280000000000000000000), (11036309745824828821878395659273/11258999068426240000000000000000000), (-58306340999973976900955597/5497558138880000000000000000000), (-349726867745073045578439060977/11258999068426240000000000000000000), (-6184726676754703693054168151/5629499534213120000000000000000000), (3031182511731120257479160973/2814749767106560000000000000000000), (377023583561573672656871161/5629499534213120000000000000000000), (-102377835309324538910401451/5629499534213120000000000000000000), (-16107008296158267093036451/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial137.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial137.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial137.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 6646902991469809646230222154539222), (Int.ofNat 837905978515915355065251490239606), (Int.ofNat 3938909183278856872465476249440), (Int.negOfNat 1467377732099562546129982338028), (Int.ofNat 202872729883877430998519654499), (Int.ofNat 91796533764661592043323606534), (Int.negOfNat 2765169856485656721687226688), (Int.negOfNat 2416960858000707556176598802), (Int.negOfNat 34848102288017535598964207), (Int.ofNat 32632110871062392309452821), (Int.ofNat 1215687935656784443521049), (Int.negOfNat 257145279638250255416440), (Int.negOfNat 13330145098674558304171), (Int.ofNat 1301996271271805562438), (Int.ofNat 83016255847641250895), (Int.negOfNat 4116009655089302579), (Int.negOfNat 232911919539292339), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(3323451495734904823115111077269611/5629499534213120000000000000000000), (418952989257957677532625745119803/5629499534213120000000000000000000), (24618182395492855452909226559/70368744177664000000000000000000), (-366844433024890636532495584507/2814749767106560000000000000000000), (202872729883877430998519654499/11258999068426240000000000000000000), (45898266882330796021661803267/5629499534213120000000000000000000), (-43205779007588386276362917/175921860444160000000000000000000), (-1208480429000353778088299401/5629499534213120000000000000000000), (-34848102288017535598964207/11258999068426240000000000000000000), (32632110871062392309452821/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial137.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial137.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial137.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 8332437136284468643408244723741311), (Int.ofNat 848317599138857845023791893706926), (Int.ofNat 5153490407274770261851098966257), (Int.ofNat 2151265316396695836916228276154), (Int.ofNat 375055826256235504754073729788), (Int.negOfNat 92890175200317357717880757288), (Int.negOfNat 18746664076112149132914852602), (Int.ofNat 1366043146197328140995055183), (Int.ofNat 391142011832326490976160217), (Int.negOfNat 4770807620062597983853114), (Int.negOfNat 4234765068144061808833684), (Int.negOfNat 65294133050204475014685), (Int.ofNat 27288352967034959364041), (Int.ofNat 830398431255923108108), (Int.negOfNat 117305766212889305750), (Int.negOfNat 4890278351222642039), (Int.ofNat 598476066630894929), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(8332437136284468643408244723741311/11258999068426240000000000000000000), (424158799569428922511895946853463/5629499534213120000000000000000000), (5153490407274770261851098966257/11258999068426240000000000000000000), (1075632658198347918458114138077/5629499534213120000000000000000000), (93763956564058876188518432447/2814749767106560000000000000000000), (-11611271900039669714735094661/1407374883553280000000000000000000), (-9373332038056074566457426301/5629499534213120000000000000000000), (1366043146197328140995055183/11258999068426240000000000000000000), (391142011832326490976160217/11258999068426240000000000000000000), (-2385403810031298991926557/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial137.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial137.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial137.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 10068993229463517559000154755433789), (Int.ofNat 896697765279942269434358425182922), (Int.ofNat 16680239076756776464578824769626), (Int.negOfNat 187680031853327224294048889570), (Int.negOfNat 933352326580115227225958626155), (Int.negOfNat 70659877294426384020347319649), (Int.ofNat 27482811354199517267592909828), (Int.ofNat 3252999332765786694779038217), (Int.negOfNat 317965789441215953353962388), (Int.negOfNat 54732612317494017393434296), (Int.ofNat 1313983975885357061830906), (Int.ofNat 463550395774509058605200), (Int.ofNat 1683964731719431971416), (Int.negOfNat 2443156868413806822163), (Int.negOfNat 43660123270767599310), (Int.ofNat 9143173140374082664), (Int.ofNat 210858996065397909), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(10068993229463517559000154755433789/11258999068426240000000000000000000), (448348882639971134717179212591461/5629499534213120000000000000000000), (8340119538378388232289412384813/5629499534213120000000000000000000), (-18768003185332722429404888957/1125899906842624000000000000000000), (-186670465316023045445191725231/2251799813685248000000000000000000), (-70659877294426384020347319649/11258999068426240000000000000000000), (6870702838549879316898227457/2814749767106560000000000000000000), (3252999332765786694779038217/11258999068426240000000000000000000), (-79491447360303988338490597/2814749767106560000000000000000000), (-6841576539686752174179287/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial137.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial137.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial137.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 11912481665616349247955025529139145), (Int.ofNat 931940696716085431359263442832251), (Int.negOfNat 4511293550406372396815062696191), (Int.negOfNat 5086779393213780045230766994911), (Int.ofNat 379594536907509833798793477827), (Int.ofNat 303248352277748593689826387473), (Int.ofNat 11454056000976390105851291732), (Int.negOfNat 6236142131436675076155747343), (Int.negOfNat 542563531147237121413015052), (Int.ofNat 48810079511557288470842714), (Int.ofNat 6587679056958271960959594), (Int.negOfNat 177009175299014132256540), (Int.negOfNat 43457941500098251359756), (Int.ofNat 127978992290210528627), (Int.ofNat 188931242423692927890), (Int.ofNat 2460508554804097364), (Int.negOfNat 809926240095944909), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(2382496333123269849591005105827829/2251799813685248000000000000000000), (931940696716085431359263442832251/11258999068426240000000000000000000), (-4511293550406372396815062696191/11258999068426240000000000000000000), (-5086779393213780045230766994911/11258999068426240000000000000000000), (379594536907509833798793477827/11258999068426240000000000000000000), (303248352277748593689826387473/11258999068426240000000000000000000), (2863514000244097526462822933/2814749767106560000000000000000000), (-6236142131436675076155747343/11258999068426240000000000000000000), (-135640882786809280353253763/2814749767106560000000000000000000), (24405039755778644235421357/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial137.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial137.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial137.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 13733228246892966072878782874824160), (Int.ofNat 888254019363201546922122258929965), (Int.negOfNat 3782843980844999550153250263197), (Int.ofNat 7799443745754083719295035066777), (Int.ofNat 2018129035667355561059553086830), (Int.negOfNat 184085956662638397440539990041), (Int.negOfNat 86697407070400106466899552588), (Int.negOfNat 3503612590641534289609120337), (Int.ofNat 985129937945430355104327773), (Int.ofNat 78420950754169940482401256), (Int.negOfNat 5592675582580756092595076), (Int.negOfNat 674428440123856040189775), (Int.ofNat 17742039134931339197089), (Int.ofNat 3535321606573748919568), (Int.negOfNat 24050702141123222090), (Int.negOfNat 13612565429576911869), (Int.negOfNat 83080985858978489), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(85832676543081037955492392967651/70368744177664000000000000000000), (177650803872640309384424451785993/2251799813685248000000000000000000), (-3782843980844999550153250263197/11258999068426240000000000000000000), (7799443745754083719295035066777/11258999068426240000000000000000000), (201812903566735556105955308683/1125899906842624000000000000000000), (-184085956662638397440539990041/11258999068426240000000000000000000), (-21674351767600026616724888147/2814749767106560000000000000000000), (-3503612590641534289609120337/11258999068426240000000000000000000), (985129937945430355104327773/11258999068426240000000000000000000), (9802618844271242560300157/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial137.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial137.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial137.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 15577688014611037655491421685353470), (Int.ofNat 999507542265748673900173047979067), (Int.ofNat 55605273828191327977250798660656), (Int.ofNat 2822973117057819679367170178689), (Int.negOfNat 4686220388166082826132662383916), (Int.negOfNat 981466109856313155526695261278), (Int.ofNat 296964373672944770430802598), (Int.ofNat 15427080266154154714206208328), (Int.ofNat 770680010866098414535430977), (Int.negOfNat 115742437411088507670166439), (Int.negOfNat 9239380380557346079066159), (Int.ofNat 520120849147068811777780), (Int.ofNat 59026320791390703353801), (Int.negOfNat 1489053860385450616382), (Int.negOfNat 252797483573753198185), (Int.ofNat 2643981441156183231), (Int.ofNat 957487408457785179), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(1557768801461103765549142168535347/1125899906842624000000000000000000), (999507542265748673900173047979067/11258999068426240000000000000000000), (3475329614261957998578174916291/703687441776640000000000000000000), (2822973117057819679367170178689/11258999068426240000000000000000000), (-1171555097041520706533165595979/2814749767106560000000000000000000), (-490733054928156577763347630639/5629499534213120000000000000000000), (148482186836472385215401299/5629499534213120000000000000000000), (1928385033269269339275776041/1407374883553280000000000000000000), (770680010866098414535430977/11258999068426240000000000000000000), (-115742437411088507670166439/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial137.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial137.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial137.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 17717445073264532988760885909981805), (Int.ofNat 1034778725053971114655696348333093), (Int.negOfNat 107245608934885096941890384477193), (Int.negOfNat 64593842359782166401596352771499), (Int.negOfNat 9862511915767123941506796871666), (Int.ofNat 376021554591850945841566269616), (Int.ofNat 204440507055573706149228274648), (Int.ofNat 6197558980389708278997301772), (Int.negOfNat 1927016631451787369894432598), (Int.negOfNat 113519740650382454806694531), (Int.ofNat 10959561843354155540395816), (Int.ofNat 894472900405091957225075), (Int.negOfNat 41679807045688073049084), (Int.negOfNat 4478112293225772070728), (Int.ofNat 110703818184399383815), (Int.ofNat 16608158161232816139), (Int.negOfNat 171340151894623561), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(3543489014652906597752177181996361/2251799813685248000000000000000000), (1034778725053971114655696348333093/11258999068426240000000000000000000), (-107245608934885096941890384477193/11258999068426240000000000000000000), (-64593842359782166401596352771499/11258999068426240000000000000000000), (-4931255957883561970753398435833/5629499534213120000000000000000000), (23501347161990684115097891851/703687441776640000000000000000000), (25555063381946713268653534331/1407374883553280000000000000000000), (1549389745097427069749325443/2814749767106560000000000000000000), (-963508315725893684947216299/5629499534213120000000000000000000), (-113519740650382454806694531/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial137.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial137.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial137.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 18708840738868844950400359185586826), (Int.negOfNat 414989264687128219399962024777535), (Int.negOfNat 652025091459871789124497490552755), (Int.negOfNat 96135231223101249190302220929157), (Int.ofNat 5461794292192730873827037178336), (Int.ofNat 2367028175128216016427893606088), (Int.ofNat 45818330016718194891430118002), (Int.negOfNat 27212630225897402290074387208), (Int.negOfNat 1298156308003003289345276257), (Int.ofNat 189553997125683930338684424), (Int.ofNat 12499823416021275677826034), (Int.negOfNat 890101363648236828034500), (Int.negOfNat 73093026586131593685406), (Int.ofNat 2999884281972693190407), (Int.ofNat 299403164003181114445), (Int.negOfNat 7274303678066438426), (Int.negOfNat 1020241530901758099), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(9354420369434422475200179592793413/5629499534213120000000000000000000), (-82997852937425643879992404955507/2251799813685248000000000000000000), (-130405018291974357824899498110551/2251799813685248000000000000000000), (-96135231223101249190302220929157/11258999068426240000000000000000000), (170681071631022839807094911823/351843720888320000000000000000000), (295878521891027002053486700761/1407374883553280000000000000000000), (22909165008359097445715059001/5629499534213120000000000000000000), (-3401578778237175286259298401/1407374883553280000000000000000000), (-1298156308003003289345276257/11258999068426240000000000000000000), (23694249640710491292335553/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial137.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial137.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial137.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 14664038190911004719148855808333419), (Int.negOfNat 3816807084052950448836662550782531), (Int.negOfNat 917019905985147333448289186935663), (Int.ofNat 33172106055518475079144603888291), (Int.ofNat 23694500914047463951642080492436), (Int.ofNat 499888502157143288125930870895), (Int.negOfNat 327791318429445743899686073653), (Int.negOfNat 14796181396072481402667497087), (Int.ofNat 2782047982738239422303587068), (Int.ofNat 164952678170350488503392346), (Int.negOfNat 15860122125206041118140206), (Int.negOfNat 1110698415406863761359225), (Int.ofNat 64789147700914702900139), (Int.ofNat 5167548763712106008533), (Int.negOfNat 198563986311965863980), (Int.negOfNat 18199895459956558849), (Int.ofNat 425761289648225611), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(14664038190911004719148855808333419/11258999068426240000000000000000000), (-3816807084052950448836662550782531/11258999068426240000000000000000000), (-917019905985147333448289186935663/11258999068426240000000000000000000), (33172106055518475079144603888291/11258999068426240000000000000000000), (5923625228511865987910520123109/2814749767106560000000000000000000), (99977700431428657625186174179/2251799813685248000000000000000000), (-327791318429445743899686073653/11258999068426240000000000000000000), (-14796181396072481402667497087/11258999068426240000000000000000000), (695511995684559855575896767/2814749767106560000000000000000000), (82476339085175244251696173/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial137.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial137.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial137.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 4000735586891465844009282626660808), (Int.negOfNat 6355033954375529890883566349659927), (Int.negOfNat 192404455845103755412097840572991), (Int.ofNat 187581501750069623780168094695285), (Int.ofNat 8413735797900150226041462598290), (Int.negOfNat 3250304098736662401631599278473), (Int.negOfNat 177437893502536729790087773087), (Int.ofNat 34476072272475136057452597788), (Int.ofNat 2105413588783203132424494892), (Int.negOfNat 240945799142507643128679029), (Int.negOfNat 15918501105039322300605419), (Int.ofNat 1186661759465776319574740), (Int.ofNat 83463359427885047318966), (Int.negOfNat 4346378347903315176312), (Int.negOfNat 322342126911068301690), (Int.ofNat 12028147937536176641), (Int.ofNat 1082995653345731019), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(500091948361433230501160328332601/1407374883553280000000000000000000), (-6355033954375529890883566349659927/11258999068426240000000000000000000), (-192404455845103755412097840572991/11258999068426240000000000000000000), (37516300350013924756033618939057/2251799813685248000000000000000000), (841373579790015022604146259829/1125899906842624000000000000000000), (-3250304098736662401631599278473/11258999068426240000000000000000000), (-177437893502536729790087773087/11258999068426240000000000000000000), (8619018068118784014363149447/2814749767106560000000000000000000), (526353397195800783106123723/2814749767106560000000000000000000), (-240945799142507643128679029/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial137.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial137.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial137.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 7954229124748300193700737228799584), (Int.negOfNat 4881546879739947956998734675806541), (Int.ofNat 858090208981751830602714058835954), (Int.ofNat 118086869927773635857228245186806), (Int.negOfNat 23850832794814444436509578477457), (Int.negOfNat 2112625244711679982314556827875), (Int.ofNat 346947184731650393626435498798), (Int.ofNat 25971935831492674993220374597), (Int.negOfNat 3097581152132152401560814083), (Int.negOfNat 216594256983599082317111451), (Int.ofNat 18700680806889206011297891), (Int.ofNat 1268480330727478243872540), (Int.negOfNat 81828778852262951949584), (Int.negOfNat 5457952819770449441668), (Int.ofNat 272455892140380383995), (Int.ofNat 17919255542995644674), (Int.negOfNat 701100468216485301), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-248569660148384381053148038399987/351843720888320000000000000000000), (-4881546879739947956998734675806541/11258999068426240000000000000000000), (429045104490875915301357029417977/5629499534213120000000000000000000), (59043434963886817928614122593403/5629499534213120000000000000000000), (-23850832794814444436509578477457/11258999068426240000000000000000000), (-16901001957693439858516454623/90071992547409920000000000000000), (173473592365825196813217749399/5629499534213120000000000000000000), (25971935831492674993220374597/11258999068426240000000000000000000), (-3097581152132152401560814083/11258999068426240000000000000000000), (-216594256983599082317111451/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial137.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial137.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial137.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial137.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial137.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial137.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial137.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial137.reflect := by
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

end Bin137
end
end ErdosOverlap.OuterNumerics
