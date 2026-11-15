/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.IntegerOuterBindings
public import ErdosOverlap.Numerics.OuterTruncation
public import ErdosOverlap.Certificate.OuterData10
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

/-! # Exact integer weighted outer models for source bin 130

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin130

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 4202309242231808700)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 3230494851665240000)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 2401928568171482200)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 1652434050849295500)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 1094712494237486400)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 644949328754553200)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 309823147970551000)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 71220395187088160)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial130.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial130.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9357482539147787000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1281010388730067000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1723926780164824000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 252667476498973120)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 165904818735878760)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 5269000769339277)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 84259562533046850)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 19505532077136894)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 5411136732834478)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial130.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial130.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9357482539147787000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1281010388730067000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1723926780164824000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 252667476498973120)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 165904818735878760)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 5269000769339277)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 84259562533046850)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 19505532077136894)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 5411136732834478)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial130.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial130.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial130.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 12162365072828307047391828550058390), (Int.ofNat 4237240699137323418208404605437941), (Int.ofNat 983639625386855712532357513186052), (Int.negOfNat 120046303250058536292713754098466), (Int.negOfNat 23346423274837322193643934445221), (Int.ofNat 2168101826724328317311054394466), (Int.ofNat 310602523193768782609861134409), (Int.negOfNat 24699420737296198583658181644), (Int.negOfNat 2666561864976520200720523174), (Int.ofNat 190063856689046910757358838), (Int.ofNat 15991027332995273901090768), (Int.negOfNat 1047489810404740912258209), (Int.negOfNat 70810550858178005212505), (Int.ofNat 4324009248508442780503), (Int.ofNat 242165390509980887508), (Int.negOfNat 13633329108485737666), (Int.negOfNat 652963835586121826), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1216236507282830704739182855005839/1125899906842624000000000000000000), (4237240699137323418208404605437941/11258999068426240000000000000000000), (245909906346713928133089378296513/2814749767106560000000000000000000), (-60023151625029268146356877049233/5629499534213120000000000000000000), (-23346423274837322193643934445221/11258999068426240000000000000000000), (1084050913362164158655527197233/5629499534213120000000000000000000), (310602523193768782609861134409/11258999068426240000000000000000000), (-6174855184324049645914545411/2814749767106560000000000000000000), (-1333280932488260100360261587/5629499534213120000000000000000000), (95031928344523455378679419/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial130.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial130.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial130.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial130 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.negOfNat 1001713426052319548441536005026173), (Int.ofNat 6203952443957152766105481015687698), (Int.negOfNat 69309574801238302828606459162639), (Int.negOfNat 187790765465882933596473859473399), (Int.ofNat 7998185029852065746799712446895), (Int.ofNat 3101555718899885694060498395647), (Int.negOfNat 170969402048720928595177711948), (Int.negOfNat 31414053528093260673561176795), (Int.ofNat 1900895272589413936903288161), (Int.ofNat 214600451964517410280014146), (Int.negOfNat 13553573429929344038075781), (Int.negOfNat 1056532919078440000023164), (Int.ofNat 68197322415255276522823), (Int.ofNat 3932884117905714108782), (Int.negOfNat 257083482132315766012), (Int.negOfNat 11131326055138963952), (Int.ofNat 810504929134369138), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-1001713426052319548441536005026173/11258999068426240000000000000000000), (3101976221978576383052740507843849/5629499534213120000000000000000000), (-69309574801238302828606459162639/11258999068426240000000000000000000), (-187790765465882933596473859473399/11258999068426240000000000000000000), (1599637005970413149359942489379/2251799813685248000000000000000000), (3101555718899885694060498395647/11258999068426240000000000000000000), (-42742350512180232148794427987/2814749767106560000000000000000000), (-6282810705618652134712235359/2251799813685248000000000000000000), (1900895272589413936903288161/11258999068426240000000000000000000), (107300225982258705140007073/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial130.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial130.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial130.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial130 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 9839465510837930671016886443963123), (Int.ofNat 4132753231181616198111129868627265), (Int.negOfNat 813901642356328008370807450252296), (Int.negOfNat 40374120600467544894100628330083), (Int.ofNat 22736919642395346334379809229169), (Int.negOfNat 437239132576114765949232788414), (Int.negOfNat 310137259081385024830719457495), (Int.ofNat 13346378915269719872584372122), (Int.ofNat 2575514684515444128237826816), (Int.negOfNat 142775017920963311743350637), (Int.negOfNat 14574803837506248492891820), (Int.ofNat 928171798208201167504656), (Int.ofNat 60203975934161358598406), (Int.negOfNat 4216127565927214340848), (Int.negOfNat 189841738634647470436), (Int.ofNat 14435717807164955628), (Int.ofNat 433891513292022868), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(9839465510837930671016886443963123/11258999068426240000000000000000000), (826550646236323239622225973725453/2251799813685248000000000000000000), (-101737705294541001046350931281537/1407374883553280000000000000000000), (-40374120600467544894100628330083/11258999068426240000000000000000000), (22736919642395346334379809229169/11258999068426240000000000000000000), (-218619566288057382974616394207/5629499534213120000000000000000000), (-62027451816277004966143891499/2251799813685248000000000000000000), (6673189457634859936292186061/5629499534213120000000000000000000), (10060604236388453625929011/43980465111040000000000000000000), (-142775017920963311743350637/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial130.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial130.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial130.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial130 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 14858604469608844835084213394087159), (Int.ofNat 1033937778805511624409203322124061), (Int.negOfNat 607084612643810689860598318367952), (Int.ofNat 85552215909530862751762494212243), (Int.ofNat 5651440315371139260905308680906), (Int.negOfNat 2257315026688931226516508043995), (Int.ofNat 36503023334710347005803705659), (Int.ofNat 25908683598865436183132976883), (Int.negOfNat 1113251943822404902379464651), (Int.negOfNat 179505651051811459565250021), (Int.ofNat 10563981680936553667615656), (Int.ofNat 850657049770504687470750), (Int.negOfNat 60766965266719286178209), (Int.negOfNat 2956250928023493568923), (Int.ofNat 245824380998560712863), (Int.ofNat 7404879682258991932), (Int.negOfNat 794271518935865704), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(14858604469608844835084213394087159/11258999068426240000000000000000000), (1033937778805511624409203322124061/11258999068426240000000000000000000), (-37942788290238168116287394897997/703687441776640000000000000000000), (85552215909530862751762494212243/11258999068426240000000000000000000), (2825720157685569630452654340453/5629499534213120000000000000000000), (-451463005337786245303301608799/2251799813685248000000000000000000), (36503023334710347005803705659/11258999068426240000000000000000000), (25908683598865436183132976883/11258999068426240000000000000000000), (-1113251943822404902379464651/11258999068426240000000000000000000), (-179505651051811459565250021/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial130.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial130.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial130.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial130 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 15206036164503937053483362375507100), (Int.negOfNat 350389024823893346929305359952851), (Int.negOfNat 115231530755850387803344005950437), (Int.ofNat 58051192764780126460339811689247), (Int.negOfNat 9278308342289824124287054406656), (Int.negOfNat 400094029647876619625430136641), (Int.ofNat 197943899345493778528427386949), (Int.negOfNat 4867476623683896316783801603), (Int.negOfNat 1871788002284741475543672901), (Int.ofNat 95284485991847269543556763), (Int.ofNat 10765042895863170127251496), (Int.negOfNat 752139386184618940275292), (Int.negOfNat 42366733790279651243595), (Int.ofNat 3748577364051394505411), (Int.ofNat 120974079514999751155), (Int.negOfNat 13865491344238450372), (Int.negOfNat 220230327730758388), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(152060361645039370534833623755071/112589990684262400000000000000000), (-350389024823893346929305359952851/11258999068426240000000000000000000), (-115231530755850387803344005950437/11258999068426240000000000000000000), (58051192764780126460339811689247/11258999068426240000000000000000000), (-9060847990517406371374076569/10995116277760000000000000000000), (-400094029647876619625430136641/11258999068426240000000000000000000), (197943899345493778528427386949/11258999068426240000000000000000000), (-4867476623683896316783801603/11258999068426240000000000000000000), (-1871788002284741475543672901/11258999068426240000000000000000000), (95284485991847269543556763/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial130.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial130.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial130.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial130 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 14359109913726124589018339548607598), (Int.negOfNat 409440986520931104172131457220303), (Int.ofNat 19809723354819624340527875674527), (Int.negOfNat 5945822087636452414117421407454), (Int.negOfNat 4368722813000117889428979689348), (Int.ofNat 981488965144491608365368958862), (Int.ofNat 7616688430814177764228876301), (Int.negOfNat 15363624510012424781734731430), (Int.ofNat 618928954606850762490327064), (Int.ofNat 116760240108278483173614729), (Int.negOfNat 7776694997198579769035820), (Int.negOfNat 546135575234328661927274), (Int.ofNat 50106773419300062355530), (Int.ofNat 1720107434732500163562), (Int.negOfNat 214883344661699064542), (Int.negOfNat 3644215253661533152), (Int.ofNat 778038108737362270), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(7179554956863062294509169774303799/5629499534213120000000000000000000), (-409440986520931104172131457220303/11258999068426240000000000000000000), (19809723354819624340527875674527/11258999068426240000000000000000000), (-2972911043818226207058710703727/5629499534213120000000000000000000), (-1092180703250029472357244922337/2814749767106560000000000000000000), (490744482572245804182684479431/5629499534213120000000000000000000), (7616688430814177764228876301/11258999068426240000000000000000000), (-1536362451001242478173473143/1125899906842624000000000000000000), (77366119325856345311290883/1407374883553280000000000000000000), (116760240108278483173614729/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial130.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial130.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial130.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial130 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 13532138624365359984003659271097839), (Int.negOfNat 467394342258746784088986257950981), (Int.negOfNat 49146025540361078933651918292420), (Int.negOfNat 7420716899609292234343703921863), (Int.ofNat 2644497012849350923078759935448), (Int.ofNat 221574835411712066393929643289), (Int.negOfNat 90723179046433328312189551590), (Int.ofNat 2365714785107966203499035783), (Int.ofNat 1025442065594861857086149867), (Int.negOfNat 65037142876400367127552558), (Int.negOfNat 6086645370487928454495507), (Int.ofNat 577980110742724925427596), (Int.ofNat 21875291193531401961925), (Int.negOfNat 3061325582447897634026), (Int.negOfNat 46682770029017293050), (Int.ofNat 11881679251035850872), (Int.ofNat 6569142169493908), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(13532138624365359984003659271097839/11258999068426240000000000000000000), (-467394342258746784088986257950981/11258999068426240000000000000000000), (-2457301277018053946682595914621/562949953421312000000000000000000), (-7420716899609292234343703921863/11258999068426240000000000000000000), (330562126606168865384844991931/1407374883553280000000000000000000), (221574835411712066393929643289/11258999068426240000000000000000000), (-9072317904643332831218955159/1125899906842624000000000000000000), (2365714785107966203499035783/11258999068426240000000000000000000), (1025442065594861857086149867/11258999068426240000000000000000000), (-32518571438200183563776279/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial130.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial130.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial130.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial130 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 12385523206702848779300562998609095), (Int.negOfNat 666160240380506572144573410959966), (Int.negOfNat 31175174315243292493842903271537), (Int.ofNat 10827772704162166256558108821559), (Int.ofNat 909763408613992177780975922870), (Int.negOfNat 370898461812481424658327557380), (Int.ofNat 2248300324403676812543131869), (Int.ofNat 6831570696203262257269795080), (Int.negOfNat 430779790555677552124708778), (Int.negOfNat 55686016107730402941897434), (Int.ofNat 5672082143122346574747914), (Int.ofNat 239016880511993617379659), (Int.negOfNat 38314287380592043681311), (Int.negOfNat 510101423900016177345), (Int.ofNat 167944997779539500864), (Int.negOfNat 225853397911260308), (Int.negOfNat 690584303351770676), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(2477104641340569755860112599721819/2251799813685248000000000000000000), (-333080120190253286072286705479983/5629499534213120000000000000000000), (-31175174315243292493842903271537/11258999068426240000000000000000000), (10827772704162166256558108821559/11258999068426240000000000000000000), (90976340861399217778097592287/1125899906842624000000000000000000), (-18544923090624071232916377869/562949953421312000000000000000000), (2248300324403676812543131869/11258999068426240000000000000000000), (170789267405081556431744877/281474976710656000000000000000000), (-215389895277838776062354389/5629499534213120000000000000000000), (-27843008053865201470948717/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial130.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial130.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial130.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial130 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 11018697354812897664010558581472997), (Int.negOfNat 658533531153672245609382647786015), (Int.ofNat 30125219897200756596252669643566), (Int.ofNat 6476901353357220534624158915294), (Int.negOfNat 1377026659886727824910118886601), (Int.negOfNat 26396158270237362629286768768), (Int.ofNat 32561505601551502642583459423), (Int.negOfNat 2328415851385540249400173528), (Int.negOfNat 390362171888270943741615222), (Int.ofNat 47136991934890982153358486), (Int.ofNat 2093964400085176943779878), (Int.negOfNat 416806391945764093486425), (Int.negOfNat 3887382925681249424337), (Int.ofNat 2239560811527062161879), (Int.negOfNat 15946077076319968672), (Int.negOfNat 8677639442407133484), (Int.ofNat 125049374739013456), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(11018697354812897664010558581472997/11258999068426240000000000000000000), (-131706706230734449121876529557203/2251799813685248000000000000000000), (15062609948600378298126334821783/5629499534213120000000000000000000), (3238450676678610267312079457647/5629499534213120000000000000000000), (-1377026659886727824910118886601/11258999068426240000000000000000000), (-206219986486229395541302881/87960930222080000000000000000000), (32561505601551502642583459423/11258999068426240000000000000000000), (-291051981423192531175021691/1407374883553280000000000000000000), (-195181085944135471870807611/5629499534213120000000000000000000), (23568495967445491076679243/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial130.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial130.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial130.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial130 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 9852780672354871037406966643964627), (Int.negOfNat 501562783418958686553465829334524), (Int.ofNat 39606507220357206669661810398880), (Int.negOfNat 2120601755251502852621950183280), (Int.negOfNat 575577344878714644182104383423), (Int.ofNat 93766341120170224663444109658), (Int.negOfNat 10976891142631121125714161082), (Int.negOfNat 1848982570036216098250158613), (Int.ofNat 337105128528117106037350169), (Int.ofNat 12748184896406731708641342), (Int.negOfNat 3911182156399858112331153), (Int.negOfNat 4838678695243653570488), (Int.ofNat 25920074532267306755395), (Int.negOfNat 422204368848334641022), (Int.negOfNat 113850883247267774522), (Int.ofNat 3154699119513644200), (Int.ofNat 537321239511925400), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(9852780672354871037406966643964627/11258999068426240000000000000000000), (-125390695854739671638366457333631/2814749767106560000000000000000000), (247540670127232541685386314993/70368744177664000000000000000000), (-26507521940643785657774377291/140737488355328000000000000000000), (-575577344878714644182104383423/11258999068426240000000000000000000), (46883170560085112331722054829/5629499534213120000000000000000000), (-5488445571315560562857080541/5629499534213120000000000000000000), (-1848982570036216098250158613/11258999068426240000000000000000000), (337105128528117106037350169/11258999068426240000000000000000000), (6374092448203365854320671/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial130.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial130.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial130.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial130 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 8984057326932549319091957042557516), (Int.negOfNat 382081960591380700929910803936316), (Int.ofNat 17312665459980560008702925396755), (Int.negOfNat 5151235298952529175362512473371), (Int.negOfNat 435031024737681943017264496014), (Int.negOfNat 45846684221274456674305904148), (Int.negOfNat 2390602030775286344597157345), (Int.ofNat 2167345789876551146175057642), (Int.ofNat 25629967675739502766527656), (Int.negOfNat 31655557611801854768458927), (Int.ofNat 470833237020218179171980), (Int.ofNat 257927297586743174381618), (Int.negOfNat 8128004520217400250078), (Int.negOfNat 1343431399107518766574), (Int.ofNat 58437303264791835270), (Int.ofNat 4705533079258709824), (Int.negOfNat 180036359727598182), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(2246014331733137329772989260639379/2814749767106560000000000000000000), (-95520490147845175232477700984079/2814749767106560000000000000000000), (3462533091996112001740585079351/2251799813685248000000000000000000), (-5151235298952529175362512473371/11258999068426240000000000000000000), (-217515512368840971508632248007/5629499534213120000000000000000000), (-11461671055318614168576476037/2814749767106560000000000000000000), (-478120406155057268919431469/2251799813685248000000000000000000), (1083672894938275573087528821/5629499534213120000000000000000000), (3203745959467437845815957/1407374883553280000000000000000000), (-31655557611801854768458927/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial130.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial130.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial130.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial130 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 8239622337404396114376248953150205), (Int.negOfNat 391764511630898642021466869056932), (Int.negOfNat 26908505545468996077823072834019), (Int.negOfNat 9741516791592454747698803065727), (Int.negOfNat 513235737782261894198683483950), (Int.ofNat 65415366809137698625405372971), (Int.ofNat 14223853233050696756517222859), (Int.negOfNat 489144905449393410753826659), (Int.negOfNat 224575239664583621372731947), (Int.ofNat 9641969123753072118626607), (Int.ofNat 2162846869530735811870896), (Int.negOfNat 124260265993845251503172), (Int.negOfNat 13230796751677807270657), (Int.ofNat 931287175332674818431), (Int.ofNat 54437942628650993633), (Int.negOfNat 4597397539432795900), (Int.negOfNat 323660053950660920), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(1647924467480879222875249790630041/2251799813685248000000000000000000), (-97941127907724660505366717264233/2814749767106560000000000000000000), (-26908505545468996077823072834019/11258999068426240000000000000000000), (-9741516791592454747698803065727/11258999068426240000000000000000000), (-10264714755645237883973669679/225179981368524800000000000000000), (65415366809137698625405372971/11258999068426240000000000000000000), (14223853233050696756517222859/11258999068426240000000000000000000), (-489144905449393410753826659/11258999068426240000000000000000000), (-224575239664583621372731947/11258999068426240000000000000000000), (9641969123753072118626607/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial130.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial130.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial130.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial130 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 7265205753512478702343841384900561), (Int.negOfNat 625173552865157857790705038327563), (Int.negOfNat 89694335877404158146756851506446), (Int.negOfNat 9552708833550521680266358274612), (Int.ofNat 667268230800039187543765383807), (Int.ofNat 126616337162489380797679239185), (Int.negOfNat 6414997229450042768838197281), (Int.negOfNat 1490563507700667720512185293), (Int.ofNat 114356429899574701344552935), (Int.ofNat 14864112503530373267126107), (Int.negOfNat 1531927487548406642211748), (Int.negOfNat 100390335316428740460926), (Int.ofNat 12905600573034575085945), (Int.ofNat 449803899840094928329), (Int.negOfNat 71358321333837415819), (Int.negOfNat 1059276408398999964), (Int.ofNat 163802949529094748), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(7265205753512478702343841384900561/11258999068426240000000000000000000), (-625173552865157857790705038327563/11258999068426240000000000000000000), (-44847167938702079073378425753223/5629499534213120000000000000000000), (-2388177208387630420066589568653/2814749767106560000000000000000000), (667268230800039187543765383807/11258999068426240000000000000000000), (25323267432497876159535847837/2251799813685248000000000000000000), (-6414997229450042768838197281/11258999068426240000000000000000000), (-1490563507700667720512185293/11258999068426240000000000000000000), (22871285979914940268910587/2251799813685248000000000000000000), (14864112503530373267126107/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial130.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial130.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial130.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial130 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 5593821462834361983582230006038708), (Int.negOfNat 1068858257748256890728676302666474), (Int.negOfNat 123154240353447998341984665101296), (Int.negOfNat 752429427745155605065956249247), (Int.ofNat 1296079527613606272375678544866), (Int.negOfNat 8314615565322538703528547290), (Int.negOfNat 10312678190548245140790972933), (Int.ofNat 822921069019606289339572718), (Int.ofNat 80281252781239371908135380), (Int.negOfNat 14658332802428040983432081), (Int.negOfNat 449277213273057416799424), (Int.ofNat 148296427022890515954280), (Int.ofNat 1261245726074056929454), (Int.negOfNat 976196742788000766588), (Int.ofNat 512272006270862896), (Int.ofNat 4604865782144515444), (Int.ofNat 109998868389396440), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(1398455365708590495895557501509677/2814749767106560000000000000000000), (-534429128874128445364338151333237/5629499534213120000000000000000000), (-7697140022090499896374041568831/703687441776640000000000000000000), (-752429427745155605065956249247/11258999068426240000000000000000000), (648039763806803136187839272433/5629499534213120000000000000000000), (-831461556532253870352854729/1125899906842624000000000000000000), (-10312678190548245140790972933/11258999068426240000000000000000000), (411460534509803144669786359/5629499534213120000000000000000000), (4014062639061968595406769/562949953421312000000000000000000), (-14658332802428040983432081/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial130.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial130.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial130.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial130 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 2977397965664018920019487168501008), (Int.negOfNat 1531258576634198486526662497123111), (Int.negOfNat 99074864893627959059023229702256), (Int.ofNat 8158718861998779388100188521660), (Int.ofNat 855445067317192474232496456800), (Int.negOfNat 55943742592901287543869879723), (Int.ofNat 904373235639567952460126152), (Int.ofNat 280653033692565085639600437), (Int.negOfNat 95204935917592335599160829), (Int.ofNat 1429967040835015253870374), (Int.ofNat 1316396522808326671287097), (Int.negOfNat 38892419827627612684864), (Int.negOfNat 10750340302995000346563), (Int.ofNat 336761898981150776098), (Int.ofNat 58748852031058268236), (Int.negOfNat 2336316737429844016), (Int.negOfNat 147569539330591314), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(186087372854001182501217948031313/703687441776640000000000000000000), (-1531258576634198486526662497123111/11258999068426240000000000000000000), (-6192179055851747441188951856391/703687441776640000000000000000000), (407935943099938969405009426083/562949953421312000000000000000000), (1069306334146490592790620571/14073748835532800000000000000000), (-55943742592901287543869879723/11258999068426240000000000000000000), (113046654454945994057515769/1407374883553280000000000000000000), (280653033692565085639600437/11258999068426240000000000000000000), (-95204935917592335599160829/11258999068426240000000000000000000), (714983520417507626935187/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial130.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial130.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial130.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial130 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 404180583848136589399738711266061), (Int.negOfNat 1806543428246279362359115453883090), (Int.negOfNat 33812321956538470471014809095063), (Int.ofNat 12920980047585844235586261134283), (Int.ofNat 342853767483558102095285678836), (Int.negOfNat 52745417831398124187219656936), (Int.negOfNat 1542860749610520737414716765), (Int.negOfNat 191897722562302968756184160), (Int.ofNat 54131277828377539630545970), (Int.ofNat 7070855352187597158237706), (Int.negOfNat 926378918256277868383264), (Int.negOfNat 83432743216854239499265), (Int.ofNat 8230532862652655119853), (Int.ofNat 596940699091018306171), (Int.negOfNat 46604054137978136148), (Int.negOfNat 3136133378978431806), (Int.ofNat 98251180439033562), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-404180583848136589399738711266061/11258999068426240000000000000000000), (-180654342824627936235911545388309/1125899906842624000000000000000000), (-33812321956538470471014809095063/11258999068426240000000000000000000), (12920980047585844235586261134283/11258999068426240000000000000000000), (85713441870889525523821419709/2814749767106560000000000000000000), (-6593177228924765523402457117/1407374883553280000000000000000000), (-308572149922104147482943353/2251799813685248000000000000000000), (-1199360766014393554726151/70368744177664000000000000000000), (5413127782837753963054597/1125899906842624000000000000000000), (3535427676093798579118853/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial130.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial130.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial130.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial130 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 4045457990714371205722300825484025), (Int.negOfNat 1780305200879483204610792345736985), (Int.ofNat 47340369981824737549984912492963), (Int.ofNat 13317998437597544003304238838003), (Int.negOfNat 256534390641836351227104804894), (Int.negOfNat 57834652182521918093139103338), (Int.ofNat 2815002870569433750817867005), (Int.ofNat 612662385883985259973740580), (Int.negOfNat 16353970062331094949637270), (Int.negOfNat 12095761125005146019140094), (Int.negOfNat 135293193763760988796896), (Int.ofNat 132739293310207620674055), (Int.ofNat 2895071188237637159587), (Int.negOfNat 887552427736284142949), (Int.negOfNat 22613481954934869412), (Int.ofNat 4343165399896486274), (Int.negOfNat 5693524509253962), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-161818319628574848228892033019361/450359962737049600000000000000000), (-356061040175896640922158469147397/2251799813685248000000000000000000), (47340369981824737549984912492963/11258999068426240000000000000000000), (13317998437597544003304238838003/11258999068426240000000000000000000), (-128267195320918175613552402447/5629499534213120000000000000000000), (-28917326091260959046569551669/5629499534213120000000000000000000), (563000574113886750163573401/2251799813685248000000000000000000), (30633119294199262998687029/562949953421312000000000000000000), (-1635397006233109494963727/1125899906842624000000000000000000), (-6047880562502573009570047/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial130.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial130.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial130.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial130 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 7315869845174945992905181825180656), (Int.negOfNat 1443192449351163359535260310078162), (Int.ofNat 117469257794300266320653574265614), (Int.ofNat 9655081629971080392052947871296), (Int.negOfNat 557702440021325466845666311055), (Int.negOfNat 1477618048004546143764519650), (Int.ofNat 2910050374882635841662109208), (Int.negOfNat 846730111777649641813938783), (Int.negOfNat 97631354864231430938484451), (Int.ofNat 9272314654887734189204174), (Int.ofNat 1567673697716011118961103), (Int.negOfNat 48081902622442108197344), (Int.negOfNat 13368285941903610316037), (Int.ofNat 114466971236085192378), (Int.ofNat 72792014313758503124), (Int.ofNat 592808293612951344), (Int.negOfNat 229869697347540926), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-457241865323434124556573864073791/703687441776640000000000000000000), (-721596224675581679767630155039081/5629499534213120000000000000000000), (58734628897150133160326787132807/5629499534213120000000000000000000), (150860650468298131125827310489/175921860444160000000000000000000), (-111540488004265093369133262211/2251799813685248000000000000000000), (-29552360960090922875290393/225179981368524800000000000000000), (363756296860329480207763651/1407374883553280000000000000000000), (-846730111777649641813938783/11258999068426240000000000000000000), (-97631354864231430938484451/11258999068426240000000000000000000), (4636157327443867094602087/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial130.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial130.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial130.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial130 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 9664048512728209813613551468737973), (Int.negOfNat 875311171995003954497708042805468), (Int.ofNat 161909707485403222689698362216872), (Int.ofNat 5021318429008401248626036575874), (Int.negOfNat 689462047676044924531935173802), (Int.negOfNat 52753326849364314702858496724), (Int.negOfNat 9802841204082245602556114847), (Int.negOfNat 118237266184200466919826742), (Int.ofNat 199993224249247072091525420), (Int.ofNat 12128553105271617524849699), (Int.negOfNat 1719178841640103475459876), (Int.negOfNat 155959586759844345339480), (Int.ofNat 8950832698038672494786), (Int.ofNat 1089594536683962154092), (Int.negOfNat 31836366899641449136), (Int.negOfNat 5145554098575704236), (Int.ofNat 224765846803352920), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-9664048512728209813613551468737973/11258999068426240000000000000000000), (-218827792998750988624427010701367/2814749767106560000000000000000000), (20238713435675402836212295277109/1407374883553280000000000000000000), (2510659214504200624313018287937/5629499534213120000000000000000000), (-344731023838022462265967586901/5629499534213120000000000000000000), (-13188331712341078675714624181/2814749767106560000000000000000000), (-9802841204082245602556114847/11258999068426240000000000000000000), (-59118633092100233459913371/5629499534213120000000000000000000), (9999661212462353604576271/562949953421312000000000000000000), (12128553105271617524849699/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial130.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial130.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial130.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial130 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 10740168121613148896852478349309134), (Int.negOfNat 195412236814572981779537885963210), (Int.ofNat 169228968201513308459332741737219), (Int.negOfNat 3847286524164390666993266559649), (Int.negOfNat 1593582855562648464930278225453), (Int.negOfNat 83525897526349924685266957111), (Int.ofNat 11742243271166527506500606323), (Int.ofNat 2679641698564796991945767387), (Int.ofNat 9089066263354372668270405), (Int.negOfNat 31740649901292394240400913), (Int.negOfNat 1198294009819778566590912), (Int.ofNat 220904112638032755098874), (Int.ofNat 12741476380376735387415), (Int.negOfNat 1026222382032260129471), (Int.negOfNat 74658925109314608221), (Int.ofNat 3133638079267020676), (Int.ofNat 213636287149037492), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-5370084060806574448426239174654567/5629499534213120000000000000000000), (-19541223681457298177953788596321/1125899906842624000000000000000000), (169228968201513308459332741737219/11258999068426240000000000000000000), (-3847286524164390666993266559649/11258999068426240000000000000000000), (-1593582855562648464930278225453/11258999068426240000000000000000000), (-83525897526349924685266957111/11258999068426240000000000000000000), (11742243271166527506500606323/11258999068426240000000000000000000), (2679641698564796991945767387/11258999068426240000000000000000000), (1817813252670874533654081/2251799813685248000000000000000000), (-31740649901292394240400913/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial130.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial130.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial130.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial130 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 10511945327704027292978067590074558), (Int.ofNat 381047245314958237128641022764116), (Int.ofNat 105699161997751330073855131121429), (Int.negOfNat 16719965654467244054845475094904), (Int.negOfNat 1097406703087859482523083854889), (Int.ofNat 220311783717020474793897136527), (Int.ofNat 28666290685495816162660389901), (Int.negOfNat 1545225815291639498484423079), (Int.negOfNat 438489615648539334044232673), (Int.ofNat 216934729620200908019667), (Int.ofNat 3923398495896907905061064), (Int.ofNat 93783753412917477420108), (Int.negOfNat 22779888817438597635023), (Int.negOfNat 877454884131763457929), (Int.ofNat 91893636057695884447), (Int.ofNat 4575327635649198980), (Int.negOfNat 438427032364617400), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-5255972663852013646489033795037279/5629499534213120000000000000000000), (95261811328739559282160255691029/2814749767106560000000000000000000), (105699161997751330073855131121429/11258999068426240000000000000000000), (-2089995706808405506855684386863/1407374883553280000000000000000000), (-1097406703087859482523083854889/11258999068426240000000000000000000), (220311783717020474793897136527/11258999068426240000000000000000000), (28666290685495816162660389901/11258999068426240000000000000000000), (-1545225815291639498484423079/11258999068426240000000000000000000), (-438489615648539334044232673/11258999068426240000000000000000000), (216934729620200908019667/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial130.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial130.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial130.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial130 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 9469793622284191141458772493695967), (Int.ofNat 590095935910562627601526160066706), (Int.ofNat 1769490633348448928998934680531), (Int.negOfNat 13688597265955406795947616984712), (Int.ofNat 1956380634033181088721087530771), (Int.ofNat 270420894655159978932355968196), (Int.negOfNat 28822668018325928617086165915), (Int.negOfNat 4895732794278190798398186538), (Int.ofNat 199276473094070616914662464), (Int.ofNat 56071209455668409156855693), (Int.negOfNat 292388411284540194983860), (Int.negOfNat 406710436176067362526702), (Int.negOfNat 5705376899564821308922), (Int.ofNat 1995682607483835255226), (Int.ofNat 52422898718659458330), (Int.negOfNat 6894302507864479456), (Int.negOfNat 197402876950534058), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-9469793622284191141458772493695967/11258999068426240000000000000000000), (295047967955281313800763080033353/5629499534213120000000000000000000), (1769490633348448928998934680531/11258999068426240000000000000000000), (-1711074658244425849493452123089/1407374883553280000000000000000000), (1956380634033181088721087530771/11258999068426240000000000000000000), (67605223663789994733088992049/2814749767106560000000000000000000), (-5764533603665185723417233183/2251799813685248000000000000000000), (-2447866397139095399199093269/5629499534213120000000000000000000), (3113694892094853389291601/175921860444160000000000000000000), (56071209455668409156855693/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial130.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial130.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial130.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial130 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 8354469727357690980795093568597322), (Int.ofNat 509748481713119506938611820005341), (Int.negOfNat 21382054474451926825836179146043), (Int.ofNat 6062884650184585206556195311908), (Int.ofNat 1988623699956477555186866170862), (Int.negOfNat 298651653932383595423897660639), (Int.negOfNat 44238036842449138887857293838), (Int.ofNat 4023541644482634853201016627), (Int.ofNat 659677614375587628743401871), (Int.negOfNat 25632617801188640692886298), (Int.negOfNat 6101177184529329912466627), (Int.ofNat 58647908592096397096112), (Int.ofNat 36599001027384677882605), (Int.ofNat 242543602913873622498), (Int.negOfNat 153037857611289827198), (Int.negOfNat 2591515542446599480), (Int.ofNat 652088217925881880), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-4177234863678845490397546784298661/5629499534213120000000000000000000), (509748481713119506938611820005341/11258999068426240000000000000000000), (-21382054474451926825836179146043/11258999068426240000000000000000000), (1515721162546146301639048827977/2814749767106560000000000000000000), (994311849978238777593433085431/5629499534213120000000000000000000), (-298651653932383595423897660639/11258999068426240000000000000000000), (-22119018421224569443928646919/5629499534213120000000000000000000), (4023541644482634853201016627/11258999068426240000000000000000000), (659677614375587628743401871/11258999068426240000000000000000000), (-12816308900594320346443149/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial130.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial130.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial130.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial130 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 7351903223951473932725349995091750), (Int.ofNat 530614318753603138452654748038956), (Int.ofNat 31914628486017952182911781637809), (Int.ofNat 6158087538656070864771483681102), (Int.negOfNat 1965050808878864519254996832291), (Int.negOfNat 291505779602295541649142262622), (Int.ofNat 51215208852734757884289554297), (Int.ofNat 6225654042675154777343535752), (Int.negOfNat 552469010808923825423823158), (Int.negOfNat 77439119214032800644429554), (Int.ofNat 2969594264434874297845802), (Int.ofNat 581766790814487264606255), (Int.negOfNat 7516231400422960015503), (Int.negOfNat 2905941593143187361361), (Int.negOfNat 3231898838792850528), (Int.ofNat 10764371159437272916), (Int.ofNat 109949071564942464), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-29407612895805895730901399980367/45035996273704960000000000000000), (132653579688400784613163687009739/2814749767106560000000000000000000), (31914628486017952182911781637809/11258999068426240000000000000000000), (3079043769328035432385741840551/5629499534213120000000000000000000), (-1965050808878864519254996832291/11258999068426240000000000000000000), (-145752889801147770824571131311/5629499534213120000000000000000000), (51215208852734757884289554297/11258999068426240000000000000000000), (778206755334394347167941969/1407374883553280000000000000000000), (-276234505404461912711911579/5629499534213120000000000000000000), (-38719559607016400322214777/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial130.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial130.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial130.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial130 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 6150622615882649136290180133396140), (Int.ofNat 657867480040954945626786136883962), (Int.ofNat 13559525334718508275692070007753), (Int.negOfNat 10879581752315564962914150630601), (Int.negOfNat 932518339512840339587226326155), (Int.ofNat 481865869853911024175171933764), (Int.ofNat 41978727482881026672722383451), (Int.negOfNat 8336521055605386186622870640), (Int.negOfNat 815217052348121719208800642), (Int.ofNat 66562169835243188762766926), (Int.ofNat 8064507325981943625573606), (Int.negOfNat 295742826794317352400261), (Int.negOfNat 49046209190437728820049), (Int.ofNat 749141242096242430615), (Int.ofNat 204761731780406939136), (Int.negOfNat 612524266182117908), (Int.negOfNat 783706734834389244), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-307531130794132456814509006669807/562949953421312000000000000000000), (328933740020477472813393068441981/5629499534213120000000000000000000), (13559525334718508275692070007753/11258999068426240000000000000000000), (-10879581752315564962914150630601/11258999068426240000000000000000000), (-186503667902568067917445265231/2251799813685248000000000000000000), (120466467463477756043792983441/2814749767106560000000000000000000), (41978727482881026672722383451/11258999068426240000000000000000000), (-104206513195067327332785883/140737488355328000000000000000000), (-407608526174060859604400321/5629499534213120000000000000000000), (33281084917621594381383463/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial130.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial130.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial130.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial130 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 4865734385020047424844880047798838), (Int.ofNat 593939830968064842466374313477418), (Int.negOfNat 32149078955470954415303032995393), (Int.ofNat 1986242897740571578683199477633), (Int.ofNat 3516131842931574524168602240481), (Int.ofNat 106080396160155339171296372446), (Int.negOfNat 101167267579309646505802123790), (Int.negOfNat 6689851496125024777673301677), (Int.ofNat 1123437647954256560583411993), (Int.ofNat 97081264626582222974224502), (Int.negOfNat 6764599293604418062236213), (Int.negOfNat 740350565507130718530404), (Int.ofNat 25478661077063753205875), (Int.ofNat 3671846026074458987094), (Int.negOfNat 61851492642008454030), (Int.negOfNat 13693216881039656808), (Int.ofNat 43313992274902812), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-2432867192510023712422440023899419/5629499534213120000000000000000000), (296969915484032421233187156738709/5629499534213120000000000000000000), (-32149078955470954415303032995393/11258999068426240000000000000000000), (1986242897740571578683199477633/11258999068426240000000000000000000), (3516131842931574524168602240481/11258999068426240000000000000000000), (53040198080077669585648186223/5629499534213120000000000000000000), (-10116726757930964650580212379/1125899906842624000000000000000000), (-6689851496125024777673301677/11258999068426240000000000000000000), (1123437647954256560583411993/11258999068426240000000000000000000), (48540632313291111487112251/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial130.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial130.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial130.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial130 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 3737910424237210316151296426519026), (Int.ofNat 589091824345223035498712337741954), (Int.ofNat 46230298169348527707251964139458), (Int.ofNat 16829240818416785758519133936401), (Int.negOfNat 1834292680152370349294390080955), (Int.negOfNat 1043609486221664527681703680174), (Int.negOfNat 35203189127855791991892941941), (Int.ofNat 15862723793348248023226397990), (Int.ofNat 1006856795258246032755317916), (Int.negOfNat 122119509581855098463079551), (Int.negOfNat 10058683299313822544358000), (Int.ofNat 587314565522741709703206), (Int.ofNat 59671550854768828469870), (Int.negOfNat 1944576061866010455438), (Int.negOfNat 245126760989635904258), (Int.ofNat 4584630629330541568), (Int.ofNat 838693719822973970), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-1868955212118605158075648213259513/5629499534213120000000000000000000), (294545912172611517749356168870977/5629499534213120000000000000000000), (23115149084674263853625982069729/5629499534213120000000000000000000), (16829240818416785758519133936401/11258999068426240000000000000000000), (-366858536030474069858878016191/2251799813685248000000000000000000), (-521804743110832263840851840087/5629499534213120000000000000000000), (-35203189127855791991892941941/11258999068426240000000000000000000), (1586272379334824802322639799/1125899906842624000000000000000000), (251714198814561508188829479/2814749767106560000000000000000000), (-122119509581855098463079551/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial130.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial130.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial130.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial130 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 2302952060664154746710935947876605), (Int.ofNat 834831379590886486705476447858588), (Int.ofNat 23050804643836427188923082950522), (Int.negOfNat 35314804059393250882330145867357), (Int.negOfNat 9409486140202085888869879933017), (Int.ofNat 12730476379364401399586966097), (Int.ofNat 195395166849969743303999225413), (Int.ofNat 9034745941771224192610443277), (Int.negOfNat 1875083207162412493684775579), (Int.negOfNat 124518299295655652593102877), (Int.ofNat 11032615562983247608202244), (Int.ofNat 892237482864037500015188), (Int.negOfNat 44855589192903220566725), (Int.negOfNat 4234807638709983248749), (Int.ofNat 134390445189936393165), (Int.ofNat 15135915300958808508), (Int.negOfNat 256975177836167292), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-460590412132830949342187189575321/2251799813685248000000000000000000), (208707844897721621676369111964647/2814749767106560000000000000000000), (11525402321918213594461541475261/5629499534213120000000000000000000), (-35314804059393250882330145867357/11258999068426240000000000000000000), (-9409486140202085888869879933017/11258999068426240000000000000000000), (12730476379364401399586966097/11258999068426240000000000000000000), (195395166849969743303999225413/11258999068426240000000000000000000), (9034745941771224192610443277/11258999068426240000000000000000000), (-1875083207162412493684775579/11258999068426240000000000000000000), (-124518299295655652593102877/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial130.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial130.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial130.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial130 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 960618045974337504850023047747114), (Int.ofNat 242593521919132527399000933472914), (Int.negOfNat 364466414307517832081096884878634), (Int.negOfNat 77587367639082294062700140122954), (Int.ofNat 2548013839700286516670749153789), (Int.ofNat 2134909919019359515211778986901), (Int.ofNat 75010928502593843649778145459), (Int.negOfNat 25116189619660212794031041637), (Int.negOfNat 1446011698456810795035409189), (Int.ofNat 177672846387987310019597359), (Int.ofNat 12449582274597008615225004), (Int.negOfNat 863568557870116827752650), (Int.negOfNat 68144714329780763037551), (Int.ofNat 3102211154823745469277), (Int.ofNat 266858169020274768777), (Int.negOfNat 8230887300190251428), (Int.negOfNat 822460309624470536), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-480309022987168752425011523873557/5629499534213120000000000000000000), (121296760959566263699500466736457/5629499534213120000000000000000000), (-182233207153758916040548442439317/5629499534213120000000000000000000), (-38793683819541147031350070061477/5629499534213120000000000000000000), (2548013839700286516670749153789/11258999068426240000000000000000000), (2134909919019359515211778986901/11258999068426240000000000000000000), (75010928502593843649778145459/11258999068426240000000000000000000), (-25116189619660212794031041637/11258999068426240000000000000000000), (-1446011698456810795035409189/11258999068426240000000000000000000), (177672846387987310019597359/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial130.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial130.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial130.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial130 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 2443592914860426464479487761062618), (Int.negOfNat 1891860089806523755586847664609591), (Int.negOfNat 598578405727108217675002890565036), (Int.ofNat 24641899206183373085803532418415), (Int.ofNat 20585669157941342565064079506934), (Int.ofNat 704870257106843337427439512314), (Int.negOfNat 293280482487874617289864526325), (Int.negOfNat 16563004493048860970355036538), (Int.ofNat 2483058276054449524021161284), (Int.ofNat 165566637033667530059889643), (Int.negOfNat 14336880428751349591356680), (Int.negOfNat 1031711512302664525707104), (Int.ofNat 60782732767665386881154), (Int.ofNat 4538184018394217137432), (Int.negOfNat 198045669771064748124), (Int.negOfNat 15143383543670528052), (Int.ofNat 470636363397431772), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-1221796457430213232239743880531309/5629499534213120000000000000000000), (-1891860089806523755586847664609591/11258999068426240000000000000000000), (-149644601431777054418750722641259/2814749767106560000000000000000000), (4928379841236674617160706483683/2251799813685248000000000000000000), (10292834578970671282532039753467/5629499534213120000000000000000000), (352435128553421668713719756157/5629499534213120000000000000000000), (-11731219299514984691594581053/450359962737049600000000000000000), (-8281502246524430485177518269/5629499534213120000000000000000000), (620764569013612381005290321/2814749767106560000000000000000000), (165566637033667530059889643/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial130.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial130.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial130.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial130 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 8092751062867218143273812510702389), (Int.negOfNat 3336229166775513607736981334106815), (Int.ofNat 23224119888553399176903976676349), (Int.ofNat 166405838264344443588784440614123), (Int.ofNat 8621347252079133625438969039242), (Int.negOfNat 2898300601199668544227871664627), (Int.negOfNat 194818597774011885058552761212), (Int.ofNat 29727383691803140811978799385), (Int.ofNat 2140683829646531778316986119), (Int.negOfNat 205811479659504943030399154), (Int.negOfNat 14880406986674812654143719), (Int.ofNat 1034112337013964059764756), (Int.ofNat 72826912837260273209777), (Int.negOfNat 3951735838209280030938), (Int.negOfNat 267395787649884136548), (Int.ofNat 11626480446019095408), (Int.ofNat 806226899425967102), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-8092751062867218143273812510702389/11258999068426240000000000000000000), (-667245833355102721547396266821363/2251799813685248000000000000000000), (23224119888553399176903976676349/11258999068426240000000000000000000), (166405838264344443588784440614123/11258999068426240000000000000000000), (4310673626039566812719484519621/5629499534213120000000000000000000), (-2898300601199668544227871664627/11258999068426240000000000000000000), (-48704649443502971264638190303/2814749767106560000000000000000000), (5945476738360628162395759877/2251799813685248000000000000000000), (2140683829646531778316986119/11258999068426240000000000000000000), (-102905739829752471515199577/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial130.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial130.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial130.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial130 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 13304103777200448576221018407988098), (Int.negOfNat 1224875983746096663573033457434945), (Int.ofNat 972677401048981828219470602356020), (Int.ofNat 107472604513657059360975170593159), (Int.negOfNat 22308138206566871520160225295647), (Int.negOfNat 2278482173337569702632845816514), (Int.ofNat 291375607267568609620583705929), (Int.ofNat 26834257399270534983229913196), (Int.negOfNat 2502746489919723312398752526), (Int.negOfNat 205339371125286731046440662), (Int.ofNat 15224665760294648775286592), (Int.ofNat 1109279138133501554694511), (Int.negOfNat 68942070918326111962535), (Int.negOfNat 4469673972805228075617), (Int.ofNat 241884798905064977252), (Int.ofNat 13674651140504444414), (Int.negOfNat 678886412225861774), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-6652051888600224288110509203994049/5629499534213120000000000000000000), (-244975196749219332714606691486989/2251799813685248000000000000000000), (48633870052449091410973530117801/562949953421312000000000000000000), (107472604513657059360975170593159/11258999068426240000000000000000000), (-22308138206566871520160225295647/11258999068426240000000000000000000), (-1139241086668784851316422908257/5629499534213120000000000000000000), (291375607267568609620583705929/11258999068426240000000000000000000), (6708564349817633745807478299/2814749767106560000000000000000000), (-1251373244959861656199376263/5629499534213120000000000000000000), (-102669685562643365523220331/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial130.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial130.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial130.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial130.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial130 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial130 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial130 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 16162561240639058027688441485354090), (Int.ofNat 284964042099760755219010024409499), (Int.ofNat 1055851801181806547132795501209748), (Int.negOfNat 95440511068805771062537857008974), (Int.negOfNat 22979449546427446360843113646859), (Int.ofNat 2207695002210071837961366709974), (Int.ofNat 294309929730848869235877670551), (Int.negOfNat 26597866812624097646601955396), (Int.negOfNat 2510324335192320665582791826), (Int.ofNat 204856414063527818110172762), (Int.ofNat 15237142571847503129863592), (Int.negOfNat 1108625813562958911536111), (Int.negOfNat 68956482489735140855735), (Int.ofNat 4467272044237056593417), (Int.ofNat 241884798905064977252), (Int.negOfNat 13674651140504444414), (Int.negOfNat 678886412225861774), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1616256124063905802768844148535409/1125899906842624000000000000000000), (284964042099760755219010024409499/11258999068426240000000000000000000), (263962950295451636783198875302437/2814749767106560000000000000000000), (-47720255534402885531268928504487/5629499534213120000000000000000000), (-22979449546427446360843113646859/11258999068426240000000000000000000), (1103847501105035918980683354987/5629499534213120000000000000000000), (294309929730848869235877670551/11258999068426240000000000000000000), (-6649466703156024411650488849/2814749767106560000000000000000000), (-1255162167596160332791395913/5629499534213120000000000000000000), (102428207031763909055086381/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial130.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial130.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial130.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 12414868350940551126963779349408027), (Int.ofNat 2846915501741880464022508780749622), (Int.ofNat 157664082819796718948938720742399), (Int.negOfNat 161989810469712801570750835264841), (Int.ofNat 7474171713787600426286351200145), (Int.ofNat 2878331892869611983287476563753), (Int.negOfNat 189697457102862716509126406812), (Int.negOfNat 29666778613188669648391848685), (Int.ofNat 2127385873267741130973674119), (Int.ofNat 205690672012521982721182054), (Int.negOfNat 14858485194707022193541219), (Int.negOfNat 1033949005871328398975156), (Int.ofNat 72802893551578558387777), (Int.ofNat 3951735838209280030938), (Int.negOfNat 267395787649884136548), (Int.negOfNat 11626480446019095408), (Int.ofNat 806226899425967102), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-12414868350940551126963779349408027/11258999068426240000000000000000000), (1423457750870940232011254390374811/5629499534213120000000000000000000), (157664082819796718948938720742399/11258999068426240000000000000000000), (-161989810469712801570750835264841/11258999068426240000000000000000000), (1494834342757520085257270240029/2251799813685248000000000000000000), (2878331892869611983287476563753/11258999068426240000000000000000000), (-47424364275715679127281601703/2814749767106560000000000000000000), (-5933355722637733929678369737/2251799813685248000000000000000000), (2127385873267741130973674119/11258999068426240000000000000000000), (102845336006260991360591027/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial130.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial130.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial130.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 7189911199199013528661458429091243), (Int.ofNat 1955988124224919574398070172727335), (Int.negOfNat 465526316451689398633829373819944), (Int.negOfNat 29372841356865319438585653412037), (Int.ofNat 19547961893733868201891598878191), (Int.negOfNat 664316450646801151674641040786), (Int.negOfNat 288806850874227284509346376225), (Int.ofNat 16414712498655546533563165238), (Int.ofNat 2471547530183380454976936584), (Int.negOfNat 165257303319240504488811443), (Int.negOfNat 14317945437089584505440180), (Int.ofNat 1031291174803234516322104), (Int.ofNat 60761115410551843541354), (Int.negOfNat 4538184018394217137432), (Int.negOfNat 198045669771064748124), (Int.ofNat 15143383543670528052), (Int.ofNat 470636363397431772), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-7189911199199013528661458429091243/11258999068426240000000000000000000), (391197624844983914879614034545467/2251799813685248000000000000000000), (-58190789556461174829228671727493/1407374883553280000000000000000000), (-29372841356865319438585653412037/11258999068426240000000000000000000), (19547961893733868201891598878191/11258999068426240000000000000000000), (-332158225323400575837320520393/5629499534213120000000000000000000), (-11552274034969091380373855049/450359962737049600000000000000000), (8207356249327773266781582619/5629499534213120000000000000000000), (308943441272922556872117073/1407374883553280000000000000000000), (-165257303319240504488811443/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial130.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial130.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial130.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 5099360474879571168218384612200359), (Int.ofNat 267790755724349509589307387998139), (Int.negOfNat 280505625317564121048789895063488), (Int.ofNat 66790963706935825332844721006877), (Int.ofNat 2131330164704879355309422531374), (Int.negOfNat 2057524011739671932256441568405), (Int.ofNat 76383385467125223651048347981), (Int.ofNat 24843737719884022293287200637), (Int.negOfNat 1449250554309487913702689589), (Int.negOfNat 177109275369059590210532459), (Int.ofNat 12454797450277378194815104), (Int.ofNat 862804744585438296413050), (Int.negOfNat 68149518186917106001951), (Int.negOfNat 3102211154823745469277), (Int.ofNat 266858169020274768777), (Int.ofNat 8230887300190251428), (Int.negOfNat 822460309624470536), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-5099360474879571168218384612200359/11258999068426240000000000000000000), (267790755724349509589307387998139/11258999068426240000000000000000000), (-4382900395586939391387342110367/175921860444160000000000000000000), (66790963706935825332844721006877/11258999068426240000000000000000000), (1065665082352439677654711265687/5629499534213120000000000000000000), (-411504802347934386451288313681/2251799813685248000000000000000000), (76383385467125223651048347981/11258999068426240000000000000000000), (24843737719884022293287200637/11258999068426240000000000000000000), (-1449250554309487913702689589/11258999068426240000000000000000000), (-177109275369059590210532459/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial130.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial130.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial130.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 5175592172985298654962559454182820), (Int.negOfNat 125164345034860112697039417400269), (Int.ofNat 38566767607548142880993624247597), (Int.ofNat 24344660181142997361552010688313), (Int.negOfNat 9047567715516695198768434739344), (Int.ofNat 57943215454845500397922078041), (Int.ofNat 192975305876472658030202940651), (Int.negOfNat 9276961011165010081218670477), (Int.negOfNat 1868263698859030901740299379), (Int.ofNat 125016227189782497923797677), (Int.ofNat 11021167361353431666600144), (Int.negOfNat 892910022863125515031188), (Int.negOfNat 44841177621494191673525), (Int.ofNat 4237209567278154730949), (Int.ofNat 134390445189936393165), (Int.negOfNat 15135915300958808508), (Int.negOfNat 256975177836167292), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-258779608649264932748127972709141/562949953421312000000000000000000), (-125164345034860112697039417400269/11258999068426240000000000000000000), (38566767607548142880993624247597/11258999068426240000000000000000000), (24344660181142997361552010688313/11258999068426240000000000000000000), (-565472982219793449923027171209/703687441776640000000000000000000), (57943215454845500397922078041/11258999068426240000000000000000000), (192975305876472658030202940651/11258999068426240000000000000000000), (-9276961011165010081218670477/11258999068426240000000000000000000), (-1868263698859030901740299379/11258999068426240000000000000000000), (125016227189782497923797677/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial130.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial130.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial130.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 5209045400625879318830308996996518), (Int.ofNat 67667559356988883684250831162943), (Int.ofNat 9536165373369870758433154252073), (Int.negOfNat 22585213065200449731899756787586), (Int.negOfNat 969184180128797846317646970332), (Int.ofNat 1068847013598916730136756184538), (Int.negOfNat 39963199007641489228054722941), (Int.negOfNat 15938279997733490100821954690), (Int.ofNat 1019815455888902596535846216), (Int.ofNat 122269557577788836091225751), (Int.negOfNat 10080273642191238432979300), (Int.negOfNat 587516327522468114208006), (Int.ofNat 59697972069018714774070), (Int.ofNat 1944576061866010455438), (Int.negOfNat 245126760989635904258), (Int.negOfNat 4584630629330541568), (Int.ofNat 838693719822973970), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-2604522700312939659415154498498259/5629499534213120000000000000000000), (67667559356988883684250831162943/11258999068426240000000000000000000), (9536165373369870758433154252073/11258999068426240000000000000000000), (-11292606532600224865949878393793/5629499534213120000000000000000000), (-242296045032199461579411742583/2814749767106560000000000000000000), (534423506799458365068378092269/5629499534213120000000000000000000), (-39963199007641489228054722941/11258999068426240000000000000000000), (-1593827999773349010082195469/1125899906842624000000000000000000), (127476931986112824566980777/1407374883553280000000000000000000), (122269557577788836091225751/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial130.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial130.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial130.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 5201836506291560105323858430173679), (Int.negOfNat 124260439125503627509715910843979), (Int.negOfNat 81766954569590402891252600844940), (Int.negOfNat 592067882378037936674037896657), (Int.ofNat 4341682431941879389475999589192), (Int.negOfNat 138379279692226864981196987089), (Int.negOfNat 105506915170778150229888733890), (Int.ofNat 6822080926714004974905167977), (Int.ofNat 1135142321526217233983783493), (Int.negOfNat 97363474415115659060877402), (Int.negOfNat 6784059723126751684161213), (Int.ofNat 740734874078038155682404), (Int.ofNat 25500278434177296545675), (Int.negOfNat 3671846026074458987094), (Int.negOfNat 61851492642008454030), (Int.ofNat 13693216881039656808), (Int.ofNat 43313992274902812), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-5201836506291560105323858430173679/11258999068426240000000000000000000), (-124260439125503627509715910843979/11258999068426240000000000000000000), (-4088347728479520144562630042247/562949953421312000000000000000000), (-592067882378037936674037896657/11258999068426240000000000000000000), (542710303992734923684499948649/1407374883553280000000000000000000), (-138379279692226864981196987089/11258999068426240000000000000000000), (-10550691517077815022988873389/1125899906842624000000000000000000), (6822080926714004974905167977/11258999068426240000000000000000000), (1135142321526217233983783493/11258999068426240000000000000000000), (-48681737207557829530438701/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial130.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial130.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial130.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 5722766789878587480422539747006935), (Int.negOfNat 346858515269121481246550166179954), (Int.negOfNat 11397191553397394731095753447183), (Int.ofNat 16985088323253314941559655662201), (Int.negOfNat 641582486552979925972759959950), (Int.negOfNat 550601944606244885589051987940), (Int.ofNat 40553084707755148246818363451), (Int.ofNat 8599248808358503368109015240), (Int.negOfNat 811430576843740752202799742), (Int.negOfNat 67115356232775419081575526), (Int.ofNat 8058233488561879714067206), (Int.ofNat 296497032364723197811061), (Int.negOfNat 49039003404733214373449), (Int.negOfNat 749141242096242430615), (Int.ofNat 204761731780406939136), (Int.ofNat 612524266182117908), (Int.negOfNat 783706734834389244), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-1144553357975717496084507949401387/2251799813685248000000000000000000), (-173429257634560740623275083089977/5629499534213120000000000000000000), (-11397191553397394731095753447183/11258999068426240000000000000000000), (16985088323253314941559655662201/11258999068426240000000000000000000), (-12831649731059598519455199199/225179981368524800000000000000000), (-27530097230312244279452599397/562949953421312000000000000000000), (40553084707755148246818363451/11258999068426240000000000000000000), (214981220208962584202725381/281474976710656000000000000000000), (-405715288421870376101399871/5629499534213120000000000000000000), (-33557678116387709540787763/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial130.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial130.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial130.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 6350613794871936872165606163668557), (Int.negOfNat 242508523444958328603947151964265), (Int.ofNat 44913109869011659125801083581834), (Int.negOfNat 551764980211906609353593038814), (Int.negOfNat 2371491978688322944753624039359), (Int.ofNat 228284389762026041104722908048), (Int.ofNat 53510409346044435940288742657), (Int.negOfNat 5983949327239818148826073152), (Int.negOfNat 558749299185510374634212858), (Int.ofNat 76930172786858031911638554), (Int.ofNat 2980071481112246576342802), (Int.negOfNat 581072633458285706250455), (Int.negOfNat 7528241043263817426503), (Int.ofNat 2905941593143187361361), (Int.negOfNat 3231898838792850528), (Int.negOfNat 10764371159437272916), (Int.ofNat 109949071564942464), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-6350613794871936872165606163668557/11258999068426240000000000000000000), (-48501704688991665720789430392853/2251799813685248000000000000000000), (22456554934505829562900541790917/5629499534213120000000000000000000), (-275882490105953304676796519407/5629499534213120000000000000000000), (-2371491978688322944753624039359/11258999068426240000000000000000000), (14267774360126627569045181753/703687441776640000000000000000000), (53510409346044435940288742657/11258999068426240000000000000000000), (-93499208238122158575407393/175921860444160000000000000000000), (-279374649592755187317106429/5629499534213120000000000000000000), (38465086393429015955819277/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial130.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial130.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial130.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 6688474370061247323731681351756627), (Int.negOfNat 119895299103015630486908996125436), (Int.ofNat 11141876461036617827461651054200), (Int.negOfNat 5748162054869029002351343571120), (Int.ofNat 1146440305910586578168194847543), (Int.ofNat 279539811262646862929096270342), (Int.negOfNat 39559772163512049615311424238), (Int.negOfNat 3942263347565553487955724627), (Int.ofNat 646917495143509478887690671), (Int.ofNat 25457922678355075394953898), (Int.negOfNat 6079906298151480830977927), (Int.negOfNat 58410117663847420358312), (Int.ofNat 36574981741702963060605), (Int.negOfNat 242543602913873622498), (Int.negOfNat 153037857611289827198), (Int.ofNat 2591515542446599480), (Int.ofNat 652088217925881880), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-6688474370061247323731681351756627/11258999068426240000000000000000000), (-29973824775753907621727249031359/2814749767106560000000000000000000), (55709382305183089137308255271/56294995342131200000000000000000), (-71852025685862862529391794639/140737488355328000000000000000000), (1146440305910586578168194847543/11258999068426240000000000000000000), (139769905631323431464548135171/5629499534213120000000000000000000), (-19779886081756024807655712119/5629499534213120000000000000000000), (-3942263347565553487955724627/11258999068426240000000000000000000), (646917495143509478887690671/11258999068426240000000000000000000), (12728961339177537697476949/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial130.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial130.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial130.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 6905258429837424940824055991798676), (Int.negOfNat 93927892814560157299292263088204), (Int.ofNat 15594389771119339684420869049885), (Int.ofNat 7271945922362034950113218657971), (Int.ofNat 1211829745430135304490941021614), (Int.negOfNat 232458821900652884576243463372), (Int.negOfNat 24479498815179260715734818215), (Int.ofNat 4768746112732004981462118438), (Int.ofNat 187319352807455029105678664), (Int.negOfNat 55811665130494918623783793), (Int.negOfNat 272417565546957723380460), (Int.ofNat 406359754605114326125502), (Int.negOfNat 5726994256678364648722), (Int.negOfNat 1995682607483835255226), (Int.ofNat 52422898718659458330), (Int.ofNat 6894302507864479456), (Int.negOfNat 197402876950534058), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-1726314607459356235206013997949669/2814749767106560000000000000000000), (-23481973203640039324823065772051/2814749767106560000000000000000000), (3118877954223867936884173809977/2251799813685248000000000000000000), (7271945922362034950113218657971/11258999068426240000000000000000000), (605914872715067652245470510807/5629499534213120000000000000000000), (-58114705475163221144060865843/2814749767106560000000000000000000), (-4895899763035852143146963643/2251799813685248000000000000000000), (2384373056366002490731059219/5629499534213120000000000000000000), (23414919100931878638209833/1407374883553280000000000000000000), (-55811665130494918623783793/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial130.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial130.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial130.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 6961546891113490146007897728345605), (Int.ofNat 73397365705703579859777830078332), (Int.ofNat 67128910654370192106759789666179), (Int.ofNat 6469442277828133217079257800527), (Int.negOfNat 1249397622870307127385589613330), (Int.negOfNat 145583610920919357974253395771), (Int.ofNat 30127523976902557316306476461), (Int.ofNat 1281089259566307917597715979), (Int.negOfNat 442805559735979890369098573), (Int.ofNat 329926110625824357645233), (Int.ofNat 3930715981937363008434864), (Int.negOfNat 94523547411914293937708), (Int.negOfNat 22789496531711283563823), (Int.ofNat 877454884131763457929), (Int.ofNat 91893636057695884447), (Int.negOfNat 4575327635649198980), (Int.negOfNat 438427032364617400), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-1392309378222698029201579545669121/2251799813685248000000000000000000), (18349341426425894964944457519583/2814749767106560000000000000000000), (67128910654370192106759789666179/11258999068426240000000000000000000), (6469442277828133217079257800527/11258999068426240000000000000000000), (-124939762287030712738558961333/1125899906842624000000000000000000), (-145583610920919357974253395771/11258999068426240000000000000000000), (30127523976902557316306476461/11258999068426240000000000000000000), (1281089259566307917597715979/11258999068426240000000000000000000), (-442805559735979890369098573/11258999068426240000000000000000000), (329926110625824357645233/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial130.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial130.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial130.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 6517147318051328397421087308572041), (Int.ofNat 373843199309837445672829202563323), (Int.ofNat 71654093248072157355779925340366), (Int.negOfNat 4548870414943252211954461543828), (Int.negOfNat 987139026815687757039965600167), (Int.ofNat 152806768715875133426616820015), (Int.ofNat 9402945669615688052301358841), (Int.negOfNat 2931111215797920120502936587), (Int.ofNat 14918277576777940048061705), (Int.ofNat 32264364784962177630867613), (Int.negOfNat 1207813441494311442283412), (Int.negOfNat 221615083494211513830074), (Int.ofNat 12751084094649421316215), (Int.ofNat 1026222382032260129471), (Int.negOfNat 74658925109314608221), (Int.negOfNat 3133638079267020676), (Int.ofNat 213636287149037492), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-6517147318051328397421087308572041/11258999068426240000000000000000000), (373843199309837445672829202563323/11258999068426240000000000000000000), (35827046624036078677889962670183/5629499534213120000000000000000000), (-1137217603735813052988615385957/2814749767106560000000000000000000), (-987139026815687757039965600167/11258999068426240000000000000000000), (30561353743175026685323364003/2251799813685248000000000000000000), (9402945669615688052301358841/11258999068426240000000000000000000), (-2931111215797920120502936587/11258999068426240000000000000000000), (2983655515355588009612341/2251799813685248000000000000000000), (32264364784962177630867613/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial130.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial130.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial130.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 5529894604239990171120977541297188), (Int.ofNat 587082739458558396409638678866874), (Int.ofNat 33337323948468470445485056022576), (Int.negOfNat 6296713803706503437405220895273), (Int.ofNat 407505168787816526707778031054), (Int.ofNat 76410017534897435308589430090), (Int.negOfNat 14699617152334517864787697947), (Int.ofNat 22901130237531211675445442), (Int.ofNat 212708427034568901935481420), (Int.negOfNat 11925692438970919958874599), (Int.negOfNat 1740139862180625343182376), (Int.ofNat 155683364974504624886480), (Int.ofNat 8974851983720387316786), (Int.negOfNat 1089594536683962154092), (Int.negOfNat 31836366899641449136), (Int.ofNat 5145554098575704236), (Int.ofNat 224765846803352920), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-1382473651059997542780244385324297/2814749767106560000000000000000000), (293541369729279198204819339433437/5629499534213120000000000000000000), (2083582746779279402842816001411/703687441776640000000000000000000), (-6296713803706503437405220895273/11258999068426240000000000000000000), (203752584393908263353889015527/5629499534213120000000000000000000), (7641001753489743530858943009/1125899906842624000000000000000000), (-14699617152334517864787697947/11258999068426240000000000000000000), (11450565118765605837722721/5629499534213120000000000000000000), (10635421351728445096774071/562949953421312000000000000000000), (-11925692438970919958874599/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial130.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial130.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial130.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 4264679269001411666391006917347088), (Int.ofNat 661395710694537859627831914934791), (Int.ofNat 8248431141506604029291304977576), (Int.negOfNat 2021798736039668986348142250580), (Int.ofNat 470099637669054062391398624320), (Int.negOfNat 35704607353530317297630188277), (Int.negOfNat 1834084752339310267281062992), (Int.ofNat 963085375693763301167680883), (Int.negOfNat 85208475201029749591661851), (Int.negOfNat 9506161079288730937516174), (Int.ofNat 1547152827388350470496303), (Int.ofNat 48394153336304400883344), (Int.negOfNat 13344266656221895494037), (Int.negOfNat 114466971236085192378), (Int.ofNat 72792014313758503124), (Int.negOfNat 592808293612951344), (Int.negOfNat 229869697347540926), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-266542454312588229149437932334193/703687441776640000000000000000000), (661395710694537859627831914934791/11258999068426240000000000000000000), (1031053892688325503661413122197/1407374883553280000000000000000000), (-101089936801983449317407112529/562949953421312000000000000000000), (1469061367715793944973120701/35184372088832000000000000000000), (-35704607353530317297630188277/11258999068426240000000000000000000), (-114630297021206891705066437/703687441776640000000000000000000), (963085375693763301167680883/11258999068426240000000000000000000), (-85208475201029749591661851/11258999068426240000000000000000000), (-4753080539644365468758087/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial130.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial130.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial130.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 2918708624206744481365313616572299), (Int.ofNat 682292973285007306998867390726170), (Int.ofNat 4572469050716510820675696315703), (Int.ofNat 377214651896206469207221195037), (Int.ofNat 160087879346739086807242936884), (Int.negOfNat 21563262483722621458162716624), (Int.ofNat 871061488072800529068747205), (Int.negOfNat 348703574711919113218355280), (Int.negOfNat 11250147116737178229953770), (Int.ofNat 11557068014681906504951294), (Int.negOfNat 143727563799391011971896), (Int.negOfNat 132011508954051661567455), (Int.ofNat 2904678902510323088387), (Int.ofNat 887552427736284142949), (Int.negOfNat 22613481954934869412), (Int.negOfNat 4343165399896486274), (Int.negOfNat 5693524509253962), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-2918708624206744481365313616572299/11258999068426240000000000000000000), (68229297328500730699886739072617/1125899906842624000000000000000000), (4572469050716510820675696315703/11258999068426240000000000000000000), (377214651896206469207221195037/11258999068426240000000000000000000), (40021969836684771701810734221/2814749767106560000000000000000000), (-1347703905232663841135169789/703687441776640000000000000000000), (174212297614560105813749441/2251799813685248000000000000000000), (-4358794683898988915229441/140737488355328000000000000000000), (-1125014711673717822995377/1125899906842624000000000000000000), (5778534007340953252475647/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial130.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial130.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial130.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 1530929950352188805176331056027775), (Int.ofNat 708531200652125835824860709601305), (Int.ofNat 8955578974723412325375476486477), (Int.ofNat 774233041897483228113585683117), (Int.negOfNat 73768502506244288928232318066), (Int.negOfNat 26652496834628062901396126582), (Int.ofNat 401080632886112484334403035), (Int.ofNat 455856533734369115511569460), (Int.ofNat 49027454882783622910862470), (Int.negOfNat 7609548462510836672426506), (Int.negOfNat 917944548220647845208264), (Int.ofNat 84160527573010198605865), (Int.ofNat 8220925148379969191053), (Int.negOfNat 596940699091018306171), (Int.negOfNat 46604054137978136148), (Int.ofNat 3136133378978431806), (Int.ofNat 98251180439033562), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-61237198014087552207053242241111/450359962737049600000000000000000), (141706240130425167164972141920261/2251799813685248000000000000000000), (8955578974723412325375476486477/11258999068426240000000000000000000), (774233041897483228113585683117/11258999068426240000000000000000000), (-36884251253122144464116159033/5629499534213120000000000000000000), (-13326248417314031450698063291/5629499534213120000000000000000000), (80216126577222496866880607/2251799813685248000000000000000000), (22792826686718455775578473/562949953421312000000000000000000), (4902745488278362291086247/1125899906842624000000000000000000), (-3804774231255418336213253/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial130.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial130.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial130.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.negOfNat 73792610504842348827342298119864), (Int.ofNat 749461837978278565629054129955202), (Int.ofNat 10145961759213123272238260167746), (Int.negOfNat 525435968085331618389615193736), (Int.negOfNat 172357010372096661014194635545), (Int.ofNat 18761517191563416290156860730), (Int.ofNat 5648508362861514061403298352), (Int.negOfNat 164297769776451426285858337), (Int.negOfNat 107627815580794016945983429), (Int.negOfNat 1663813465236012002182374), (Int.ofNat 1336917393135987319751897), (Int.ofNat 39204670541489905370864), (Int.negOfNat 10774359588676715168563), (Int.negOfNat 336761898981150776098), (Int.ofNat 58748852031058268236), (Int.ofNat 2336316737429844016), (Int.negOfNat 147569539330591314), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-9224076313105293603417787264983/1407374883553280000000000000000000), (374730918989139282814527064977601/5629499534213120000000000000000000), (5072980879606561636119130083873/5629499534213120000000000000000000), (-65679496010666452298701899217/1407374883553280000000000000000000), (-34471402074419332202838927109/2251799813685248000000000000000000), (1876151719156341629015686073/1125899906842624000000000000000000), (353031772678844628837706147/703687441776640000000000000000000), (-164297769776451426285858337/11258999068426240000000000000000000), (-107627815580794016945983429/11258999068426240000000000000000000), (-831906732618006001091187/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial130.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial130.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial130.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1459667554352304472300194508865293), (Int.ofNat 780629825212539824241751561455668), (Int.ofNat 5418143183452653749944751545448), (Int.negOfNat 522965946958686651595919279634), (Int.ofNat 199112311151623983656268297162), (Int.ofNat 31971306250766814907485264124), (Int.negOfNat 5415902242295972878559389833), (Int.negOfNat 918257204966275544583954018), (Int.ofNat 67566049995917542064179380), (Int.ofNat 14861193468728738549407181), (Int.negOfNat 428316192732535549076924), (Int.negOfNat 148572648808230236407280), (Int.ofNat 1237226440392342107454), (Int.ofNat 976196742788000766588), (Int.ofNat 512272006270862896), (Int.negOfNat 4604865782144515444), (Int.ofNat 109998868389396440), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(1459667554352304472300194508865293/11258999068426240000000000000000000), (195157456303134956060437890363917/2814749767106560000000000000000000), (677267897931581718743093943181/1407374883553280000000000000000000), (-261482973479343325797959639817/5629499534213120000000000000000000), (99556155575811991828134148581/5629499534213120000000000000000000), (7992826562691703726871316031/2814749767106560000000000000000000), (-5415902242295972878559389833/11258999068426240000000000000000000), (-459128602483137772291977009/5629499534213120000000000000000000), (3378302499795877103208969/562949953421312000000000000000000), (14861193468728738549407181/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial130.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial130.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial130.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3042184949958068591733900240561534), (Int.ofNat 803604515360950014306874935353970), (Int.ofNat 7880539075977826086456974958341), (Int.ofNat 1156551894441561348965065199569), (Int.ofNat 60824402052451206760195491973), (Int.negOfNat 57335465973171702245549743769), (Int.negOfNat 4075699627888381041173280843), (Int.ofNat 1239093990467544591955016093), (Int.ofNat 108527218586151133964761635), (Int.negOfNat 14340397619860589876659407), (Int.negOfNat 1522408055873873766519248), (Int.ofNat 99679364460249981729726), (Int.ofNat 12895992858761889157145), (Int.negOfNat 449803899840094928329), (Int.negOfNat 71358321333837415819), (Int.ofNat 1059276408398999964), (Int.ofNat 163802949529094748), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(1521092474979034295866950120280767/5629499534213120000000000000000000), (80360451536095001430687493535397/1125899906842624000000000000000000), (7880539075977826086456974958341/11258999068426240000000000000000000), (1156551894441561348965065199569/11258999068426240000000000000000000), (60824402052451206760195491973/11258999068426240000000000000000000), (-57335465973171702245549743769/11258999068426240000000000000000000), (-4075699627888381041173280843/11258999068426240000000000000000000), (1239093990467544591955016093/11258999068426240000000000000000000), (21705443717230226792952327/2251799813685248000000000000000000), (-14340397619860589876659407/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial130.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial130.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial130.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4689223900822067551217111298706798), (Int.ofNat 846209122651808093680294656791844), (Int.ofNat 11661745797833885404935232981091), (Int.negOfNat 509006585055295492762601584616), (Int.negOfNat 361244818002165995717154631631), (Int.ofNat 9312805987063084869478253273), (Int.ofNat 12762619941643955602871136299), (Int.ofNat 225008349724061829867119559), (Int.negOfNat 220259295577143065047866047), (Int.negOfNat 9095108283507046852961707), (Int.ofNat 2155529383490280708497096), (Int.ofNat 123520471994848434985572), (Int.negOfNat 13221189037405121341857), (Int.negOfNat 931287175332674818431), (Int.ofNat 54437942628650993633), (Int.ofNat 4597397539432795900), (Int.negOfNat 323660053950660920), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(2344611950411033775608555649353399/5629499534213120000000000000000000), (211552280662952023420073664197961/2814749767106560000000000000000000), (11661745797833885404935232981091/11258999068426240000000000000000000), (-63625823131911936595325198077/1407374883553280000000000000000000), (-361244818002165995717154631631/11258999068426240000000000000000000), (9312805987063084869478253273/11258999068426240000000000000000000), (12762619941643955602871136299/11258999068426240000000000000000000), (225008349724061829867119559/11258999068426240000000000000000000), (-220259295577143065047866047/11258999068426240000000000000000000), (-9095108283507046852961707/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial130.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial130.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial130.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 6419522134494080692204416315439487), (Int.ofNat 878250003687149226842323267245214), (Int.ofNat 3487766322046692593781950635229), (Int.negOfNat 1265416044656468305987387755008), (Int.ofNat 309519863868933126019343656189), (Int.ofNat 83808756976146778071239201204), (Int.negOfNat 6733771233921954245948505045), (Int.negOfNat 2294332471422736963111125742), (Int.ofNat 37587087962355090575511456), (Int.ofNat 31915101936975345301530827), (Int.ofNat 450862391282635707568580), (Int.negOfNat 258277979157696210782818), (Int.negOfNat 8106387163103856910278), (Int.ofNat 1343431399107518766574), (Int.ofNat 58437303264791835270), (Int.negOfNat 4705533079258709824), (Int.negOfNat 180036359727598182), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(6419522134494080692204416315439487/11258999068426240000000000000000000), (439125001843574613421161633622607/5629499534213120000000000000000000), (3487766322046692593781950635229/11258999068426240000000000000000000), (-2471515712219664660131616709/21990232555520000000000000000000), (309519863868933126019343656189/11258999068426240000000000000000000), (20952189244036694517809800301/2814749767106560000000000000000000), (-1346754246784390849189701009/2251799813685248000000000000000000), (-1147166235711368481555562871/5629499534213120000000000000000000), (1174596498823596580484733/351843720888320000000000000000000), (31915101936975345301530827/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial130.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial130.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial130.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 8186785315065487093227797256524682), (Int.ofNat 891415966028054753678303045218739), (Int.ofNat 7082576284664322284149533315083), (Int.ofNat 2435324350570175231186762697452), (Int.ofNat 266606049169011353447226250018), (Int.negOfNat 112878183790006339561558395041), (Int.negOfNat 15655155821568210398260030682), (Int.ofNat 1930260866953297463495450613), (Int.ofNat 349865247760195255893061369), (Int.negOfNat 12922880019240297006573742), (Int.negOfNat 3932453042777707193819853), (Int.ofNat 5076469623492630308288), (Int.ofNat 25944093817949021577395), (Int.ofNat 422204368848334641022), (Int.negOfNat 113850883247267774522), (Int.negOfNat 3154699119513644200), (Int.ofNat 537321239511925400), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(4093392657532743546613898628262341/5629499534213120000000000000000000), (891415966028054753678303045218739/11258999068426240000000000000000000), (7082576284664322284149533315083/11258999068426240000000000000000000), (608831087642543807796690674363/2814749767106560000000000000000000), (133303024584505676723613125009/5629499534213120000000000000000000), (-112878183790006339561558395041/11258999068426240000000000000000000), (-7827577910784105199130015341/5629499534213120000000000000000000), (1930260866953297463495450613/11258999068426240000000000000000000), (349865247760195255893061369/11258999068426240000000000000000000), (-6461440009620148503286871/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial130.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial130.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial130.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 10017407925737668815113254273241070), (Int.ofNat 946639326460644958906870900720004), (Int.ofNat 17126738514096575436157994299631), (Int.negOfNat 870578794891292967432233434342), (Int.negOfNat 970585490076695393882354952269), (Int.negOfNat 36825231570228845830887284338), (Int.ofNat 30266305108241824586584271063), (Int.ofNat 2570120566820876877917636128), (Int.negOfNat 384081883511684394531225522), (Int.negOfNat 47645938362065750886149486), (Int.ofNat 2083487183407804665282878), (Int.ofNat 417500549301965651842225), (Int.negOfNat 3875373282840392013337), (Int.negOfNat 2239560811527062161879), (Int.negOfNat 15946077076319968672), (Int.ofNat 8677639442407133484), (Int.ofNat 125049374739013456), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(1001740792573766881511325427324107/1125899906842624000000000000000000), (236659831615161239726717725180001/2814749767106560000000000000000000), (17126738514096575436157994299631/11258999068426240000000000000000000), (-435289397445646483716116717171/5629499534213120000000000000000000), (-970585490076695393882354952269/11258999068426240000000000000000000), (-18412615785114422915443642169/5629499534213120000000000000000000), (30266305108241824586584271063/11258999068426240000000000000000000), (80316267713152402434926129/351843720888320000000000000000000), (-192040941755842197265612761/5629499534213120000000000000000000), (-23822969181032875443074743/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial130.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial130.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial130.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 11957667380699470232282384907665580), (Int.ofNat 977169205150464914027155750627678), (Int.negOfNat 6218457427113956652036880693233), (Int.negOfNat 4722266133208228548516254424999), (Int.ofNat 618827555653347215492054728475), (Int.ofNat 302162387060067888521155626036), (Int.ofNat 3673943099529555238447151869), (Int.negOfNat 6568842943450145075783650480), (Int.negOfNat 434566266060058519130709678), (Int.ofNat 55132829710198172623088834), (Int.ofNat 5678355980542410486254314), (Int.negOfNat 238262674941587771968859), (Int.negOfNat 38321493166296558127911), (Int.ofNat 510101423900016177345), (Int.ofNat 167944997779539500864), (Int.ofNat 225853397911260308), (Int.negOfNat 690584303351770676), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(597883369034973511614119245383279/562949953421312000000000000000000), (488584602575232457013577875313839/5629499534213120000000000000000000), (-6218457427113956652036880693233/11258999068426240000000000000000000), (-4722266133208228548516254424999/11258999068426240000000000000000000), (24753102226133888619682189139/450359962737049600000000000000000), (75540596765016972130288906509/2814749767106560000000000000000000), (3673943099529555238447151869/11258999068426240000000000000000000), (-82110536793126813447295631/140737488355328000000000000000000), (-217283133030029259565354839/5629499534213120000000000000000000), (27566414855099086311544417/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial130.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial130.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial130.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 13868240745633977993074288740974678), (Int.ofNat 937073734099674195751532237016742), (Int.ofNat 471850073863493437732282816993), (Int.ofNat 8814891914974796561743755198527), (Int.ofNat 1818946423837895301254403288119), (Int.negOfNat 253873718943576346286536880846), (Int.negOfNat 86383531454964824588102941490), (Int.negOfNat 2233485354518986006267169483), (Int.ofNat 1013737392022901183685778367), (Int.ofNat 64754933087866931040899658), (Int.negOfNat 6067184940965594832570507), (Int.negOfNat 577595802171817488275596), (Int.ofNat 21853673836417858622125), (Int.ofNat 3061325582447897634026), (Int.negOfNat 46682770029017293050), (Int.negOfNat 11881679251035850872), (Int.ofNat 6569142169493908), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(6934120372816988996537144370487339/5629499534213120000000000000000000), (468536867049837097875766118508371/5629499534213120000000000000000000), (471850073863493437732282816993/11258999068426240000000000000000000), (8814891914974796561743755198527/11258999068426240000000000000000000), (1818946423837895301254403288119/11258999068426240000000000000000000), (-126936859471788173143268440423/5629499534213120000000000000000000), (-8638353145496482458810294149/1125899906842624000000000000000000), (-2233485354518986006267169483/11258999068426240000000000000000000), (1013737392022901183685778367/11258999068426240000000000000000000), (32377466543933465520449829/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial130.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial130.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial130.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 15830244890109051311727187820033586), (Int.ofNat 1066200370221932456199162089610606), (Int.ofNat 56503856150911084662784444012742), (Int.ofNat 189849840849564757785172599639), (Int.negOfNat 5233831313026336553196575018765), (Int.negOfNat 956251437767109897849404634586), (Int.ofNat 12376698310599875000390657301), (Int.ofNat 15288068305627182704139174730), (Int.ofNat 605970293976194198709798764), (Int.negOfNat 116610192112344745545468529), (Int.negOfNat 7755104654321163880414520), (Int.ofNat 545933813234602257422474), (Int.ofNat 50080352205050176051330), (Int.negOfNat 1720107434732500163562), (Int.negOfNat 214883344661699064542), (Int.ofNat 3644215253661533152), (Int.ofNat 778038108737362270), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(7915122445054525655863593910016793/5629499534213120000000000000000000), (533100185110966228099581044805303/5629499534213120000000000000000000), (28251928075455542331392222006371/5629499534213120000000000000000000), (189849840849564757785172599639/11258999068426240000000000000000000), (-1046766262605267310639315003753/2251799813685248000000000000000000), (-478125718883554948924702317293/5629499534213120000000000000000000), (12376698310599875000390657301/11258999068426240000000000000000000), (1528806830562718270413917473/1125899906842624000000000000000000), (151492573494048549677449691/2814749767106560000000000000000000), (-116610192112344745545468529/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial130.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial130.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial130.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 18078676276817384020347670625207925), (Int.ofNat 1060056059379167801664246033648972), (Int.negOfNat 130747493719439167315052790589202), (Int.negOfNat 69021336643029046998530634387683), (Int.negOfNat 9640226766973881006987154117823), (Int.ofNat 470767721482069154905716244903), (Int.ofNat 200363760319001686075689340667), (Int.ofNat 4625261554290110428175574403), (Int.negOfNat 1878607510588123067488149101), (Int.negOfNat 94786558097720424212861963), (Int.ofNat 10776491097492986068853596), (Int.ofNat 751466846185530925259292), (Int.negOfNat 42381145361688680136795), (Int.negOfNat 3746175435483223023211), (Int.ofNat 120974079514999751155), (Int.ofNat 13865491344238450372), (Int.negOfNat 220230327730758388), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(723147051072695360813906825008317/450359962737049600000000000000000), (265014014844791950416061508412243/2814749767106560000000000000000000), (-65373746859719583657526395294601/5629499534213120000000000000000000), (-69021336643029046998530634387683/11258999068426240000000000000000000), (-9640226766973881006987154117823/11258999068426240000000000000000000), (470767721482069154905716244903/11258999068426240000000000000000000), (200363760319001686075689340667/11258999068426240000000000000000000), (4625261554290110428175574403/11258999068426240000000000000000000), (-1878607510588123067488149101/11258999068426240000000000000000000), (-94786558097720424212861963/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial130.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial130.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial130.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 18997346898505323032686424821909594), (Int.negOfNat 523553501162334376637945901429634), (Int.negOfNat 691045401633641672520710940521766), (Int.negOfNat 96348619841679795439864209708846), (Int.ofNat 6068123990365973558111655933571), (Int.ofNat 2334700933968489301410933642579), (Int.ofNat 35130566370168144731067834181), (Int.negOfNat 26181135498641626683876817883), (Int.negOfNat 1110013087969727783712184251), (Int.ofNat 180069222070739179374314921), (Int.ofNat 10558766505256184088025556), (Int.negOfNat 851420863055183218810350), (Int.negOfNat 60762161409582943213809), (Int.ofNat 2956250928023493568923), (Int.ofNat 245824380998560712863), (Int.negOfNat 7404879682258991932), (Int.negOfNat 794271518935865704), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(9498673449252661516343212410954797/5629499534213120000000000000000000), (-261776750581167188318972950714817/5629499534213120000000000000000000), (-345522700816820836260355470260883/5629499534213120000000000000000000), (-48174309920839897719932104854423/5629499534213120000000000000000000), (6068123990365973558111655933571/11258999068426240000000000000000000), (2334700933968489301410933642579/11258999068426240000000000000000000), (35130566370168144731067834181/11258999068426240000000000000000000), (-26181135498641626683876817883/11258999068426240000000000000000000), (-1110013087969727783712184251/11258999068426240000000000000000000), (180069222070739179374314921/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial130.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial130.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial130.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 14585783795167585082491653833871098), (Int.negOfNat 4068625196763092810448788868584409), (Int.negOfNat 946953731631661183093675252666364), (Int.ofNat 35643178449773788534234321635305), (Int.ofNat 23774626906601552033114916162386), (Int.ofNat 477792939036213329283408469606), (Int.negOfNat 314610890695032357611237607595), (Int.negOfNat 13494670909663034309376243422), (Int.ofNat 2587025430386513197282051516), (Int.ofNat 143084351635390337314428837), (Int.negOfNat 14593738829168013578808320), (Int.negOfNat 928592135707631176889656), (Int.ofNat 60225593291274901938206), (Int.ofNat 4216127565927214340848), (Int.negOfNat 189841738634647470436), (Int.negOfNat 14435717807164955628), (Int.ofNat 433891513292022868), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(7292891897583792541245826916935549/5629499534213120000000000000000000), (-4068625196763092810448788868584409/11258999068426240000000000000000000), (-236738432907915295773418813166591/2814749767106560000000000000000000), (7128635689954757706846864327061/2251799813685248000000000000000000), (11887313453300776016557458081193/5629499534213120000000000000000000), (238896469518106664641704234803/5629499534213120000000000000000000), (-62922178139006471522247521519/2251799813685248000000000000000000), (-6747335454831517154688121711/5629499534213120000000000000000000), (646756357596628299320512879/2814749767106560000000000000000000), (143084351635390337314428837/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial130.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial130.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial130.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 3320403862012581275280033586284949), (Int.negOfNat 6693266108990466012571836534057025), (Int.negOfNat 203749537732457974149814337640149), (Int.ofNat 192206793260498397461636573221877), (Int.ofNat 9145360568143695010066653960278), (Int.negOfNat 3121524427229801924666516007653), (Int.negOfNat 176090542719870097144604066348), (Int.ofNat 31474658606707731837148127495), (Int.ofNat 1914193228968204584246600161), (Int.negOfNat 214721259611500370589231246), (Int.negOfNat 13575495221897134498678281), (Int.ofNat 1056696250221075660812764), (Int.ofNat 68221341700936991344823), (Int.negOfNat 3932884117905714108782), (Int.negOfNat 257083482132315766012), (Int.ofNat 11131326055138963952), (Int.ofNat 810504929134369138), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(3320403862012581275280033586284949/11258999068426240000000000000000000), (-267730644359618640502873461362281/450359962737049600000000000000000), (-203749537732457974149814337640149/11258999068426240000000000000000000), (192206793260498397461636573221877/11258999068426240000000000000000000), (4572680284071847505033326980139/5629499534213120000000000000000000), (-3121524427229801924666516007653/11258999068426240000000000000000000), (-44022635679967524286151016587/2814749767106560000000000000000000), (6294931721341546367429625499/2251799813685248000000000000000000), (1914193228968204584246600161/11258999068426240000000000000000000), (-107360629805750185294615623/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial130.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial130.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial130.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 9303907609397608106496300023313422), (Int.negOfNat 5177152640783505756780453417003295), (Int.ofNat 900465225253956339229704973644100), (Int.ofNat 132078396694901602588046722418241), (Int.negOfNat 22675111934975843631292566200313), (Int.negOfNat 2238888997851724862712310285926), (Int.ofNat 307668200730477700721101500831), (Int.ofNat 24935811323942635920286139444), (Int.negOfNat 2658984019703922847536483874), (Int.negOfNat 190546813750805823693626738), (Int.ofNat 15978550521442419546513768), (Int.ofNat 1048143134975283555416609), (Int.negOfNat 70796139286768976319305), (Int.negOfNat 4326411177076614262703), (Int.ofNat 242165390509980887508), (Int.ofNat 13633329108485737666), (Int.negOfNat 652963835586121826), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-4651953804698804053248150011656711/5629499534213120000000000000000000), (-1035430528156701151356090683400659/2251799813685248000000000000000000), (9004652252539563392297049736441/112589990684262400000000000000000), (132078396694901602588046722418241/11258999068426240000000000000000000), (-22675111934975843631292566200313/11258999068426240000000000000000000), (-1119444498925862431356155142963/5629499534213120000000000000000000), (307668200730477700721101500831/11258999068426240000000000000000000), (6233952830985658980071534861/2814749767106560000000000000000000), (-1329492009851961423768241937/5629499534213120000000000000000000), (-95273406875402911846813369/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial130.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial130.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial130.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial130.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial130.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial130.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial130.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial130.reflect := by
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

end Bin130
end
end ErdosOverlap.OuterNumerics
