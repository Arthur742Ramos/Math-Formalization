/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.IntegerOuterBindings
public import ErdosOverlap.Numerics.OuterTruncation
public import ErdosOverlap.Certificate.OuterData13
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

/-! # Exact integer weighted outer models for source bin 156

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin156

def weightDenominator : ℤ := (Int.ofNat 5000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 789050066873450000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 562129776063469550)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 288999732284184220)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 463633595896253400)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 359943426504296050)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 255202174656115700)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 186135616415846350)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 115176547512575115)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 54199765100081920)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial156.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial156.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 4633386510341719000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1785394318484773500)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 646966045285897500)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 545666847410352150)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 319247773837009050)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 140340035364373250)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 44567537815711740)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 12475075066905386)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 12739293329346482)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial156.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial156.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4633386510341719000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1785394318484773500)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 646966045285897500)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 545666847410352150)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 319247773837009050)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 140340035364373250)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 44567537815711740)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 12475075066905386)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 12739293329346482)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial156.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial156.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial156.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 1506589191036249759682300977007858), (Int.ofNat 2173167597743858756176763863445801), (Int.ofNat 165061165808167320911390094938241), (Int.negOfNat 58995110397939501985021781315126), (Int.negOfNat 4836910075047567745765535060451), (Int.ofNat 1099249870708289520099701027755), (Int.ofNat 78033526334251046412136863945), (Int.negOfNat 13248232015387522934316065821), (Int.negOfNat 782758424606186952356413210), (Int.ofNat 108599994226934388033842413), (Int.ofNat 5320852291278387849095882), (Int.negOfNat 636655232721952015992138), (Int.negOfNat 26112092745711920005050), (Int.ofNat 2780607092115062317346), (Int.ofNat 97181510031967713750), (Int.negOfNat 9223447773137774846), (Int.negOfNat 297264537970000437), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-753294595518124879841150488503929/2814749767106560000000000000000000), (2173167597743858756176763863445801/5629499534213120000000000000000000), (165061165808167320911390094938241/5629499534213120000000000000000000), (-29497555198969750992510890657563/2814749767106560000000000000000000), (-4836910075047567745765535060451/5629499534213120000000000000000000), (219849974141657904019940205551/1125899906842624000000000000000000), (15606705266850209282427372789/1125899906842624000000000000000000), (-13248232015387522934316065821/5629499534213120000000000000000000), (-78275842460618695235641321/562949953421312000000000000000000), (108599994226934388033842413/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial156.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial156.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial156.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial156 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 2988972869962081339864329185646134), (Int.ofNat 2067145288835130904781553122273038), (Int.negOfNat 208090313566763858637766771663922), (Int.negOfNat 49420148538589375237041098692882), (Int.ofNat 6731681551907032605135556173674), (Int.ofNat 813482979900017349098780320003), (Int.negOfNat 114550219376639178007518000825), (Int.negOfNat 8717849439268770110395028601), (Int.ofNat 1207443634771529814024335712), (Int.ofNat 63771501047473007271580875), (Int.negOfNat 8641694708598033378199044), (Int.negOfNat 335991727352222279278810), (Int.ofNat 44546260471043702995874), (Int.ofNat 1331896275681355091816), (Int.negOfNat 172966374168794688952), (Int.negOfNat 4055672165675472576), (Int.ofNat 558007151597439869), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(1494486434981040669932164592823067/2814749767106560000000000000000000), (1033572644417565452390776561136519/2814749767106560000000000000000000), (-104045156783381929318883385831961/2814749767106560000000000000000000), (-24710074269294687618520549346441/2814749767106560000000000000000000), (3365840775953516302567778086837/2814749767106560000000000000000000), (813482979900017349098780320003/5629499534213120000000000000000000), (-4582008775065567120300720033/225179981368524800000000000000000), (-8717849439268770110395028601/5629499534213120000000000000000000), (37732613586610306688260491/175921860444160000000000000000000), (510172008379784058172647/45035996273704960000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial156.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial156.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial156.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial156 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 6021164676291882608184501169350789), (Int.ofNat 897671928380284349807838677072816), (Int.negOfNat 308970915870667295910371088918800), (Int.ofNat 16127512004619733256027616859195), (Int.ofNat 7037575277732684356414406679647), (Int.negOfNat 698772183961993263942944827719), (Int.negOfNat 89727372501312595648226422563), (Int.ofNat 10910082985204244848429757351), (Int.ofNat 729188400877261464185275254), (Int.negOfNat 100927902173347019048996931), (Int.negOfNat 4109057966282806713102932), (Int.ofNat 631540567717692014585212), (Int.ofNat 16979787142847467084416), (Int.negOfNat 2865322672108455470472), (Int.negOfNat 53466306573583315830), (Int.ofNat 9850866328889750064), (Int.ofNat 121925949340408195), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(6021164676291882608184501169350789/5629499534213120000000000000000000), (56104495523767771862989917317051/351843720888320000000000000000000), (-772427289676668239775927722297/14073748835532800000000000000000), (3225502400923946651205523371839/1125899906842624000000000000000000), (7037575277732684356414406679647/5629499534213120000000000000000000), (-698772183961993263942944827719/5629499534213120000000000000000000), (-89727372501312595648226422563/5629499534213120000000000000000000), (10910082985204244848429757351/5629499534213120000000000000000000), (364594200438630732092637627/2814749767106560000000000000000000), (-100927902173347019048996931/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial156.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial156.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial156.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial156 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 6795671527332674973953116643194569), (Int.ofNat 12779592125739921562283263333277), (Int.negOfNat 112596049437730183770039759003056), (Int.ofNat 36959224148707498215411519030841), (Int.negOfNat 1896689757143372355410698519093), (Int.negOfNat 749556926579882595882937982233), (Int.ofNat 72748745167337628906305887965), (Int.ofNat 7541877954259173138336838929), (Int.negOfNat 979122724680105051750994880), (Int.negOfNat 47314255348266904711252807), (Int.ofNat 7802393605816720114272682), (Int.ofNat 201985068491316712608272), (Int.negOfNat 42452225359578444164262), (Int.negOfNat 612839036546230159992), (Int.ofNat 169458073483784154448), (Int.ofNat 1199162048546891086), (Int.negOfNat 519789271609400423), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(6795671527332674973953116643194569/5629499534213120000000000000000000), (12779592125739921562283263333277/5629499534213120000000000000000000), (-7037253089858136485627484937691/351843720888320000000000000000000), (36959224148707498215411519030841/5629499534213120000000000000000000), (-1896689757143372355410698519093/5629499534213120000000000000000000), (-749556926579882595882937982233/5629499534213120000000000000000000), (14549749033467525781261177593/1125899906842624000000000000000000), (7541877954259173138336838929/5629499534213120000000000000000000), (-3059758514625328286721859/17592186044416000000000000000000), (-47314255348266904711252807/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial156.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial156.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial156.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial156 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 6617542076212250518245547869815805), (Int.negOfNat 98476488521458382002708097198611), (Int.ofNat 24322083827305200016183314683136), (Int.ofNat 5781272455488404315219245863770), (Int.negOfNat 4095031123836748609282261028334), (Int.ofNat 287471851758689614809904622167), (Int.ofNat 63564829756468901649195432043), (Int.negOfNat 7450076192544937651537920561), (Int.negOfNat 489180173303332305561723108), (Int.ofNat 81991030167368828901433721), (Int.ofNat 2222620040428335823250008), (Int.negOfNat 554508950533163528632080), (Int.negOfNat 5919937464941053398540), (Int.ofNat 2614747221600583140032), (Int.ofNat 5858530416047831036), (Int.negOfNat 9273286284848296250), (Int.ofNat 40673345959837565), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(1323508415242450103649109573963161/1125899906842624000000000000000000), (-98476488521458382002708097198611/5629499534213120000000000000000000), (95008139950410937563216072981/21990232555520000000000000000000), (578127245548840431521924586377/562949953421312000000000000000000), (-2047515561918374304641130514167/2814749767106560000000000000000000), (287471851758689614809904622167/5629499534213120000000000000000000), (63564829756468901649195432043/5629499534213120000000000000000000), (-7450076192544937651537920561/5629499534213120000000000000000000), (-122295043325833076390430777/1407374883553280000000000000000000), (81991030167368828901433721/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial156.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial156.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial156.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial156 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 6510838641331497375369645975302783), (Int.negOfNat 31296205538700671015773339177006), (Int.negOfNat 6512966910337029539485278112345), (Int.negOfNat 9906795949324378123487399762778), (Int.ofNat 296899389016245983990738530043), (Int.ofNat 372351963593797038315903786183), (Int.negOfNat 40950337338923689692177993761), (Int.negOfNat 4139187607106197168279089691), (Int.ofNat 709498534681699594501265068), (Int.ofNat 21554836357867169975975063), (Int.negOfNat 6276744072259514637826676), (Int.negOfNat 43029493307126456369984), (Int.ofNat 35883076272564024585928), (Int.negOfNat 145473002008937221270), (Int.negOfNat 146965578569145389944), (Int.ofNat 1510961732194924604), (Int.ofNat 481571391621360977), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(6510838641331497375369645975302783/5629499534213120000000000000000000), (-15648102769350335507886669588503/2814749767106560000000000000000000), (-1302593382067405907897055622469/1125899906842624000000000000000000), (-4953397974662189061743699881389/2814749767106560000000000000000000), (296899389016245983990738530043/5629499534213120000000000000000000), (372351963593797038315903786183/5629499534213120000000000000000000), (-40950337338923689692177993761/5629499534213120000000000000000000), (-4139187607106197168279089691/5629499534213120000000000000000000), (177374633670424898625316267/1407374883553280000000000000000000), (21554836357867169975975063/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial156.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial156.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial156.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial156 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 6356641306122179424982859009178021), (Int.negOfNat 145913082755113037766403695962068), (Int.negOfNat 40350039683884441926469555096289), (Int.negOfNat 214554985165391242592674183847), (Int.ofNat 1204147345739088893559527549732), (Int.negOfNat 153874345609122267631566172952), (Int.negOfNat 24691914478149045544653977731), (Int.ofNat 4897626322737512163007174515), (Int.ofNat 163428985304617447842948674), (Int.negOfNat 60295042624101495791010519), (Int.negOfNat 88444630587859683596894), (Int.ofNat 431680490483532888021968), (Int.negOfNat 5155217765830671212284), (Int.negOfNat 2094001264849445958260), (Int.ofNat 39279017559352982966), (Int.ofNat 7637189525463897000), (Int.negOfNat 203272641260083325), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(6356641306122179424982859009178021/5629499534213120000000000000000000), (-36478270688778259441600923990517/1407374883553280000000000000000000), (-40350039683884441926469555096289/5629499534213120000000000000000000), (-214554985165391242592674183847/5629499534213120000000000000000000), (301036836434772223389881887433/1407374883553280000000000000000000), (-19234293201140283453945771619/703687441776640000000000000000000), (-24691914478149045544653977731/5629499534213120000000000000000000), (979525264547502432601434903/1125899906842624000000000000000000), (81714492652308723921474337/2814749767106560000000000000000000), (-60295042624101495791010519/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial156.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial156.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial156.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial156 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 5915099256987240081750205094464830), (Int.negOfNat 286179235738492410817410510340049), (Int.negOfNat 27657135384805766689381443279968), (Int.ofNat 2040056888952434298028811414147), (Int.negOfNat 489159652639974348875452177756), (Int.negOfNat 76215975850182067192769045705), (Int.ofNat 27028034709744587718401839347), (Int.ofNat 691904468390087608941245353), (Int.negOfNat 482155263964262708650704348), (Int.ofNat 4419681567084660900244009), (Int.ofNat 4471194216815715099436140), (Int.negOfNat 105265342006787390492842), (Int.negOfNat 26282206140990113108100), (Int.ofNat 807395601219724807664), (Int.ofNat 108434748983038143654), (Int.negOfNat 3827236672165165484), (Int.negOfNat 389153746533239611), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(591509925698724008175020509446483/562949953421312000000000000000000), (-286179235738492410817410510340049/5629499534213120000000000000000000), (-864285480775180209043170102499/175921860444160000000000000000000), (2040056888952434298028811414147/5629499534213120000000000000000000), (-122289913159993587218863044439/1407374883553280000000000000000000), (-15243195170036413438553809141/1125899906842624000000000000000000), (27028034709744587718401839347/5629499534213120000000000000000000), (691904468390087608941245353/5629499534213120000000000000000000), (-120538815991065677162676087/1407374883553280000000000000000000), (4419681567084660900244009/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial156.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial156.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial156.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial156 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 5239868686057875145186376514457278), (Int.negOfNat 389040554454666791575197493892541), (Int.negOfNat 27098938643709975568684440788279), (Int.negOfNat 988589418574308961167489616787), (Int.ofNat 94612545215163601807842609621), (Int.ofNat 129787147753706076144030019910), (Int.negOfNat 2154935533414212015423081389), (Int.negOfNat 3187090568366016934161762489), (Int.ofNat 105253170883511999708153468), (Int.ofNat 39032033717886809831011169), (Int.negOfNat 1689189389028916715215312), (Int.negOfNat 284204526589268760105908), (Int.ofNat 13967179085314851298028), (Int.ofNat 1389615740152085479620), (Int.negOfNat 73494585067054601166), (Int.negOfNat 5041383331326347868), (Int.ofNat 286193584801554201), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(2619934343028937572593188257228639/2814749767106560000000000000000000), (-389040554454666791575197493892541/5629499534213120000000000000000000), (-27098938643709975568684440788279/5629499534213120000000000000000000), (-988589418574308961167489616787/5629499534213120000000000000000000), (94612545215163601807842609621/5629499534213120000000000000000000), (12978714775370607614403001991/562949953421312000000000000000000), (-2154935533414212015423081389/5629499534213120000000000000000000), (-3187090568366016934161762489/5629499534213120000000000000000000), (26313292720877999927038367/1407374883553280000000000000000000), (39032033717886809831011169/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial156.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial156.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial156.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial156 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 4350648917894541118230007613655004), (Int.negOfNat 497544106054416483195151426831710), (Int.negOfNat 22693565995747711701249785442716), (Int.ofNat 3192653457671118478953776591054), (Int.ofNat 613547806229700429557749309594), (Int.negOfNat 58184379334045389593751094201), (Int.negOfNat 17568905594297999881123450387), (Int.ofNat 1463461047903618703895885391), (Int.ofNat 279362490019955015869179960), (Int.negOfNat 22609480535526970987515489), (Int.negOfNat 2559184843724643871367426), (Int.ofNat 208537461190751962346072), (Int.ofNat 14992669954214506258284), (Int.negOfNat 1248555821013369579084), (Int.negOfNat 61231595794781706294), (Int.ofNat 5289285737664879612), (Int.ofNat 255275629674382807), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(1087662229473635279557501903413751/1407374883553280000000000000000000), (-49754410605441648319515142683171/562949953421312000000000000000000), (-5673391498936927925312446360679/1407374883553280000000000000000000), (1596326728835559239476888295527/2814749767106560000000000000000000), (306773903114850214778874654797/2814749767106560000000000000000000), (-58184379334045389593751094201/5629499534213120000000000000000000), (-17568905594297999881123450387/5629499534213120000000000000000000), (1463461047903618703895885391/5629499534213120000000000000000000), (6984062250498875396729499/140737488355328000000000000000000), (-22609480535526970987515489/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial156.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial156.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial156.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial156 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 3297403244863686692119160482347206), (Int.negOfNat 537521831216483331804616469485092), (Int.ofNat 3673279700161282094963510714220), (Int.ofNat 4132030422859875875137825096140), (Int.negOfNat 415127846950256969315169384285), (Int.negOfNat 79915062540946133310962719752), (Int.ofNat 14078455105129110199482996985), (Int.ofNat 1547036423986225536943635907), (Int.negOfNat 252748270858921721063385768), (Int.negOfNat 17898848513523841921161271), (Int.ofNat 2703004963141089171998336), (Int.ofNat 126793572153788007974034), (Int.negOfNat 18771972928678176195520), (Int.negOfNat 597995295744501452434), (Int.ofNat 90737876944517578776), (Int.ofNat 1999008649257359408), (Int.negOfNat 302175469913596675), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(1648701622431843346059580241173603/2814749767106560000000000000000000), (-134380457804120832951154117371273/1407374883553280000000000000000000), (183663985008064104748175535711/281474976710656000000000000000000), (206601521142993793756891254807/281474976710656000000000000000000), (-83025569390051393863033876857/1125899906842624000000000000000000), (-9989382817618266663870339969/703687441776640000000000000000000), (2815691021025822039896599397/1125899906842624000000000000000000), (1547036423986225536943635907/5629499534213120000000000000000000), (-31593533857365215132923221/703687441776640000000000000000000), (-17898848513523841921161271/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial156.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial156.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial156.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial156 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 2261937738372648272851281464703186), (Int.negOfNat 489810775811656007539202665801853), (Int.ofNat 16025603561907188876493632403467), (Int.ofNat 228803298987280034438693569834), (Int.negOfNat 252464757128814113712383385475), (Int.ofNat 93204224123769499481052229773), (Int.ofNat 5188368076087587719020037219), (Int.negOfNat 2310276144150762378894113455), (Int.negOfNat 76339524046510344661574484), (Int.ofNat 30143539607994319809012687), (Int.ofNat 645412434353845425358380), (Int.negOfNat 247826647168010505375990), (Int.negOfNat 3322901097949350701248), (Int.ofNat 1390767317741971567992), (Int.ofNat 10967638627541234116), (Int.negOfNat 5651453164114630662), (Int.negOfNat 92676334374137047), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(1130968869186324136425640732351593/2814749767106560000000000000000000), (-489810775811656007539202665801853/5629499534213120000000000000000000), (16025603561907188876493632403467/5629499534213120000000000000000000), (114401649493640017219346784917/2814749767106560000000000000000000), (-10098590285152564548495335419/225179981368524800000000000000000), (93204224123769499481052229773/5629499534213120000000000000000000), (5188368076087587719020037219/5629499534213120000000000000000000), (-462055228830152475778822691/1125899906842624000000000000000000), (-19084881011627586165393621/1407374883553280000000000000000000), (30143539607994319809012687/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial156.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial156.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial156.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial156 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 1347224508368736903675126475702009), (Int.negOfNat 423632308976574348111328494833403), (Int.ofNat 18490864192574341126765743900137), (Int.ofNat 1498365957746477034470030397441), (Int.ofNat 378330750770570873192882369394), (Int.negOfNat 14036784427205021511629244178), (Int.negOfNat 16841056689366946963986066483), (Int.ofNat 184330808914121258097705265), (Int.ofNat 283859298805241848152602266), (Int.negOfNat 2437416359754869160449285), (Int.negOfNat 2838014014656798545584160), (Int.ofNat 24958438505294787786588), (Int.ofNat 18823357338489112310966), (Int.negOfNat 177770014163116400804), (Int.negOfNat 88410977944383911652), (Int.ofNat 927643140409344582), (Int.ofNat 263957589925557229), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(1347224508368736903675126475702009/5629499534213120000000000000000000), (-423632308976574348111328494833403/5629499534213120000000000000000000), (18490864192574341126765743900137/5629499534213120000000000000000000), (1498365957746477034470030397441/5629499534213120000000000000000000), (189165375385285436596441184697/2814749767106560000000000000000000), (-7018392213602510755814622089/2814749767106560000000000000000000), (-16841056689366946963986066483/5629499534213120000000000000000000), (36866161782824251619541053/1125899906842624000000000000000000), (141929649402620924076301133/2814749767106560000000000000000000), (-487483271950973832089857/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial156.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial156.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial156.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial156 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 590528795722106393787916623278195), (Int.negOfNat 323584472185708102715797135951708), (Int.ofNat 31986737082675982071215306969655), (Int.ofNat 1827236518946402244698236930379), (Int.negOfNat 447647757796572062941256487097), (Int.negOfNat 98774129246603296842403305231), (Int.ofNat 7737788459550795394219283341), (Int.ofNat 2204169905466149952497925525), (Int.negOfNat 111492152040865857690326860), (Int.negOfNat 27583980220081752512983617), (Int.ofNat 1083557780253680006120716), (Int.ofNat 220576041961433984618068), (Int.negOfNat 7286094085513269213696), (Int.negOfNat 1216916407402471307892), (Int.ofNat 35427025683161489270), (Int.ofNat 4904146701904050348), (Int.negOfNat 69922960926108713), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(118105759144421278757583324655639/1125899906842624000000000000000000), (-80896118046427025678949283987927/1407374883553280000000000000000000), (6397347416535196414243061393931/1125899906842624000000000000000000), (1827236518946402244698236930379/5629499534213120000000000000000000), (-447647757796572062941256487097/5629499534213120000000000000000000), (-98774129246603296842403305231/5629499534213120000000000000000000), (7737788459550795394219283341/5629499534213120000000000000000000), (88166796218645998099917021/225179981368524800000000000000000), (-5574607602043292884516343/281474976710656000000000000000000), (-27583980220081752512983617/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial156.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial156.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial156.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial156 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 76337765009436230484267835378247), (Int.negOfNat 193634148486343136612740819840074), (Int.ofNat 27334074384328874448117672811249), (Int.negOfNat 3555796666043601523380255996574), (Int.negOfNat 567483986322511194393783722382), (Int.ofNat 87841789702748665354482353298), (Int.ofNat 13814493634954944765971462621), (Int.negOfNat 1642685164329324927560334973), (Int.negOfNat 219392826817002547013921534), (Int.ofNat 19431235810984352312647537), (Int.ofNat 2167216850453133481180468), (Int.negOfNat 151881299241877135770310), (Int.negOfNat 14321063074413699982494), (Int.ofNat 833215296299646868220), (Int.ofNat 67134546682060598688), (Int.negOfNat 3491109533288955092), (Int.negOfNat 225739709937517783), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(76337765009436230484267835378247/5629499534213120000000000000000000), (-96817074243171568306370409920037/2814749767106560000000000000000000), (27334074384328874448117672811249/5629499534213120000000000000000000), (-1777898333021800761690127998287/2814749767106560000000000000000000), (-283741993161255597196891861191/2814749767106560000000000000000000), (43920894851374332677241176649/2814749767106560000000000000000000), (13814493634954944765971462621/5629499534213120000000000000000000), (-1642685164329324927560334973/5629499534213120000000000000000000), (-109696413408501273506960767/2814749767106560000000000000000000), (19431235810984352312647537/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial156.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial156.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial156.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial156 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 235679908820585791123636538229841), (Int.negOfNat 136353899628606656506027275929635), (Int.ofNat 1334879518796784053732849747728), (Int.negOfNat 3554724416750067398676234070076), (Int.ofNat 533738773725337288099147251714), (Int.ofNat 68380769158834463017196191545), (Int.negOfNat 16283204343697568286533266809), (Int.negOfNat 1324811782998287769224493375), (Int.ofNat 250428317528490619193855994), (Int.ofNat 16658015962659157744556375), (Int.negOfNat 2382603364535016466015816), (Int.negOfNat 135767647630441977386032), (Int.ofNat 15347256665285529709362), (Int.ofNat 764469570561536264698), (Int.negOfNat 71001733833729813750), (Int.negOfNat 3193848235483622266), (Int.ofNat 219782962897007991), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-235679908820585791123636538229841/5629499534213120000000000000000000), (-27270779925721331301205455185927/1125899906842624000000000000000000), (83429969924799003358303109233/351843720888320000000000000000000), (-888681104187516849669058517519/1407374883553280000000000000000000), (266869386862668644049573625857/2814749767106560000000000000000000), (13676153831766892603439238309/1125899906842624000000000000000000), (-16283204343697568286533266809/5629499534213120000000000000000000), (-10598494263986302153795947/45035996273704960000000000000000), (125214158764245309596927997/2814749767106560000000000000000000), (133264127701273261956451/45035996273704960000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial156.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial156.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial156.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial156 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 521899692742603864070207429092138), (Int.negOfNat 154559363645223213389881024543405), (Int.negOfNat 6016129931896495466365884186122), (Int.ofNat 601093586945479516596840817661), (Int.ofNat 181639674971620581955923561617), (Int.negOfNat 114027562007582489227504138816), (Int.negOfNat 4586152825259525409258497331), (Int.ofNat 2514753282324428348684355515), (Int.ofNat 79882464332215188366383616), (Int.negOfNat 30259399103376722328114765), (Int.negOfNat 865373309548100990002394), (Int.ofNat 234965777319957150986088), (Int.ofNat 6189463401143971595238), (Int.negOfNat 1271101147258753808282), (Int.negOfNat 31056486953381847970), (Int.ofNat 5138595850594398814), (Int.ofNat 91861593078660979), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-260949846371301932035103714546069/2814749767106560000000000000000000), (-30911872729044642677976204908681/1125899906842624000000000000000000), (-3008064965948247733182942093061/2814749767106560000000000000000000), (601093586945479516596840817661/5629499534213120000000000000000000), (181639674971620581955923561617/5629499534213120000000000000000000), (-1781680656368476394179752169/87960930222080000000000000000000), (-4586152825259525409258497331/5629499534213120000000000000000000), (502950656464885669736871103/1125899906842624000000000000000000), (156020438148857789778093/10995116277760000000000000000000), (-6051879820675344465622953/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial156.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial156.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial156.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial156 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 850983896844153226964736434186140), (Int.negOfNat 174464047488865944182481184030656), (Int.negOfNat 6582613882950458255229031278053), (Int.negOfNat 1854994942049423879869662393179), (Int.negOfNat 563615593286118204266861731178), (Int.ofNat 17124343754803069020885218799), (Int.ofNat 19875414849072954026485675559), (Int.negOfNat 142320674236030736392910973), (Int.negOfNat 315356405355944257654761576), (Int.ofNat 174693858519371856683217), (Int.ofNat 3036557903263814966290372), (Int.ofNat 10139928613134099032960), (Int.negOfNat 19611653256468775176146), (Int.negOfNat 111890808322081462560), (Int.ofNat 90556118905062343532), (Int.ofNat 769225047414041248), (Int.negOfNat 302703906438478867), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-42549194842207661348236821709307/281474976710656000000000000000000), (-2726000742013530377851268500479/87960930222080000000000000000000), (-6582613882950458255229031278053/5629499534213120000000000000000000), (-1854994942049423879869662393179/5629499534213120000000000000000000), (-281807796643059102133430865589/2814749767106560000000000000000000), (17124343754803069020885218799/5629499534213120000000000000000000), (19875414849072954026485675559/5629499534213120000000000000000000), (-142320674236030736392910973/5629499534213120000000000000000000), (-39419550669493032206845197/703687441776640000000000000000000), (174693858519371856683217/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial156.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial156.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial156.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial156 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 1248376059231075154015730777018506), (Int.negOfNat 236275212428003694020621288391176), (Int.negOfNat 25725306776787047918915455166625), (Int.negOfNat 3097863318293480636540415649965), (Int.ofNat 446613980057927520532354886785), (Int.ofNat 125600538378570131555966395514), (Int.negOfNat 8082471041639205612260994201), (Int.negOfNat 2664544029044005611243342045), (Int.ofNat 104728833545444555004436690), (Int.ofNat 32893458223166493757754233), (Int.negOfNat 819339347736517427003556), (Int.negOfNat 260116714609767913184262), (Int.ofNat 4148404740500553676396), (Int.ofNat 1421203170783484181608), (Int.negOfNat 14853201278687260350), (Int.negOfNat 5766014406346374032), (Int.ofNat 83476995550931263), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-624188029615537577007865388509253/2814749767106560000000000000000000), (-29534401553500461752577661048897/703687441776640000000000000000000), (-205802454214296383351323641333/45035996273704960000000000000000), (-619572663658696127308083129993/1125899906842624000000000000000000), (89322796011585504106470977357/1125899906842624000000000000000000), (62800269189285065777983197757/2814749767106560000000000000000000), (-8082471041639205612260994201/5629499534213120000000000000000000), (-532908805808801122248668409/1125899906842624000000000000000000), (10472883354544455500443669/562949953421312000000000000000000), (32893458223166493757754233/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial156.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial156.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial156.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial156 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 1838261608088358104301590220592506), (Int.negOfNat 354580580593544849829489125854812), (Int.negOfNat 26953094010061317143790666455561), (Int.ofNat 3055529453977349377477928711703), (Int.ofNat 700538119693561294276298835403), (Int.negOfNat 95420089217160508024671400124), (Int.negOfNat 17618051872174005527653876029), (Int.ofNat 1833854422682174176973185245), (Int.ofNat 290232785971171485228103594), (Int.negOfNat 19748837494828182145285735), (Int.negOfNat 2913161157092363789892160), (Int.ofNat 134496674670002576575128), (Int.ofNat 19321437563569991175034), (Int.negOfNat 632564109715937182464), (Int.negOfNat 90390924386653943928), (Int.ofNat 2087285069714540242), (Int.ofNat 264486026450439421), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-919130804044179052150795110296253/2814749767106560000000000000000000), (-88645145148386212457372281463703/1407374883553280000000000000000000), (-26953094010061317143790666455561/5629499534213120000000000000000000), (3055529453977349377477928711703/5629499534213120000000000000000000), (700538119693561294276298835403/5629499534213120000000000000000000), (-23855022304290127006167850031/1407374883553280000000000000000000), (-17618051872174005527653876029/5629499534213120000000000000000000), (366770884536434835394637049/1125899906842624000000000000000000), (145116392985585742614051797/2814749767106560000000000000000000), (-3949767498965636429057147/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial156.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial156.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial156.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial156 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 2623467011450316126231111289744002), (Int.negOfNat 413265361565125068738247113820067), (Int.negOfNat 2036096027970569841878791729153), (Int.ofNat 3427892431528758691300386036596), (Int.negOfNat 583172683020228368289708192196), (Int.negOfNat 80430442729401529413446068994), (Int.ofNat 20432921699086552314260019421), (Int.ofNat 1932943263949949087040786105), (Int.negOfNat 299788974472171194876968136), (Int.negOfNat 26352767291749614642309473), (Int.ofNat 2596455041148926784653480), (Int.ofNat 221091701107672655092780), (Int.negOfNat 14994394270203748160272), (Int.negOfNat 1253703629934366558768), (Int.ofNat 61822760392617552044), (Int.ofNat 5188434362304920218), (Int.negOfNat 246076290851177023), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-1311733505725158063115555644872001/2814749767106560000000000000000000), (-413265361565125068738247113820067/5629499534213120000000000000000000), (-2036096027970569841878791729153/5629499534213120000000000000000000), (856973107882189672825096509149/1407374883553280000000000000000000), (-145793170755057092072427048049/1407374883553280000000000000000000), (-40215221364700764706723034497/2814749767106560000000000000000000), (20432921699086552314260019421/5629499534213120000000000000000000), (386588652789989817408157221/1125899906842624000000000000000000), (-37473621809021399359621017/703687441776640000000000000000000), (-26352767291749614642309473/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial156.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial156.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial156.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial156 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 3441155590154801311361732354209090), (Int.negOfNat 400934261685327507361577277305989), (Int.ofNat 3679812973122944484813874240530), (Int.negOfNat 734666297049527936949706847540), (Int.negOfNat 20343313907515883767809244150), (Int.ofNat 165318358611564018395103681676), (Int.ofNat 7098185533871381128164502245), (Int.negOfNat 3481951748309214934727739533), (Int.negOfNat 169993429359633448683871982), (Int.ofNat 38731359796643699302652029), (Int.ofNat 1987492572250732008855304), (Int.negOfNat 274416351937651649419466), (Int.negOfNat 14355824044377319464100), (Int.ofNat 1350293155403906789526), (Int.ofNat 71343447222907837524), (Int.negOfNat 4797408850456355932), (Int.negOfNat 226268146462399975), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-344115559015480131136173235420909/562949953421312000000000000000000), (-400934261685327507361577277305989/5629499534213120000000000000000000), (367981297312294448481387424053/562949953421312000000000000000000), (-36733314852476396847485342377/281474976710656000000000000000000), (-406866278150317675356184883/112589990684262400000000000000000), (41329589652891004598775920419/1407374883553280000000000000000000), (1419637106774276225632900449/1125899906842624000000000000000000), (-3481951748309214934727739533/5629499534213120000000000000000000), (-84996714679816724341935991/2814749767106560000000000000000000), (38731359796643699302652029/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial156.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial156.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial156.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial156 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 4229231164931473121211457473772397), (Int.negOfNat 382731610839816398066628423613090), (Int.ofNat 11261018837170420421644911595832), (Int.ofNat 4822487588765086074991452349395), (Int.ofNat 1063410342245566046526276484313), (Int.negOfNat 33103379700282265617794562036), (Int.negOfNat 32551912528131992627541172133), (Int.negOfNat 359035823900359603852366059), (Int.ofNat 473578761589095844948233720), (Int.ofNat 10998876627404272692981271), (Int.negOfNat 4173608148322652380698094), (Int.negOfNat 120486594178899898669368), (Int.ofNat 24640809573501928887796), (Int.ofNat 783734519559342177196), (Int.negOfNat 104178562342873724146), (Int.negOfNat 3552337602920520968), (Int.ofNat 408675586151422783), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-4229231164931473121211457473772397/5629499534213120000000000000000000), (-38273161083981639806662842361309/562949953421312000000000000000000), (1407627354646302552705613949479/703687441776640000000000000000000), (964497517753017214998290469879/1125899906842624000000000000000000), (1063410342245566046526276484313/5629499534213120000000000000000000), (-8275844925070566404448640509/1407374883553280000000000000000000), (-32551912528131992627541172133/5629499534213120000000000000000000), (-359035823900359603852366059/5629499534213120000000000000000000), (11839469039727396123705843/140737488355328000000000000000000), (10998876627404272692981271/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial156.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial156.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial156.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial156 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 4897121979601902332940312956155505), (Int.negOfNat 254359444364276890631257301216334), (Int.ofNat 55865403682341309635681119642736), (Int.ofNat 7437778859674193303616318222303), (Int.negOfNat 804399536558723647946617794438), (Int.negOfNat 254124812805700293305032909138), (Int.ofNat 8592371781587313216910208449), (Int.ofNat 4820452064495544119889899071), (Int.negOfNat 32979667674257092731290338), (Int.negOfNat 53896855727908306536549001), (Int.negOfNat 339826720273162897417968), (Int.ofNat 387805132330487876535892), (Int.ofNat 5246292165050011351072), (Int.negOfNat 1933527121647589858320), (Int.negOfNat 33986293711860838834), (Int.ofNat 7113683790426596812), (Int.ofNat 133850501374278609), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-979424395920380466588062591231101/1125899906842624000000000000000000), (-127179722182138445315628650608167/2814749767106560000000000000000000), (3491587730146331852230069977671/351843720888320000000000000000000), (7437778859674193303616318222303/5629499534213120000000000000000000), (-402199768279361823973308897219/2814749767106560000000000000000000), (-127062406402850146652516454569/2814749767106560000000000000000000), (8592371781587313216910208449/5629499534213120000000000000000000), (4820452064495544119889899071/5629499534213120000000000000000000), (-16489833837128546365645169/2814749767106560000000000000000000), (-53896855727908306536549001/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial156.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial156.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial156.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial156 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 5142748066077278768528881163485175), (Int.ofNat 15938747016538287052135892724971), (Int.ofNat 65857604661197364673191080771816), (Int.negOfNat 5425852460430492563454820507566), (Int.negOfNat 1722872186188937668019758052149), (Int.ofNat 139079161356718120781319888970), (Int.ofNat 40635810003473305255480193053), (Int.negOfNat 1829321434970972766470941967), (Int.negOfNat 590998813342527788014281912), (Int.ofNat 11894453588309047962825829), (Int.ofNat 5307022929029808766398100), (Int.negOfNat 31081484053713681804492), (Int.negOfNat 31687169721256383644040), (Int.negOfNat 72263913180008053956), (Int.ofNat 134719387821099199346), (Int.ofNat 956531408782971836), (Int.negOfNat 491596529692893659), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-205709922643091150741155246539407/225179981368524800000000000000000), (15938747016538287052135892724971/5629499534213120000000000000000000), (8232200582649670584148885096477/703687441776640000000000000000000), (-2712926230215246281727410253783/2814749767106560000000000000000000), (-1722872186188937668019758052149/5629499534213120000000000000000000), (13907916135671812078131988897/562949953421312000000000000000000), (40635810003473305255480193053/5629499534213120000000000000000000), (-1829321434970972766470941967/5629499534213120000000000000000000), (-73874851667815973501785239/703687441776640000000000000000000), (11894453588309047962825829/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial156.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial156.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial156.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial156 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 4911735819368484015330042912202717), (Int.ofNat 176684175393861084228590771037873), (Int.ofNat 10657079334167690250282770018725), (Int.negOfNat 9086766236616655551331442492980), (Int.ofNat 1046007152845904008269481642193), (Int.ofNat 271035628457378147059024949496), (Int.negOfNat 27588549552604831160726521379), (Int.negOfNat 5394607607260250793333496115), (Int.ofNat 308678656714926061525566376), (Int.ofNat 62914624387669244318010581), (Int.negOfNat 1875625681425245984874246), (Int.negOfNat 459871847564324895136972), (Int.ofNat 6866938452377356982444), (Int.ofNat 2302983070315460726740), (Int.negOfNat 14646160940041769526), (Int.negOfNat 8575732855926310940), (Int.ofNat 27615484578195), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-4911735819368484015330042912202717/5629499534213120000000000000000000), (176684175393861084228590771037873/5629499534213120000000000000000000), (426283173366707610011310800749/225179981368524800000000000000000), (-454338311830832777566572124649/281474976710656000000000000000000), (1046007152845904008269481642193/5629499534213120000000000000000000), (33879453557172268382378118687/703687441776640000000000000000000), (-27588549552604831160726521379/5629499534213120000000000000000000), (-1078921521452050158666699223/1125899906842624000000000000000000), (38584832089365757690695797/703687441776640000000000000000000), (62914624387669244318010581/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial156.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial156.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial156.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial156 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 4565371785483585049032185269877422), (Int.ofNat 158159138020919490131797734901042), (Int.negOfNat 6513599489820321899690300927899), (Int.ofNat 3532135971650039787634666952756), (Int.ofNat 1146993764643918807710457378512), (Int.negOfNat 275358211132298072811669390718), (Int.negOfNat 38483718242331656848401004699), (Int.ofNat 4782278908573749331579753249), (Int.ofNat 636242759784727308368355612), (Int.negOfNat 40835501900251371642364227), (Int.negOfNat 5897621557515759096226974), (Int.ofNat 215265796865373916623616), (Int.ofNat 35344363304293988711932), (Int.negOfNat 780705772985686771230), (Int.negOfNat 149768194924877466556), (Int.ofNat 2085843273286016624), (Int.ofNat 507578414804936133), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-2282685892741792524516092634938711/2814749767106560000000000000000000), (79079569010459745065898867450521/2814749767106560000000000000000000), (-6513599489820321899690300927899/5629499534213120000000000000000000), (883033992912509946908666738189/1407374883553280000000000000000000), (71687110290244925481903586157/351843720888320000000000000000000), (-137679105566149036405834695359/2814749767106560000000000000000000), (-38483718242331656848401004699/5629499534213120000000000000000000), (4782278908573749331579753249/5629499534213120000000000000000000), (159060689946181827092088903/1407374883553280000000000000000000), (-40835501900251371642364227/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial156.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial156.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial156.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial156 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 4239024700329810721112905034325814), (Int.ofNat 184449569477560559387263636767524), (Int.ofNat 15048317955473033977603762505700), (Int.negOfNat 942793662302127094755294678403), (Int.negOfNat 2094752936935803640452032375193), (Int.negOfNat 170749944230764129038537771128), (Int.ofNat 57464727532999054290551947965), (Int.ofNat 5306904136716825481899245179), (Int.negOfNat 654101916560662774812557202), (Int.negOfNat 66457496036473542353239529), (Int.ofNat 4401048010950238356184442), (Int.ofNat 487318542512369580889790), (Int.negOfNat 20219510279712744386180), (Int.negOfNat 2420125021147225397448), (Int.ofNat 68253224273884376604), (Int.ofNat 8937900282376061990), (Int.negOfNat 162626910784823955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-2119512350164905360556452517162907/2814749767106560000000000000000000), (46112392369390139846815909191881/1407374883553280000000000000000000), (150483179554730339776037625057/56294995342131200000000000000000), (-942793662302127094755294678403/5629499534213120000000000000000000), (-2094752936935803640452032375193/5629499534213120000000000000000000), (-21343743028845516129817221391/703687441776640000000000000000000), (11492945506599810858110389593/1125899906842624000000000000000000), (5306904136716825481899245179/5629499534213120000000000000000000), (-327050958280331387406278601/2814749767106560000000000000000000), (-66457496036473542353239529/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial156.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial156.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial156.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial156 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 3852293730641615739183123127922864), (Int.ofNat 165252436782426424427745358246823), (Int.negOfNat 38600420114062665884027270163842), (Int.negOfNat 13808753758187443101687974794007), (Int.ofNat 207393015615342674362921553414), (Int.ofNat 584737885417844634634975271358), (Int.ofNat 34180520928598933538452430697), (Int.negOfNat 8665666798123927544287390921), (Int.negOfNat 655138776750444973828585560), (Int.ofNat 72311920841763664394891083), (Int.ofNat 6044235543670634710603098), (Int.negOfNat 403248304242133009218338), (Int.negOfNat 35496466606957254525578), (Int.ofNat 1639218859546002937068), (Int.ofNat 148079512968348992532), (Int.negOfNat 5012495062952720614), (Int.negOfNat 469360534816896687), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-240768358165100983698945195495179/351843720888320000000000000000000), (165252436782426424427745358246823/5629499534213120000000000000000000), (-19300210057031332942013635081921/2814749767106560000000000000000000), (-13808753758187443101687974794007/5629499534213120000000000000000000), (103696507807671337181460776707/2814749767106560000000000000000000), (292368942708922317317487635679/2814749767106560000000000000000000), (34180520928598933538452430697/5629499534213120000000000000000000), (-8665666798123927544287390921/5629499534213120000000000000000000), (-16378469418761124345714639/140737488355328000000000000000000), (72311920841763664394891083/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial156.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial156.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial156.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial156 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 3763677777141137161935735855725532), (Int.negOfNat 99236860875143768645181997839561), (Int.negOfNat 68101090963349863863655213721522), (Int.ofNat 11143142783556376090384687878205), (Int.ofNat 5297460232340796116175224927792), (Int.ofNat 153158101720486269268158825492), (Int.negOfNat 99215510493799733878700800607), (Int.negOfNat 5727045430275268991784504599), (Int.ofNat 1011439747774745932633984696), (Int.ofNat 68029735103866010922659309), (Int.negOfNat 6763994132250779400324888), (Int.negOfNat 475385074643467070924918), (Int.ofNat 32470971595100193779924), (Int.ofNat 2282819901901696489348), (Int.negOfNat 118092906335479758090), (Int.negOfNat 8190593820165481676), (Int.ofNat 325226206085069715), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-940919444285284290483933963931383/1407374883553280000000000000000000), (-99236860875143768645181997839561/5629499534213120000000000000000000), (-34050545481674931931827606860761/2814749767106560000000000000000000), (2228628556711275218076937575641/1125899906842624000000000000000000), (331091264521299757260951557987/351843720888320000000000000000000), (38289525430121567317039706373/1407374883553280000000000000000000), (-99215510493799733878700800607/5629499534213120000000000000000000), (-5727045430275268991784504599/5629499534213120000000000000000000), (126429968471843241579248087/703687441776640000000000000000000), (68029735103866010922659309/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial156.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial156.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial156.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial156 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 4062547142587167305433003514023685), (Int.negOfNat 76613857498332828285347332783414), (Int.ofNat 112526344262608823305243330572966), (Int.ofNat 42625998828782021601161308509932), (Int.ofNat 573467394672272873016957070829), (Int.negOfNat 992926632649105400507767581185), (Int.negOfNat 47838805234727357139367021585), (Int.ofNat 12259534965357168957858974629), (Int.ofNat 714088013911132842712039228), (Int.negOfNat 98128902512203274964858635), (Int.negOfNat 5880940440573697685342256), (Int.ofNat 555877205811271443324260), (Int.ofNat 32364949991901033559006), (Int.negOfNat 2349478189831872626884), (Int.negOfNat 129584827731170321468), (Int.ofNat 7575961455832331124), (Int.ofNat 431142654828857241), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-812509428517433461086600702804737/1125899906842624000000000000000000), (-38306928749166414142673666391707/2814749767106560000000000000000000), (56263172131304411652621665286483/2814749767106560000000000000000000), (10656499707195505400290327127483/1407374883553280000000000000000000), (573467394672272873016957070829/5629499534213120000000000000000000), (-198585326529821080101553516237/1125899906842624000000000000000000), (-9567761046945471427873404317/1125899906842624000000000000000000), (12259534965357168957858974629/5629499534213120000000000000000000), (178522003477783210678009807/1407374883553280000000000000000000), (-19625780502440654992971727/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial156.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial156.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial156.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial156 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 3448624334537345134061867482038541), (Int.ofNat 820709498183349350429032923294210), (Int.ofNat 300145662126688254232892132207083), (Int.ofNat 7395933908262134207444061270244), (Int.negOfNat 8441761906056488410729478694188), (Int.negOfNat 443694854343136410323671955804), (Int.ofNat 127608640251320269177568558907), (Int.ofNat 7363524849439669611215603099), (Int.negOfNat 1235034495069521787252343530), (Int.negOfNat 68775635372674119949083967), (Int.ofNat 8324794644631838950768988), (Int.ofNat 426687974153446606674682), (Int.negOfNat 41144488874615300624190), (Int.negOfNat 1908733565021809568754), (Int.ofNat 154841290561108330170), (Int.ofNat 6480295353745053594), (Int.negOfNat 475086208055968993), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-3448624334537345134061867482038541/5629499534213120000000000000000000), (82070949818334935042903292329421/562949953421312000000000000000000), (300145662126688254232892132207083/5629499534213120000000000000000000), (1848983477065533551861015317561/1407374883553280000000000000000000), (-2110440476514122102682369673547/1407374883553280000000000000000000), (-110923713585784102580917988951/1407374883553280000000000000000000), (127608640251320269177568558907/5629499534213120000000000000000000), (7363524849439669611215603099/5629499534213120000000000000000000), (-123503449506952178725234353/562949953421312000000000000000000), (-68775635372674119949083967/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial156.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial156.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial156.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial156.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial156 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial156 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial156 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 4826844842579973347397191206141082), (Int.negOfNat 1027803198315173696691082138210751), (Int.ofNat 340810782085028006008737117099009), (Int.negOfNat 5647374459227264048641758269414), (Int.negOfNat 8658256245402903140184759944739), (Int.ofNat 438684217532947457175299496575), (Int.ofNat 128091633999998786506915142225), (Int.negOfNat 7356044280076256075234283349), (Int.negOfNat 1235626199838373885118697130), (Int.ofNat 68768753901050616554366417), (Int.ofNat 8325250769142419157517638), (Int.negOfNat 426683477115238098918282), (Int.negOfNat 41144488874615300624190), (Int.ofNat 1908733565021809568754), (Int.ofNat 154841290561108330170), (Int.negOfNat 6480295353745053594), (Int.negOfNat 475086208055968993), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-2413422421289986673698595603070541/2814749767106560000000000000000000), (-1027803198315173696691082138210751/5629499534213120000000000000000000), (340810782085028006008737117099009/5629499534213120000000000000000000), (-2823687229613632024320879134707/2814749767106560000000000000000000), (-8658256245402903140184759944739/5629499534213120000000000000000000), (17547368701317898287011979863/225179981368524800000000000000000), (5123665359999951460276605689/225179981368524800000000000000000), (-7356044280076256075234283349/5629499534213120000000000000000000), (-123562619983837388511869713/562949953421312000000000000000000), (68768753901050616554366417/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial156.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial156.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial156.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 5681898630686931578685209630250394), (Int.ofNat 45930147498458633734925064626282), (Int.ofNat 158205964587386166887390292537102), (Int.negOfNat 42729441611587169403810383583098), (Int.ofNat 337256702494924665945358063726), (Int.ofNat 994065115502363501037432341607), (Int.negOfNat 47320395943820742976111138485), (Int.negOfNat 12262057956878958338350045629), (Int.ofNat 713458304254898051176805728), (Int.ofNat 98131653227971287922757535), (Int.negOfNat 5880456653072994002113856), (Int.negOfNat 555878892200599633732910), (Int.ofNat 32364949991901033559006), (Int.ofNat 2349478189831872626884), (Int.negOfNat 129584827731170321468), (Int.negOfNat 7575961455832331124), (Int.ofNat 431142654828857241), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-2840949315343465789342604815125197/2814749767106560000000000000000000), (22965073749229316867462532313141/2814749767106560000000000000000000), (79102982293693083443695146268551/2814749767106560000000000000000000), (-21364720805793584701905191791549/2814749767106560000000000000000000), (168628351247462332972679031863/2814749767106560000000000000000000), (994065115502363501037432341607/5629499534213120000000000000000000), (-9464079188764148595222227697/1125899906842624000000000000000000), (-12262057956878958338350045629/5629499534213120000000000000000000), (22295572007965564099275179/175921860444160000000000000000000), (19626330645594257584551507/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial156.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial156.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial156.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 5266215989882655121892036606809739), (Int.ofNat 242660423507512408589704696740804), (Int.negOfNat 28498492800645594204670874452020), (Int.negOfNat 13010305505919599698191929723505), (Int.ofNat 5102344696912472850591948998523), (Int.negOfNat 146283381672132951628748035571), (Int.negOfNat 98799518472068179483146292407), (Int.ofNat 5715291627475650262115109599), (Int.ofNat 1010942247449707519401857746), (Int.negOfNat 68018145726583971480971559), (Int.negOfNat 6763614447047841902471888), (Int.ofNat 475377766956378245820768), (Int.ofNat 32470971595100193779924), (Int.negOfNat 2282819901901696489348), (Int.negOfNat 118092906335479758090), (Int.ofNat 8190593820165481676), (Int.ofNat 325226206085069715), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-5266215989882655121892036606809739/5629499534213120000000000000000000), (60665105876878102147426174185201/1407374883553280000000000000000000), (-1424924640032279710233543722601/281474976710656000000000000000000), (-2602061101183919939638385944701/1125899906842624000000000000000000), (5102344696912472850591948998523/5629499534213120000000000000000000), (-146283381672132951628748035571/5629499534213120000000000000000000), (-98799518472068179483146292407/5629499534213120000000000000000000), (5715291627475650262115109599/5629499534213120000000000000000000), (505471123724853759700928873/2814749767106560000000000000000000), (-68018145726583971480971559/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial156.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial156.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial156.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 4927388586822841946458074106922199), (Int.ofNat 108555970183287690775537934660013), (Int.negOfNat 14242487969672706206351823069804), (Int.ofNat 10714808424940511230367562156609), (Int.ofNat 102187426527457894218717073823), (Int.negOfNat 574055275974812367684339202797), (Int.ofNat 34385181490090277317256310465), (Int.ofNat 8647942120184493185593765721), (Int.negOfNat 655370632626951948669911860), (Int.negOfNat 72294689485347269285384083), (Int.ofNat 6044407240856428724722598), (Int.ofNat 403237623776387803296888), (Int.negOfNat 35496466606957254525578), (Int.negOfNat 1639218859546002937068), (Int.ofNat 148079512968348992532), (Int.ofNat 5012495062952720614), (Int.negOfNat 469360534816896687), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-4927388586822841946458074106922199/5629499534213120000000000000000000), (108555970183287690775537934660013/5629499534213120000000000000000000), (-3560621992418176551587955767451/1407374883553280000000000000000000), (10714808424940511230367562156609/5629499534213120000000000000000000), (102187426527457894218717073823/5629499534213120000000000000000000), (-574055275974812367684339202797/5629499534213120000000000000000000), (6877036298018055463451262093/1125899906842624000000000000000000), (8647942120184493185593765721/5629499534213120000000000000000000), (-32768531631347597433495593/281474976710656000000000000000000), (-72294689485347269285384083/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial156.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial156.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial156.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 4695153243453626289480368502409015), (Int.ofNat 147182409178014904155465512138121), (Int.ofNat 19209125849544923464614094732104), (Int.negOfNat 2542992820009103175447496621890), (Int.negOfNat 2086004074594793293249131410946), (Int.ofNat 182331527212372053116884906663), (Int.ofNat 57407264694140609291784618567), (Int.negOfNat 5325752033120213274320500629), (Int.negOfNat 654007694174067590269939452), (Int.ofNat 66475646899091780076949929), (Int.ofNat 4400965733766446125575992), (Int.negOfNat 487330347237666913750340), (Int.negOfNat 20219510279712744386180), (Int.ofNat 2420125021147225397448), (Int.ofNat 68253224273884376604), (Int.negOfNat 8937900282376061990), (Int.negOfNat 162626910784823955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-939030648690725257896073700481803/1125899906842624000000000000000000), (147182409178014904155465512138121/5629499534213120000000000000000000), (2401140731193115433076761841513/703687441776640000000000000000000), (-254299282000910317544749662189/562949953421312000000000000000000), (-1043002037297396646624565705473/2814749767106560000000000000000000), (182331527212372053116884906663/5629499534213120000000000000000000), (57407264694140609291784618567/5629499534213120000000000000000000), (-5325752033120213274320500629/5629499534213120000000000000000000), (-163501923543516897567484863/1407374883553280000000000000000000), (66475646899091780076949929/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial156.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial156.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial156.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 4368974895971187925116916031704593), (Int.ofNat 149473785689228031693763557139146), (Int.negOfNat 22157216801494005149678023744805), (Int.negOfNat 6504152425057557558602761057942), (Int.ofNat 1263010408929098690687379166767), (Int.ofNat 284744825756467513802531159827), (Int.negOfNat 38782742972751210319388026349), (Int.negOfNat 4797143227948645653216927799), (Int.ofNat 636634326735728682780382612), (Int.ofNat 40849619487799632176348227), (Int.negOfNat 5897933637488766842372724), (Int.negOfNat 215274790941790932136416), (Int.ofNat 35344363304293988711932), (Int.ofNat 780705772985686771230), (Int.negOfNat 149768194924877466556), (Int.negOfNat 2085843273286016624), (Int.ofNat 507578414804936133), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-4368974895971187925116916031704593/5629499534213120000000000000000000), (74736892844614015846881778569573/2814749767106560000000000000000000), (-4431443360298801029935604748961/1125899906842624000000000000000000), (-3252076212528778779301380528971/2814749767106560000000000000000000), (1263010408929098690687379166767/5629499534213120000000000000000000), (284744825756467513802531159827/5629499534213120000000000000000000), (-38782742972751210319388026349/5629499534213120000000000000000000), (-4797143227948645653216927799/5629499534213120000000000000000000), (159158581683932170695095653/1407374883553280000000000000000000), (40849619487799632176348227/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial156.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial156.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial156.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 4184287978416327701329277871389211), (Int.ofNat 37109903251425340148799079501948), (Int.negOfNat 19364299912222331536616889767401), (Int.ofNat 7362951985214236377672006285197), (Int.ofNat 1234277382870243559768295119968), (Int.negOfNat 266284789952077631204088281808), (Int.negOfNat 28043500867410294190869399479), (Int.ofNat 5387699583916560756603540615), (Int.ofNat 309257938172805953848986626), (Int.negOfNat 62908365827629381213087631), (Int.negOfNat 1876081223122246282227046), (Int.ofNat 459868474785668514319672), (Int.ofNat 6866938452377356982444), (Int.negOfNat 2302983070315460726740), (Int.negOfNat 14646160940041769526), (Int.ofNat 8575732855926310940), (Int.ofNat 27615484578195), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-4184287978416327701329277871389211/5629499534213120000000000000000000), (9277475812856335037199769875487/1407374883553280000000000000000000), (-19364299912222331536616889767401/5629499534213120000000000000000000), (7362951985214236377672006285197/5629499534213120000000000000000000), (38571168214695111242759222499/175921860444160000000000000000000), (-16642799372004851950255517613/351843720888320000000000000000000), (-28043500867410294190869399479/5629499534213120000000000000000000), (1077539916783312151320708123/1125899906842624000000000000000000), (154628969086402976924493313/2814749767106560000000000000000000), (-62908365827629381213087631/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial156.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial156.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial156.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 4118453598402946354277986674961290), (Int.ofNat 63398917854566702928799744993799), (Int.ofNat 30279123572099923543741858830688), (Int.ofNat 5322637472569062648008699426763), (Int.negOfNat 1515657120111842841308841286624), (Int.negOfNat 140099639024191701442265683005), (Int.ofNat 40151659005286981538497875003), (Int.ofNat 1832131881463097916411251817), (Int.negOfNat 590391965307548382934606012), (Int.negOfNat 11897709456176327239255479), (Int.ofNat 5306549615758363325037000), (Int.ofNat 31084294702593999152242), (Int.negOfNat 31687169721256383644040), (Int.ofNat 72263913180008053956), (Int.ofNat 134719387821099199346), (Int.negOfNat 956531408782971836), (Int.negOfNat 491596529692893659), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-411845359840294635427798667496129/562949953421312000000000000000000), (63398917854566702928799744993799/5629499534213120000000000000000000), (946222611628122610741933088459/175921860444160000000000000000000), (5322637472569062648008699426763/5629499534213120000000000000000000), (-47364285003495088790901290207/175921860444160000000000000000000), (-28019927804838340288453136601/1125899906842624000000000000000000), (40151659005286981538497875003/5629499534213120000000000000000000), (1832131881463097916411251817/5629499534213120000000000000000000), (-147597991326887095733651503/1407374883553280000000000000000000), (-11897709456176327239255479/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial156.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial156.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial156.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 3854039513392936374593521839726158), (Int.ofNat 196602762530773078261874295629171), (Int.ofNat 24445915510234375944724976388309), (Int.negOfNat 5998919920789445945869909068483), (Int.negOfNat 634991080413728688300743458631), (Int.ofNat 247792176214712987259888599370), (Int.ofNat 8211802205347502654577725819), (Int.negOfNat 4808837563362880349444207921), (Int.negOfNat 32511793467197429803191988), (Int.ofNat 53885045611241261327328201), (Int.negOfNat 340188515270558884790868), (Int.negOfNat 387797262513622987962192), (Int.ofNat 5246292165050011351072), (Int.ofNat 1933527121647589858320), (Int.negOfNat 33986293711860838834), (Int.negOfNat 7113683790426596812), (Int.ofNat 133850501374278609), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-1927019756696468187296760919863079/2814749767106560000000000000000000), (196602762530773078261874295629171/5629499534213120000000000000000000), (24445915510234375944724976388309/5629499534213120000000000000000000), (-5998919920789445945869909068483/5629499534213120000000000000000000), (-634991080413728688300743458631/5629499534213120000000000000000000), (24779217621471298725988859937/562949953421312000000000000000000), (8211802205347502654577725819/5629499534213120000000000000000000), (-4808837563362880349444207921/5629499534213120000000000000000000), (-8127948366799357450797997/1407374883553280000000000000000000), (53885045611241261327328201/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial156.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial156.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial156.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 3413344009061325487392699425239824), (Int.ofNat 221410327322440636965008435609010), (Int.negOfNat 8048875365652876268847566385444), (Int.negOfNat 2335283749732656845606450676694), (Int.ofNat 1150382203265305525138615788306), (Int.ofNat 23362652418778275253966647831), (Int.negOfNat 32726505101872514509878514583), (Int.ofNat 376133370391774227043249259), (Int.ofNat 473780444756197106268303520), (Int.negOfNat 11015937392674591302423321), (Int.negOfNat 4173758701155344869991994), (Int.ofNat 120497836774421168060368), (Int.ofNat 24640809573501928887796), (Int.negOfNat 783734519559342177196), (Int.negOfNat 104178562342873724146), (Int.ofNat 3552337602920520968), (Int.ofNat 408675586151422783), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-213334000566332842962043714077489/351843720888320000000000000000000), (22141032732244063696500843560901/562949953421312000000000000000000), (-2012218841413219067211891596361/1407374883553280000000000000000000), (-1167641874866328422803225338347/2814749767106560000000000000000000), (575191101632652762569307894153/2814749767106560000000000000000000), (23362652418778275253966647831/5629499534213120000000000000000000), (-32726505101872514509878514583/5629499534213120000000000000000000), (376133370391774227043249259/5629499534213120000000000000000000), (2961127779726231914176897/35184372088832000000000000000000), (-11015937392674591302423321/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial156.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial156.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial156.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 3004182043589808033266495782425906), (Int.ofNat 194197993290359770328872239865152), (Int.ofNat 571076996081372064428104998360), (Int.ofNat 3509923598904517509060245191900), (Int.negOfNat 36311426364196450440618693645), (Int.negOfNat 175662928645979756551809982468), (Int.ofNat 7173741426463531338278524645), (Int.ofNat 3499734132050016930939877383), (Int.negOfNat 170111065241111058354112432), (Int.negOfNat 38748937521144787544320779), (Int.ofNat 1987592610667067460508904), (Int.ofNat 274427594533172918810466), (Int.negOfNat 14355824044377319464100), (Int.negOfNat 1350293155403906789526), (Int.ofNat 71343447222907837524), (Int.ofNat 4797408850456355932), (Int.negOfNat 226268146462399975), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-1502091021794904016633247891212953/2814749767106560000000000000000000), (3034343645161871411388628747893/87960930222080000000000000000000), (14276924902034301610702624959/140737488355328000000000000000000), (35099235989045175090602451919/56294995342131200000000000000000), (-7262285272839290088123738729/1125899906842624000000000000000000), (-43915732161494939137952495617/1407374883553280000000000000000000), (1434748285292706267655704929/1125899906842624000000000000000000), (3499734132050016930939877383/5629499534213120000000000000000000), (-10631941577569441147132027/351843720888320000000000000000000), (-38748937521144787544320779/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial156.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial156.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial156.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 2590778330475597506670926361068586), (Int.ofNat 226081004603866085906234888388843), (Int.ofNat 10325704349453420941129992954243), (Int.negOfNat 1172419042329246363304752657314), (Int.negOfNat 693274882494842105875284596455), (Int.ofNat 72399262481347019340149508837), (Int.ofNat 20732943466784773705217778991), (Int.negOfNat 1919420186953300089743577755), (Int.negOfNat 300190674771810630461432436), (Int.ofNat 26339528104340885114136223), (Int.ofNat 2596778807216135497187980), (Int.negOfNat 221083269161031703049530), (Int.negOfNat 14994394270203748160272), (Int.ofNat 1253703629934366558768), (Int.ofNat 61822760392617552044), (Int.negOfNat 5188434362304920218), (Int.negOfNat 246076290851177023), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-1295389165237798753335463180534293/2814749767106560000000000000000000), (226081004603866085906234888388843/5629499534213120000000000000000000), (10325704349453420941129992954243/5629499534213120000000000000000000), (-586209521164623181652376328657/2814749767106560000000000000000000), (-138654976498968421175056919291/1125899906842624000000000000000000), (72399262481347019340149508837/5629499534213120000000000000000000), (20732943466784773705217778991/5629499534213120000000000000000000), (-383884037390660017948715551/1125899906842624000000000000000000), (-75047668692952657615358109/1407374883553280000000000000000000), (26339528104340885114136223/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial156.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial156.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial156.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 2114448462291880524906474241364559), (Int.ofNat 239806563427404451496023989833593), (Int.negOfNat 4263084679232066443286127931947), (Int.negOfNat 1947330187478761954082428272231), (Int.ofNat 531413275898641872700006073546), (Int.ofNat 91921292972077400015883496138), (Int.negOfNat 17181394737370688531668268267), (Int.negOfNat 1828314972109177565792839895), (Int.ofNat 289660583751884404104756894), (Int.ofNat 19743577521809181689939735), (Int.negOfNat 2912705517448070971993860), (Int.negOfNat 134493301891346195757828), (Int.ofNat 19321437563569991175034), (Int.ofNat 632564109715937182464), (Int.negOfNat 90390924386653943928), (Int.negOfNat 2087285069714540242), (Int.ofNat 264486026450439421), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-2114448462291880524906474241364559/5629499534213120000000000000000000), (239806563427404451496023989833593/5629499534213120000000000000000000), (-4263084679232066443286127931947/5629499534213120000000000000000000), (-1947330187478761954082428272231/5629499534213120000000000000000000), (265706637949320936350003036773/2814749767106560000000000000000000), (45960646486038700007941748069/2814749767106560000000000000000000), (-17181394737370688531668268267/5629499534213120000000000000000000), (-365662994421835513158567979/1125899906842624000000000000000000), (144830291875942202052378447/2814749767106560000000000000000000), (3948715504361836337987947/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial156.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial156.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial156.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 1657274768890354647285692319573125), (Int.ofNat 219953449235916745302075635176648), (Int.negOfNat 617525873243495897151111206245), (Int.ofNat 2785032665467880207930007465211), (Int.ofNat 269595806156823604811808415367), (Int.negOfNat 123657338330552975458819551739), (Int.negOfNat 7634317450979345820700120751), (Int.ofNat 2660619503620164701699004645), (Int.ofNat 104146386087259554568083840), (Int.negOfNat 32889314611864807060089333), (Int.negOfNat 818877632953882354448856), (Int.ofNat 260113903960887595836512), (Int.ofNat 4148404740500553676396), (Int.negOfNat 1421203170783484181608), (Int.negOfNat 14853201278687260350), (Int.ofNat 5766014406346374032), (Int.ofNat 83476995550931263), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-2651639630224567435657107711317/9007199254740992000000000000000), (27494181154489593162759454397081/703687441776640000000000000000000), (-123505174648699179430222241249/1125899906842624000000000000000000), (2785032665467880207930007465211/5629499534213120000000000000000000), (269595806156823604811808415367/5629499534213120000000000000000000), (-123657338330552975458819551739/5629499534213120000000000000000000), (-7634317450979345820700120751/5629499534213120000000000000000000), (532123900724032940339800929/1125899906842624000000000000000000), (162728728261343054012631/8796093022208000000000000000000), (-32889314611864807060089333/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial156.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial156.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial156.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1197339729904506985094024958065077), (Int.ofNat 249394017269229005666819092501254), (Int.ofNat 12659103095086187148032917919661), (Int.ofNat 272239228701588153862348927174), (Int.negOfNat 696040985459756163473453478098), (Int.negOfNat 10381921254678427678944268378), (Int.ofNat 20207673979855072302582451409), (Int.ofNat 130096893555945846603702023), (Int.negOfNat 315786569044218708621979126), (Int.negOfNat 162323886149346491594067), (Int.ofNat 3036898316645916695894072), (Int.negOfNat 10148360559775051076210), (Int.negOfNat 19611653256468775176146), (Int.ofNat 111890808322081462560), (Int.ofNat 90556118905062343532), (Int.negOfNat 769225047414041248), (Int.negOfNat 302703906438478867), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-1197339729904506985094024958065077/5629499534213120000000000000000000), (124697008634614502833409546250627/2814749767106560000000000000000000), (12659103095086187148032917919661/5629499534213120000000000000000000), (136119614350794076931174463587/2814749767106560000000000000000000), (-348020492729878081736726739049/2814749767106560000000000000000000), (-5190960627339213839472134189/2814749767106560000000000000000000), (20207673979855072302582451409/5629499534213120000000000000000000), (130096893555945846603702023/5629499534213120000000000000000000), (-157893284522109354310989563/2814749767106560000000000000000000), (-162323886149346491594067/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial156.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial156.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial156.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 655974216308038093742731195296009), (Int.ofNat 283822821189537755688436680365445), (Int.ofNat 1161054798735875405663517236632), (Int.negOfNat 2927938872066961615265566072044), (Int.ofNat 132723707547212171396162903366), (Int.ofNat 123565013913192513192046956365), (Int.negOfNat 4463876133206396617001226081), (Int.negOfNat 2531797889498959145125758815), (Int.ofNat 79724410466398619401555866), (Int.ofNat 30276541845915677402233915), (Int.negOfNat 865248408448620456253644), (Int.negOfNat 234977019915478420377088), (Int.ofNat 6189463401143971595238), (Int.ofNat 1271101147258753808282), (Int.negOfNat 31056486953381847970), (Int.negOfNat 5138595850594398814), (Int.ofNat 91861593078660979), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-655974216308038093742731195296009/5629499534213120000000000000000000), (56764564237907551137687336073089/1125899906842624000000000000000000), (145131849841984425707939654579/703687441776640000000000000000000), (-731984718016740403816391518011/1407374883553280000000000000000000), (66361853773606085698081451683/2814749767106560000000000000000000), (24713002782638502638409391273/1125899906842624000000000000000000), (-4463876133206396617001226081/5629499534213120000000000000000000), (-506359577899791829025151763/1125899906842624000000000000000000), (39862205233199309700777933/2814749767106560000000000000000000), (6055308369183135480446783/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial156.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial156.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial156.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 101605385254785352299683874993402), (Int.ofNat 265617357173033522321954806771075), (Int.negOfNat 5842305211775717404197622116558), (Int.ofNat 1227879131629718530278688370869), (Int.ofNat 582654741151085911235233341233), (Int.negOfNat 58843317253313045691759915284), (Int.negOfNat 16405481035750697078790538059), (Int.ofNat 1307767175823756972783090075), (Int.ofNat 250586371394307188158683744), (Int.negOfNat 16640873220120202670437225), (Int.negOfNat 2382728265634496999764566), (Int.ofNat 135756405034920707995032), (Int.ofNat 15347256665285529709362), (Int.negOfNat 764469570561536264698), (Int.negOfNat 71001733833729813750), (Int.ofNat 3193848235483622266), (Int.ofNat 219782962897007991), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-50802692627392676149841937496701/2814749767106560000000000000000000), (10624694286921340892878192270843/225179981368524800000000000000000), (-2921152605887858702098811058279/2814749767106560000000000000000000), (1227879131629718530278688370869/5629499534213120000000000000000000), (582654741151085911235233341233/5629499534213120000000000000000000), (-14710829313328261422939978821/1407374883553280000000000000000000), (-16405481035750697078790538059/5629499534213120000000000000000000), (52310687032950278911323603/225179981368524800000000000000000), (7830824106072099629958867/175921860444160000000000000000000), (-665634928804808106817489/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial156.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial156.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial156.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 422693598070605013497848984819340), (Int.ofNat 268564118267040306885678063246636), (Int.ofNat 8092357406349703991927739741723), (Int.ofNat 1973040952696325906270918078289), (Int.negOfNat 435058594148995296663582369082), (Int.negOfNat 81099367202457429167577890629), (Int.ofNat 13482234504172826489874686771), (Int.ofNat 1630461383649240037771126023), (Int.negOfNat 218962663128728096046703984), (Int.negOfNat 19418865838614326947558387), (Int.ofNat 2166876437071031751576768), (Int.ofNat 151872867295236183727060), (Int.negOfNat 14321063074413699982494), (Int.negOfNat 833215296299646868220), (Int.ofNat 67134546682060598688), (Int.ofNat 3491109533288955092), (Int.negOfNat 225739709937517783), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(21134679903530250674892449240967/281474976710656000000000000000000), (67141029566760076721419515811659/1407374883553280000000000000000000), (8092357406349703991927739741723/5629499534213120000000000000000000), (1973040952696325906270918078289/5629499534213120000000000000000000), (-217529297074497648331791184541/2814749767106560000000000000000000), (-81099367202457429167577890629/5629499534213120000000000000000000), (13482234504172826489874686771/5629499534213120000000000000000000), (1630461383649240037771126023/5629499534213120000000000000000000), (-13685166445545506002918999/351843720888320000000000000000000), (-19418865838614326947558387/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial156.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial156.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial156.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 999427505383091148713927203744346), (Int.ofNat 307262708994164167416310979895296), (Int.ofNat 6878956179169653623816980704835), (Int.negOfNat 2140067171776951163972154340205), (Int.negOfNat 270629583895857118351163552055), (Int.ofNat 100717329294644874653159077586), (Int.ofNat 7289634868890935602658409891), (Int.negOfNat 2208094430889990862042262925), (Int.negOfNat 110909704582680857253974010), (Int.ofNat 27588123831383439210648517), (Int.ofNat 1083096065471044933566016), (Int.negOfNat 220578852610314301965818), (Int.negOfNat 7286094085513269213696), (Int.ofNat 1216916407402471307892), (Int.ofNat 35427025683161489270), (Int.negOfNat 4904146701904050348), (Int.negOfNat 69922960926108713), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(499713752691545574356963601872173/2814749767106560000000000000000000), (37507654906514180592811398913/687194767360000000000000000000), (1375791235833930724763396140967/1125899906842624000000000000000000), (-428013434355390232794430868041/1125899906842624000000000000000000), (-54125916779171423670232710411/1125899906842624000000000000000000), (50358664647322437326579538793/2814749767106560000000000000000000), (7289634868890935602658409891/5629499534213120000000000000000000), (-88323777235599634481690517/225179981368524800000000000000000), (-11090970458268085725397401/562949953421312000000000000000000), (27588123831383439210648517/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial156.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial156.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial156.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 1623411362575127552848995123548206), (Int.ofNat 308858291811036083677284897719352), (Int.negOfNat 4199145138267121580011135102449), (Int.negOfNat 390166691255511094649431306253), (Int.ofNat 547455594566161512644198800967), (Int.ofNat 10537988182235998728606574444), (Int.negOfNat 17277713824144785373312981281), (Int.negOfNat 178791358341124646917359915), (Int.ofNat 284431501024528929275948966), (Int.ofNat 2432156386735868705103285), (Int.negOfNat 2838469654301091363482460), (Int.negOfNat 24955065726638406969288), (Int.ofNat 18823357338489112310966), (Int.ofNat 177770014163116400804), (Int.negOfNat 88410977944383911652), (Int.negOfNat 927643140409344582), (Int.ofNat 263957589925557229), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(811705681287563776424497561774103/2814749767106560000000000000000000), (38607286476379510459660612214919/703687441776640000000000000000000), (-4199145138267121580011135102449/5629499534213120000000000000000000), (-390166691255511094649431306253/5629499534213120000000000000000000), (547455594566161512644198800967/5629499534213120000000000000000000), (2634497045558999682151643611/1407374883553280000000000000000000), (-17277713824144785373312981281/5629499534213120000000000000000000), (-35758271668224929383471983/1125899906842624000000000000000000), (142215750512264464637974483/2814749767106560000000000000000000), (486431277347173741020657/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial156.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial156.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial156.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 2229249057401898882843183766011102), (Int.ofNat 302626418850870482118496244043057), (Int.ofNat 3663803184439638251306585735203), (Int.ofNat 2026670090208969301358312345084), (Int.negOfNat 142362557654520144273810630784), (Int.negOfNat 101235404371822952681299025546), (Int.ofNat 4888346308389366328062277649), (Int.ofNat 2323799221147411376191321805), (Int.negOfNat 75937823746870909077110184), (Int.negOfNat 30156778795403049337185937), (Int.ofNat 645088668286636712823880), (Int.ofNat 247835079114651457419240), (Int.negOfNat 3322901097949350701248), (Int.negOfNat 1390767317741971567992), (Int.ofNat 10967638627541234116), (Int.ofNat 5651453164114630662), (Int.negOfNat 92676334374137047), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(1114624528700949441421591883005551/2814749767106560000000000000000000), (302626418850870482118496244043057/5629499534213120000000000000000000), (3663803184439638251306585735203/5629499534213120000000000000000000), (506667522552242325339578086271/1407374883553280000000000000000000), (-1112207481675938627139145553/43980465111040000000000000000000), (-50617702185911476340649512773/2814749767106560000000000000000000), (4888346308389366328062277649/5629499534213120000000000000000000), (464759844229482275238264361/1125899906842624000000000000000000), (-9492227968358863634638773/703687441776640000000000000000000), (-30156778795403049337185937/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial156.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial156.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial156.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 2860429698303418348591501109038090), (Int.ofNat 330785562821774487682882921433819), (Int.ofNat 6782015677142656681623721220650), (Int.negOfNat 1356773121008928891195630956340), (Int.negOfNat 399159734492992441857304978530), (Int.ofNat 69570492506301696266201068264), (Int.ofNat 14002899212536959989368974585), (Int.negOfNat 1529254040245423540731498057), (Int.negOfNat 252630634977444111393145318), (Int.ofNat 17881270789022753679492521), (Int.ofNat 2702904924724753720344736), (Int.negOfNat 126782329558266738583034), (Int.negOfNat 18771972928678176195520), (Int.ofNat 597995295744501452434), (Int.ofNat 90737876944517578776), (Int.negOfNat 1999008649257359408), (Int.negOfNat 302175469913596675), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(286042969830341834859150110903809/562949953421312000000000000000000), (330785562821774487682882921433819/5629499534213120000000000000000000), (135640313542853133632474424413/112589990684262400000000000000000), (-67838656050446444559781547817/281474976710656000000000000000000), (-39915973449299244185730497853/562949953421312000000000000000000), (8696311563287712033275133533/703687441776640000000000000000000), (2800579842507391997873794917/1125899906842624000000000000000000), (-1529254040245423540731498057/5629499534213120000000000000000000), (-126315317488722055696572659/2814749767106560000000000000000000), (17881270789022753679492521/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial156.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial156.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial156.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 3534761762029348570949939286714947), (Int.ofNat 336222822537006724215787884354230), (Int.negOfNat 3383671793012571083946720534452), (Int.negOfNat 705449618642870395908883863865), (Int.ofNat 526575945208551589496159378977), (Int.ofNat 48443652052846501014260855076), (Int.negOfNat 17394313020557477998786107937), (Int.negOfNat 1446363501412204080705002191), (Int.ofNat 279160806852853754549110160), (Int.ofNat 22592419770256652378073439), (Int.negOfNat 2559034290891951382073526), (Int.negOfNat 208526218595230692955072), (Int.ofNat 14992669954214506258284), (Int.ofNat 1248555821013369579084), (Int.negOfNat 61231595794781706294), (Int.negOfNat 5289285737664879612), (Int.ofNat 255275629674382807), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(3534761762029348570949939286714947/5629499534213120000000000000000000), (33622282253700672421578788435423/562949953421312000000000000000000), (-845917948253142770986680133613/1407374883553280000000000000000000), (-141089923728574079181776772773/1125899906842624000000000000000000), (526575945208551589496159378977/5629499534213120000000000000000000), (12110913013211625253565213769/1407374883553280000000000000000000), (-17394313020557477998786107937/5629499534213120000000000000000000), (-1446363501412204080705002191/5629499534213120000000000000000000), (3489510085660671931863877/70368744177664000000000000000000), (22592419770256652378073439/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial156.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial156.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial156.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 4196786219853398564063462888891995), (Int.ofNat 331283872620713971195231234422754), (Int.ofNat 4320549528279643201347769703704), (Int.ofNat 2427448357454453587451373696807), (Int.negOfNat 74795910929733128319110634902), (Int.negOfNat 136119784344553818376750402462), (Int.negOfNat 1774365957174401453090598759), (Int.ofNat 3198705069498680704607453639), (Int.ofNat 104785296676452336780055118), (Int.negOfNat 39043843834553855040231969), (Int.negOfNat 1688827594031520727842412), (Int.ofNat 284212396406133648679608), (Int.ofNat 13967179085314851298028), (Int.negOfNat 1389615740152085479620), (Int.negOfNat 73494585067054601166), (Int.ofNat 5041383331326347868), (Int.ofNat 286193584801554201), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(839357243970679712812692577778399/1125899906842624000000000000000000), (165641936310356985597615617211377/2814749767106560000000000000000000), (540068691034955400168471212963/703687441776640000000000000000000), (2427448357454453587451373696807/5629499534213120000000000000000000), (-37397955464866564159555317451/2814749767106560000000000000000000), (-68059892172276909188375201231/2814749767106560000000000000000000), (-1774365957174401453090598759/5629499534213120000000000000000000), (3198705069498680704607453639/5629499534213120000000000000000000), (52392648338226168390027559/2814749767106560000000000000000000), (-39043843834553855040231969/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial156.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial156.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial156.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 4890804789316006820035449678633225), (Int.ofNat 365516900608647074259551062008079), (Int.ofNat 7921345704175211970365450316824), (Int.negOfNat 2143271876808677661317216972914), (Int.negOfNat 696374718714248518504550814641), (Int.ofNat 75195498182773199893845746570), (Int.ofNat 27512185707930911435384157397), (Int.negOfNat 689094021897962459000935503), (Int.negOfNat 482762111999242113730380248), (Int.negOfNat 4422937434951940176673659), (Int.ofNat 4471667530087160540797240), (Int.ofNat 105268152655667707840592), (Int.negOfNat 26282206140990113108100), (Int.negOfNat 807395601219724807664), (Int.ofNat 108434748983038143654), (Int.ofNat 3827236672165165484), (Int.negOfNat 389153746533239611), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(195632191572640272801417987145329/225179981368524800000000000000000), (365516900608647074259551062008079/5629499534213120000000000000000000), (990168213021901496295681289603/703687441776640000000000000000000), (-1071635938404338830658608486457/2814749767106560000000000000000000), (-696374718714248518504550814641/5629499534213120000000000000000000), (7519549818277319989384574657/562949953421312000000000000000000), (27512185707930911435384157397/5629499534213120000000000000000000), (-689094021897962459000935503/5629499534213120000000000000000000), (-60345263999905264216297531/703687441776640000000000000000000), (-4422937434951940176673659/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial156.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial156.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial156.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 5629193465170835792831505516202907), (Int.ofNat 359707161399133593088875414124237), (Int.negOfNat 10328660437519162386928164418835), (Int.negOfNat 1509259266221333830710613430120), (Int.ofNat 1015877115715173190816232422457), (Int.ofNat 158625184114002539603350166924), (Int.negOfNat 24236963163343582514511099631), (Int.negOfNat 4904534346081202199737130015), (Int.ofNat 162849703846737555519528424), (Int.ofNat 60301301184141358895933469), (Int.negOfNat 87989088890859386244094), (Int.negOfNat 431683863262189268839268), (Int.negOfNat 5155217765830671212284), (Int.ofNat 2094001264849445958260), (Int.ofNat 39279017559352982966), (Int.negOfNat 7637189525463897000), (Int.negOfNat 203272641260083325), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(5629193465170835792831505516202907/5629499534213120000000000000000000), (359707161399133593088875414124237/5629499534213120000000000000000000), (-2065732087503832477385632883767/1125899906842624000000000000000000), (-37731481655533345767765335753/140737488355328000000000000000000), (1015877115715173190816232422457/5629499534213120000000000000000000), (39656296028500634900837541731/1407374883553280000000000000000000), (-24236963163343582514511099631/5629499534213120000000000000000000), (-980906869216240439947426003/1125899906842624000000000000000000), (20356212980842194439941053/703687441776640000000000000000000), (60301301184141358895933469/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial156.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial156.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial156.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 6314441751817420007704374332919242), (Int.ofNat 338929129247688743872022148197618), (Int.ofNat 9130650401416970604028787043109), (Int.ofNat 6934779495927700690098782815524), (Int.ofNat 180882744728234343439690596188), (Int.negOfNat 362965348969691782250539629782), (Int.negOfNat 40651312608504136221190972111), (Int.ofNat 4124323287731300846641915141), (Int.ofNat 709106967730698220089238068), (Int.negOfNat 21540718770318909441991063), (Int.negOfNat 6276431992286506891680926), (Int.ofNat 43020499230709440857184), (Int.ofNat 35883076272564024585928), (Int.ofNat 145473002008937221270), (Int.negOfNat 146965578569145389944), (Int.negOfNat 1510961732194924604), (Int.ofNat 481571391621360977), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(3157220875908710003852187166459621/2814749767106560000000000000000000), (169464564623844371936011074098809/2814749767106560000000000000000000), (9130650401416970604028787043109/5629499534213120000000000000000000), (1733694873981925172524695703881/1407374883553280000000000000000000), (45220686182058585859922649047/1407374883553280000000000000000000), (-181482674484845891125269814891/2814749767106560000000000000000000), (-40651312608504136221190972111/5629499534213120000000000000000000), (4124323287731300846641915141/5629499534213120000000000000000000), (177276741932674555022309517/1407374883553280000000000000000000), (-21540718770318909441991063/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial156.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial156.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial156.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 7073670619332458798289599831159534), (Int.ofNat 430108467176277618514370487958636), (Int.ofNat 20161275933343996626071916896740), (Int.negOfNat 9267058937804519928661718236807), (Int.negOfNat 4103779986178731914547659369897), (Int.negOfNat 275890268777005783408106289932), (Int.ofNat 63622292595352825234621454405), (Int.ofNat 7431228296141549859116665111), (Int.negOfNat 489274395689927490104340858), (Int.negOfNat 81972879304750591177723321), (Int.ofNat 2222702317612128053858458), (Int.ofNat 554497145807866195771530), (Int.negOfNat 5919937464941053398540), (Int.negOfNat 2614747221600583140032), (Int.ofNat 5858530416047831036), (Int.ofNat 9273286284848296250), (Int.ofNat 40673345959837565), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(3536835309666229399144799915579767/2814749767106560000000000000000000), (107527116794069404628592621989659/1407374883553280000000000000000000), (1008063796667199831303595844837/281474976710656000000000000000000), (-9267058937804519928661718236807/5629499534213120000000000000000000), (-4103779986178731914547659369897/5629499534213120000000000000000000), (-68972567194251445852026572483/1407374883553280000000000000000000), (12724458519070565046924290881/1125899906842624000000000000000000), (7431228296141549859116665111/5629499534213120000000000000000000), (-244637197844963745052170429/2814749767106560000000000000000000), (-81972879304750591177723321/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial156.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial156.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial156.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 7870766383509144892001600527060324), (Int.ofNat 261028814839549279019664012838047), (Int.negOfNat 136953981582059005642340945499958), (Int.negOfNat 40053169481963084224799966989763), (Int.negOfNat 1791484168055983934071877390894), (Int.ofNat 760239536022979047759071663502), (Int.ofNat 72544084605820806540843315233), (Int.negOfNat 7559602632198607497030464129), (Int.negOfNat 978890868803598076909668580), (Int.ofNat 47331486704683299820759807), (Int.ofNat 7802221908630926100153182), (Int.negOfNat 201995748957061918529722), (Int.negOfNat 42452225359578444164262), (Int.ofNat 612839036546230159992), (Int.ofNat 169458073483784154448), (Int.negOfNat 1199162048546891086), (Int.negOfNat 519789271609400423), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(1967691595877286223000400131765081/1407374883553280000000000000000000), (261028814839549279019664012838047/5629499534213120000000000000000000), (-68476990791029502821170472749979/2814749767106560000000000000000000), (-40053169481963084224799966989763/5629499534213120000000000000000000), (-895742084027991967035938695447/2814749767106560000000000000000000), (380119768011489523879535831751/2814749767106560000000000000000000), (72544084605820806540843315233/5629499534213120000000000000000000), (-7559602632198607497030464129/5629499534213120000000000000000000), (-48944543440179903845483429/281474976710656000000000000000000), (47331486704683299820759807/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial156.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial156.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial156.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 7523702889027944934924249434620092), (Int.negOfNat 754248365748205690777971577255629), (Int.negOfNat 348573514033355951272605891855198), (Int.negOfNat 17994674726986488441354265764315), (Int.ofNat 7232690813162375840929505094668), (Int.ofNat 705646904010245724108770610168), (Int.negOfNat 90143364523044150043780930763), (Int.negOfNat 10921836788003863578099152351), (Int.ofNat 729685901202299877417402204), (Int.ofNat 100939491550629058490684681), (Int.negOfNat 4109437651485744210955932), (Int.negOfNat 631547875404780839689362), (Int.ofNat 16979787142847467084416), (Int.ofNat 2865322672108455470472), (Int.negOfNat 53466306573583315830), (Int.negOfNat 9850866328889750064), (Int.ofNat 121925949340408195), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(1880925722256986233731062358655023/1407374883553280000000000000000000), (-754248365748205690777971577255629/5629499534213120000000000000000000), (-174286757016677975636302945927599/2814749767106560000000000000000000), (-3598934945397297688270853152863/1125899906842624000000000000000000), (1808172703290593960232376273667/1407374883553280000000000000000000), (88205863001280715513596326271/703687441776640000000000000000000), (-90143364523044150043780930763/5629499534213120000000000000000000), (-10921836788003863578099152351/5629499534213120000000000000000000), (182421475300574969354350551/1407374883553280000000000000000000), (100939491550629058490684681/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial156.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial156.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial156.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 4608324358055868870259445341695215), (Int.negOfNat 2097828998835231781137360748348046), (Int.negOfNat 253769933891509008841337595318666), (Int.ofNat 49316705755787964419699875481528), (Int.ofNat 6967892244085706464817415177801), (Int.negOfNat 812344497046797954907954479325), (Int.negOfNat 115068628667545792170773883925), (Int.ofNat 8715326447746980729903957601), (Int.ofNat 1208073344427764605559569212), (Int.negOfNat 63768750331704994313681975), (Int.negOfNat 8642178496098737061427444), (Int.ofNat 335990040962894088870160), (Int.ofNat 44546260471043702995874), (Int.negOfNat 1331896275681355091816), (Int.negOfNat 172966374168794688952), (Int.ofNat 4055672165675472576), (Int.ofNat 558007151597439869), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(921664871611173774051889068339043/1125899906842624000000000000000000), (-1048914499417615890568680374174023/2814749767106560000000000000000000), (-126884966945754504420668797659333/2814749767106560000000000000000000), (6164588219473495552462484435191/703687441776640000000000000000000), (6967892244085706464817415177801/5629499534213120000000000000000000), (-32493779881871918196318179173/225179981368524800000000000000000), (-4602745146701831686830955357/225179981368524800000000000000000), (8715326447746980729903957601/5629499534213120000000000000000000), (302018336106941151389892303/1407374883553280000000000000000000), (-2550750013268199772547279/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial156.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial156.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial156.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 128368682999945241509185653897029), (Int.negOfNat 2380261297875779896613701410860590), (Int.ofNat 124396045849871730397545885325567), (Int.ofNat 60743669846977021374979150791096), (Int.negOfNat 4620415735701986377696633505492), (Int.negOfNat 1104260507518492229436778595956), (Int.ofNat 77550532585547050496131587663), (Int.ofNat 13255712584750936470297385571), (Int.negOfNat 782166719837334854490059610), (Int.negOfNat 108606875698557891428559963), (Int.ofNat 5320396166767807642347232), (Int.ofNat 636659729760160523748538), (Int.negOfNat 26112092745711920005050), (Int.negOfNat 2780607092115062317346), (Int.ofNat 97181510031967713750), (Int.ofNat 9223447773137774846), (Int.negOfNat 297264537970000437), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-128368682999945241509185653897029/5629499534213120000000000000000000), (-238026129787577989661370141086059/562949953421312000000000000000000), (124396045849871730397545885325567/5629499534213120000000000000000000), (7592958730872127671872393848887/703687441776640000000000000000000), (-1155103933925496594424158376373/1407374883553280000000000000000000), (-276065126879623057359194648989/1407374883553280000000000000000000), (77550532585547050496131587663/5629499534213120000000000000000000), (13255712584750936470297385571/5629499534213120000000000000000000), (-78216671983733485449005961/562949953421312000000000000000000), (-108606875698557891428559963/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial156.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial156.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial156.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial156.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial156.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial156.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial156.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial156.reflect := by
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

end Bin156
end
end ErdosOverlap.OuterNumerics
