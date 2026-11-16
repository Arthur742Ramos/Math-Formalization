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

/-! # Exact integer weighted outer models for source bin 160

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin160

def weightDenominator : ℤ := (Int.ofNat 5000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 182511692375309600)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 888237410529214700)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 652478248321862350)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 228072138175701350)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 432369599529223100)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 351017084513210500)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 252920599653790670)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 190443188828660100)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 110160899886408790)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 63448258896559560)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial160.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial160.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 4626794890703622000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1809673633160619750)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 592767102222138700)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 504391332772787300)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 266699532994921775)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 100586606156819200)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 9777351432406142)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 12745564932205505)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 7915251449161678)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial160.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial160.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4626794890703622000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1809673633160619750)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 592767102222138700)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 504391332772787300)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 266699532994921775)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 100586606156819200)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 9777351432406142)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 12745564932205505)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 7915251449161678)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial160.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial160.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial160.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 1962820034756259424424493529617842), (Int.ofNat 2051031013674679707864162746419456), (Int.ofNat 195566446389484675703430899901103), (Int.negOfNat 51607535534067229754584560258173), (Int.negOfNat 6138222241857037527687060930771), (Int.ofNat 932671611312595099953721531615), (Int.ofNat 105330152346577155469770330630), (Int.negOfNat 11133102568369240118559451669), (Int.negOfNat 1111842078693372766241936186), (Int.ofNat 91224064678132946817878819), (Int.ofNat 7901934608257993026263808), (Int.negOfNat 536829619674310591731232), (Int.negOfNat 40334382687785058361867), (Int.ofNat 2357362338543913652521), (Int.ofNat 155146236348718365484), (Int.negOfNat 7884908991852836654), (Int.negOfNat 487639267996382163), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-981410017378129712212246764808921/2814749767106560000000000000000000), (8011839897166717608844385728201/21990232555520000000000000000000), (195566446389484675703430899901103/5629499534213120000000000000000000), (-51607535534067229754584560258173/5629499534213120000000000000000000), (-6138222241857037527687060930771/5629499534213120000000000000000000), (186534322262519019990744306323/1125899906842624000000000000000000), (10533015234657715546977033063/562949953421312000000000000000000), (-11133102568369240118559451669/5629499534213120000000000000000000), (-555921039346686383120968093/2814749767106560000000000000000000), (91224064678132946817878819/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial160.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial160.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial160.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial160 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 2445366445845349332208685948642352), (Int.ofNat 2106537964155527195432957882095626), (Int.negOfNat 170483026738356979367578219156554), (Int.negOfNat 54195218593582988924990191150211), (Int.ofNat 5592998242371991443640469994500), (Int.ofNat 991922000596798828698323367156), (Int.negOfNat 96914959191005177804642331291), (Int.negOfNat 11745563237465296365843315111), (Int.ofNat 1043546020567549333533826266), (Int.ofNat 93986062250848941076833673), (Int.negOfNat 7622964412115892281704477), (Int.negOfNat 536887291174858567902754), (Int.ofNat 40003306843150130380974), (Int.ofNat 2288846391903692772568), (Int.negOfNat 157661345145297995537), (Int.negOfNat 7467210885084894840), (Int.ofNat 509892141433473493), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(152835402865334333263042871790147/351843720888320000000000000000000), (1053268982077763597716478941047813/2814749767106560000000000000000000), (-85241513369178489683789109578277/2814749767106560000000000000000000), (-54195218593582988924990191150211/5629499534213120000000000000000000), (11185996484743982887280939989/11258999068426240000000000000000), (247980500149199707174580841789/1407374883553280000000000000000000), (-96914959191005177804642331291/5629499534213120000000000000000000), (-11745563237465296365843315111/5629499534213120000000000000000000), (521773010283774666766913133/2814749767106560000000000000000000), (93986062250848941076833673/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial160.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial160.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial160.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial160 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 5656778547864496138277352568725861), (Int.ofNat 1009964396687539195708639434317632), (Int.negOfNat 311018037107210366351025861749082), (Int.ofNat 10382322477458731812129500817129), (Int.ofNat 7836884199035658098032696864037), (Int.negOfNat 573416883409210037258593208891), (Int.negOfNat 112135153305476444898778896023), (Int.ofNat 9519132056643770603292333513), (Int.ofNat 1030871085557672072478070347), (Int.negOfNat 91702902642168157266760138), (Int.negOfNat 6601554190611816525672928), (Int.ofNat 591679912725215912753740), (Int.ofNat 31087344399372991488628), (Int.negOfNat 2749438285399539379513), (Int.negOfNat 111869822413366433580), (Int.ofNat 9654551193532008884), (Int.ofNat 305209742755865161), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(5656778547864496138277352568725861/5629499534213120000000000000000000), (15780693698242799932947491161213/87960930222080000000000000000000), (-155509018553605183175512930874541/2814749767106560000000000000000000), (10382322477458731812129500817129/5629499534213120000000000000000000), (7836884199035658098032696864037/5629499534213120000000000000000000), (-573416883409210037258593208891/5629499534213120000000000000000000), (-112135153305476444898778896023/5629499534213120000000000000000000), (9519132056643770603292333513/5629499534213120000000000000000000), (1030871085557672072478070347/5629499534213120000000000000000000), (-45851451321084078633380069/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial160.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial160.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial160.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial160 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 6616987884823393831673782190784310), (Int.ofNat 78939483880328319056098690386215), (Int.negOfNat 125660817587371281203454521190912), (Int.ofNat 38810361014008017056519092480777), (Int.negOfNat 1236092941398780233772571289087), (Int.negOfNat 876052045256048648274092702849), (Int.ofNat 62706997130347179748226268947), (Int.ofNat 10048313015142877524144200667), (Int.negOfNat 906958777512271998046598860), (Int.negOfNat 74102690911741878584109454), (Int.ofNat 7556682114834365807601598), (Int.ofNat 386255030021091447836582), (Int.negOfNat 42480492887483303491300), (Int.negOfNat 1506100457658089274239), (Int.ofNat 173909773351915316232), (Int.ofNat 4423304063426748152), (Int.negOfNat 533637895780958527), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(661698788482339383167378219078431/562949953421312000000000000000000), (15787896776065663811219738077243/1125899906842624000000000000000000), (-245431284350334533600497111701/10995116277760000000000000000000), (38810361014008017056519092480777/5629499534213120000000000000000000), (-1236092941398780233772571289087/5629499534213120000000000000000000), (-876052045256048648274092702849/5629499534213120000000000000000000), (62706997130347179748226268947/5629499534213120000000000000000000), (10048313015142877524144200667/5629499534213120000000000000000000), (-45347938875613599902329943/281474976710656000000000000000000), (-37051345455870939292054727/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial160.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial160.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial160.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial160 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 6539932973413357393043861628585762), (Int.negOfNat 52134725169578149017898529981067), (Int.ofNat 27381250646496838678881866780128), (Int.ofNat 7643359962339370708817848978756), (Int.negOfNat 4623112087600495588042757073900), (Int.ofNat 232524200296830634327471003261), (Int.ofNat 80405749598245629318116571890), (Int.negOfNat 7001355106925438261969528600), (Int.negOfNat 733885850949206171016582965), (Int.ofNat 81789571468599235063216565), (Int.ofNat 4327807970972149319367821), (Int.negOfNat 576036440990328273780979), (Int.negOfNat 18087509628716889956746), (Int.ofNat 2802028866839016724409), (Int.ofNat 56682668679691310975), (Int.negOfNat 10192942374542553840), (Int.negOfNat 114864966066186481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(3269966486706678696521930814292881/2814749767106560000000000000000000), (-52134725169578149017898529981067/5629499534213120000000000000000000), (855664082703026208715058336879/175921860444160000000000000000000), (1910839990584842677204462244689/1407374883553280000000000000000000), (-46231120876004955880427570739/56294995342131200000000000000000), (232524200296830634327471003261/5629499534213120000000000000000000), (8040574959824562931811657189/562949953421312000000000000000000), (-35006775534627191309847643/28147497671065600000000000000000), (-146777170189841234203316593/1125899906842624000000000000000000), (16357914293719847012643313/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial160.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial160.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial160.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial160 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 6543913383783564938222514441476210), (Int.ofNat 31526565648901003776563686202056), (Int.negOfNat 5424238835834111140592449416349), (Int.negOfNat 11930880631481972434833924578367), (Int.ofNat 106515963330724736663488229857), (Int.ofNat 462369591163110335897485095022), (Int.negOfNat 39257391050986046141043295546), (Int.negOfNat 5995256214547727982577946917), (Int.ofNat 731586868553080545710896037), (Int.ofNat 42210208411515716504076377), (Int.negOfNat 6772099539168421776248602), (Int.negOfNat 188483041516127552853677), (Int.ofNat 40113982767020572320022), (Int.ofNat 568145872334767089377), (Int.negOfNat 169085483717196359734), (Int.negOfNat 1094195694992248784), (Int.ofNat 557383650128443561), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(654391338378356493822251444147621/562949953421312000000000000000000), (3940820706112625472070460775257/703687441776640000000000000000000), (-5424238835834111140592449416349/5629499534213120000000000000000000), (-11930880631481972434833924578367/5629499534213120000000000000000000), (106515963330724736663488229857/5629499534213120000000000000000000), (231184795581555167948742547511/2814749767106560000000000000000000), (-19628695525493023070521647773/2814749767106560000000000000000000), (-5995256214547727982577946917/5629499534213120000000000000000000), (731586868553080545710896037/5629499534213120000000000000000000), (42210208411515716504076377/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial160.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial160.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial160.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial160 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 6503244474607362887027959348841940), (Int.negOfNat 102355575248256408061010730434872), (Int.negOfNat 49489233286208842592402258545575), (Int.negOfNat 791991365245084266846957126448), (Int.ofNat 1591805780713742089315561774838), (Int.negOfNat 155575399454600116870730658709), (Int.negOfNat 36060307715120446840054044009), (Int.ofNat 5298008002122182371628070514), (Int.ofNat 333001923137998294152367854), (Int.negOfNat 68028937144609049301811627), (Int.negOfNat 1581460401564014130528574), (Int.ofNat 505226779199157192435694), (Int.ofNat 3585453815511536436385), (Int.negOfNat 2531572455499585410215), (Int.ofNat 2548620170774832992), (Int.ofNat 9446537874723584240), (Int.negOfNat 75479810623492199), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(325162223730368144351397967442097/281474976710656000000000000000000), (-12794446906032051007626341304359/703687441776640000000000000000000), (-1979569331448353703696090341823/225179981368524800000000000000000), (-49499460327817766677934820403/351843720888320000000000000000000), (795902890356871044657780887419/2814749767106560000000000000000000), (-155575399454600116870730658709/5629499534213120000000000000000000), (-36060307715120446840054044009/5629499534213120000000000000000000), (2649004001061091185814035257/2814749767106560000000000000000000), (166500961568999147076183927/2814749767106560000000000000000000), (-68028937144609049301811627/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial160.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial160.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial160.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial160 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 6113151052334508242458417487269816), (Int.negOfNat 275692918324028598265674949997666), (Int.negOfNat 33298969691735343651545741191828), (Int.ofNat 3144420665474138004721311180090), (Int.negOfNat 545813811343995856192735572666), (Int.negOfNat 129482887017361775036812833122), (Int.ofNat 31528721862219991887208542782), (Int.ofNat 1807671115400309694151609231), (Int.negOfNat 577512541191006775046807091), (Int.negOfNat 8258959147109613128353887), (Int.ofNat 5531891995499908169671130), (Int.negOfNat 14805258336220634724558), (Int.negOfNat 33635454121543823886820), (Int.ofNat 361505807632525005982), (Int.ofNat 143526089886270753313), (Int.negOfNat 2202971337874786884), (Int.negOfNat 517681145579369035), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(764143881541813530307302185908727/703687441776640000000000000000000), (-137846459162014299132837474998833/2814749767106560000000000000000000), (-8324742422933835912886435297957/1407374883553280000000000000000000), (314442066547413800472131118009/562949953421312000000000000000000), (-272906905671997928096367786333/2814749767106560000000000000000000), (-64741443508680887518406416561/2814749767106560000000000000000000), (15764360931109995943604271391/2814749767106560000000000000000000), (1807671115400309694151609231/5629499534213120000000000000000000), (-577512541191006775046807091/5629499534213120000000000000000000), (-8258959147109613128353887/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial160.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial160.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial160.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial160 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 5442950878967398901187404794800518), (Int.negOfNat 392700107362415633541214800208092), (Int.negOfNat 30120773703879135901057089964139), (Int.negOfNat 1343053664865100932790524977396), (Int.negOfNat 53154017993534028214130982114), (Int.ofNat 166348240843274828296026014669), (Int.ofNat 3164951349883986213318417992), (Int.negOfNat 4144915344365828402658973581), (Int.ofNat 23038099693181947103664449), (Int.ofNat 51991322396803678373539287), (Int.negOfNat 952902820220402533352330), (Int.negOfNat 391154727108399527501572), (Int.ofNat 9638642259100378837100), (Int.ofNat 1983704224465882337738), (Int.negOfNat 55361206672097758187), (Int.negOfNat 7413601841395121756), (Int.ofNat 218206831314934675), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(2721475439483699450593702397400259/2814749767106560000000000000000000), (-98175026840603908385303700052023/1407374883553280000000000000000000), (-30120773703879135901057089964139/5629499534213120000000000000000000), (-335763416216275233197631244349/1407374883553280000000000000000000), (-26577008996767014107065491057/2814749767106560000000000000000000), (166348240843274828296026014669/5629499534213120000000000000000000), (395618918735498276664802249/703687441776640000000000000000000), (-4144915344365828402658973581/5629499534213120000000000000000000), (23038099693181947103664449/5629499534213120000000000000000000), (51991322396803678373539287/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial160.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial160.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial160.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial160 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 4530498622308211947178095051152891), (Int.negOfNat 518807738157792674166846959810385), (Int.negOfNat 27912917717601398151336277672988), (Int.ofNat 3362127275622488757684804911501), (Int.ofNat 847624138797849993688867404012), (Int.negOfNat 46405388542482784458655775186), (Int.negOfNat 25383175021443406084358693399), (Int.ofNat 1157865270068173480062170066), (Int.ofNat 413383596908864018023833064), (Int.negOfNat 18913838397114345028326043), (Int.negOfNat 3908295522399184125096094), (Int.ofNat 181826344397764835318506), (Int.ofNat 23866409812382490501845), (Int.negOfNat 1119313978750183975185), (Int.negOfNat 102329248527732028828), (Int.ofNat 4865403287169694680), (Int.ofNat 406615130684573271), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(4530498622308211947178095051152891/5629499534213120000000000000000000), (-103761547631558534833369391962077/1125899906842624000000000000000000), (-6978229429400349537834069418247/1407374883553280000000000000000000), (3362127275622488757684804911501/5629499534213120000000000000000000), (211906034699462498422216851003/1407374883553280000000000000000000), (-23202694271241392229327887593/2814749767106560000000000000000000), (-25383175021443406084358693399/5629499534213120000000000000000000), (578932635034086740031085033/2814749767106560000000000000000000), (51672949613608002252979133/703687441776640000000000000000000), (-18913838397114345028326043/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial160.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial160.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial160.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial160 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 3418821790355411328008031180553841), (Int.negOfNat 570694904859839998317690234652533), (Int.ofNat 4191643449333194112037690690417), (Int.ofNat 5463047330947023150284956759404), (Int.negOfNat 470810977655726557892510609668), (Int.negOfNat 130854575667426688004036557264), (Int.ofNat 15073332162223382433579878814), (Int.ofNat 2702893404352789659297608467), (Int.negOfNat 262506250354252868454673063), (Int.negOfNat 32537255950476156600171507), (Int.ofNat 2774437582674251421196358), (Int.ofNat 243064687182291694163947), (Int.negOfNat 19221261273981357687038), (Int.negOfNat 1229666166178852082457), (Int.ofNat 93065776274282377166), (Int.ofNat 4492642678121357704), (Int.negOfNat 305400844558979269), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(3418821790355411328008031180553841/5629499534213120000000000000000000), (-570694904859839998317690234652533/5629499534213120000000000000000000), (4191643449333194112037690690417/5629499534213120000000000000000000), (1365761832736755787571239189851/1407374883553280000000000000000000), (-117702744413931639473127652417/1407374883553280000000000000000000), (-8178410979214168000252284829/351843720888320000000000000000000), (7536666081111691216789939407/2814749767106560000000000000000000), (2702893404352789659297608467/5629499534213120000000000000000000), (-262506250354252868454673063/5629499534213120000000000000000000), (-32537255950476156600171507/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial160.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial160.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial160.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial160 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 2327412665619145541156380817902895), (Int.negOfNat 510128459930717877129747654558114), (Int.ofNat 20053047665747663435833798858616), (Int.negOfNat 207168350797755947828789715526), (Int.negOfNat 498569124355594790663051966457), (Int.ofNat 121182672540829265059704484846), (Int.ofNat 13236907233544043741839476420), (Int.negOfNat 2811819559571505778602290850), (Int.negOfNat 210445493648749365609273805), (Int.ofNat 35386156510161526480962285), (Int.ofNat 1965525768145214494225121), (Int.negOfNat 284970473426414242729851), (Int.negOfNat 11882804453236347240686), (Int.ofNat 1581332866613335446631), (Int.ofNat 50277638618146658555), (Int.negOfNat 6403332931904832080), (Int.negOfNat 216270353994894591), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(465482533123829108231276163580579/1125899906842624000000000000000000), (-255064229965358938564873827279057/2814749767106560000000000000000000), (2506630958218457929479224857327/703687441776640000000000000000000), (-103584175398877973914394857763/2814749767106560000000000000000000), (-498569124355594790663051966457/5629499534213120000000000000000000), (60591336270414632529852242423/2814749767106560000000000000000000), (661845361677202187091973821/281474976710656000000000000000000), (-56236391191430115572045817/112589990684262400000000000000000), (-42089098729749873121854761/1125899906842624000000000000000000), (7077231302032305296192457/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial160.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial160.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial160.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial160 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 1382064215944930112569285243282314), (Int.negOfNat 437507413181383993326735397326675), (Int.ofNat 17626329187905835343305352243225), (Int.ofNat 1025292615698216937447312099463), (Int.ofNat 640626303264791939902004525381), (Int.ofNat 27663162756817565236146727989), (Int.negOfNat 23861547662294831489502887035), (Int.negOfNat 817466721831265150410348967), (Int.ofNat 379310617836558119420806950), (Int.ofNat 10257344506944683328839584), (Int.negOfNat 3659972893403437929065452), (Int.negOfNat 75555278832655391729982), (Int.ofNat 23732767688070584550420), (Int.ofNat 367419467146734537319), (Int.negOfNat 109869247776854200508), (Int.negOfNat 1223132121313662832), (Int.ofNat 329146598906464303), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(691032107972465056284642621641157/2814749767106560000000000000000000), (-17500296527255359733069415893067/225179981368524800000000000000000), (705053167516233413732214089729/225179981368524800000000000000000), (1025292615698216937447312099463/5629499534213120000000000000000000), (640626303264791939902004525381/5629499534213120000000000000000000), (27663162756817565236146727989/5629499534213120000000000000000000), (-4772309532458966297900577407/1125899906842624000000000000000000), (-817466721831265150410348967/5629499534213120000000000000000000), (7586212356731162388416139/112589990684262400000000000000000), (320542015842021354026237/175921860444160000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial160.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial160.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial160.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial160 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 595359065652966469417430693780748), (Int.negOfNat 336540085618234698187308445895653), (Int.ofNat 35774381279463076410407583787221), (Int.ofNat 3659358165119286200410338105089), (Int.negOfNat 326493244285814804819598625547), (Int.negOfNat 166067020203741333212888286286), (Int.ofNat 2054565735850803648601944227), (Int.ofNat 3409698584450271551779089017), (Int.negOfNat 12424974438446574529809183), (Int.negOfNat 40490257237646588886992152), (Int.ofNat 92947043462326737608932), (Int.ofNat 312529141926265662486220), (Int.negOfNat 797375187629517972772), (Int.negOfNat 1683186550926283770647), (Int.ofNat 5324780113792045880), (Int.ofNat 6688127901607101636), (Int.ofNat 25925577305215911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(148839766413241617354357673445187/1407374883553280000000000000000000), (-336540085618234698187308445895653/5629499534213120000000000000000000), (35774381279463076410407583787221/5629499534213120000000000000000000), (3659358165119286200410338105089/5629499534213120000000000000000000), (-326493244285814804819598625547/5629499534213120000000000000000000), (-83033510101870666606444143143/2814749767106560000000000000000000), (2054565735850803648601944227/5629499534213120000000000000000000), (3409698584450271551779089017/5629499534213120000000000000000000), (-12424974438446574529809183/5629499534213120000000000000000000), (-5061282154705823610874019/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial160.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial160.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial160.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial160 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 84657988601655382415612902460653), (Int.negOfNat 171443509902725409128360477625956), (Int.ofNat 39194455689350505883264176042292), (Int.negOfNat 3582985939145148532477014309484), (Int.negOfNat 1072589949075180928141411297859), (Int.ofNat 67187839201932978598729507412), (Int.ofNat 25725582374094683539837470989), (Int.negOfNat 1072622424517027524811184949), (Int.negOfNat 381437785017215296787003784), (Int.ofNat 11782588327922589254158817), (Int.ofNat 3571882542486583155257063), (Int.negOfNat 89100105026457317660666), (Int.negOfNat 22711663312587164924886), (Int.ofNat 483733243858162587672), (Int.ofNat 103676844697826733523), (Int.negOfNat 2077786946684146480), (Int.negOfNat 352892353253949337), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(84657988601655382415612902460653/5629499534213120000000000000000000), (-42860877475681352282090119406489/1407374883553280000000000000000000), (9798613922337626470816044010573/1407374883553280000000000000000000), (-895746484786287133119253577371/1407374883553280000000000000000000), (-1072589949075180928141411297859/5629499534213120000000000000000000), (16796959800483244649682376853/1407374883553280000000000000000000), (25725582374094683539837470989/5629499534213120000000000000000000), (-1072622424517027524811184949/5629499534213120000000000000000000), (-47679723127151912098375473/703687441776640000000000000000000), (11782588327922589254158817/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial160.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial160.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial160.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial160 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 143705610393971508206341891627037), (Int.negOfNat 82497274619801925308375982955530), (Int.ofNat 2190721304092299125473451630306), (Int.negOfNat 6532204443250905903098679269224), (Int.ofNat 504426288957660703885086189562), (Int.ofNat 162787724672949089224714047090), (Int.negOfNat 14574670042943686006521243210), (Int.negOfNat 3002351352179362870944882841), (Int.ofNat 213314443648021086924554794), (Int.ofNat 34744567737565217458810091), (Int.negOfNat 1960003129912416318468562), (Int.negOfNat 265169235299366084289738), (Int.ofNat 12337077277846974282713), (Int.ofNat 1420856749436094424079), (Int.negOfNat 56205604631638051176), (Int.negOfNat 5666243536115616066), (Int.ofNat 172334450833624447), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-143705610393971508206341891627037/5629499534213120000000000000000000), (-8249727461980192530837598295553/562949953421312000000000000000000), (1095360652046149562736725815153/2814749767106560000000000000000000), (-816525555406363237887334908653/703687441776640000000000000000000), (252213144478830351942543094781/2814749767106560000000000000000000), (16278772467294908922471404709/562949953421312000000000000000000), (-1457467004294368600652124321/562949953421312000000000000000000), (-3002351352179362870944882841/5629499534213120000000000000000000), (106657221824010543462277397/2814749767106560000000000000000000), (34744567737565217458810091/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial160.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial160.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial160.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial160 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 340162053321503789107971658687968), (Int.negOfNat 126813739042393269545515909051970), (Int.negOfNat 16875405957492898253106936096642), (Int.ofNat 530945102369018602091837121947), (Int.ofNat 760635808306413089839338160887), (Int.negOfNat 120695990229645549085208551895), (Int.negOfNat 18887964340190924584823394420), (Int.ofNat 2568359017964180224567434519), (Int.ofNat 277495113456802047665173116), (Int.negOfNat 29855774235813802028685459), (Int.negOfNat 2592357321738490058462788), (Int.ofNat 225573053332739998081822), (Int.ofNat 16546844973720333665367), (Int.negOfNat 1195266798507768102661), (Int.negOfNat 76208032615278986804), (Int.ofNat 4767618273318331534), (Int.ofNat 241826338359153573), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-10630064166296993409624114333999/175921860444160000000000000000000), (-12681373904239326954551590905197/562949953421312000000000000000000), (-8437702978746449126553468048321/2814749767106560000000000000000000), (530945102369018602091837121947/5629499534213120000000000000000000), (760635808306413089839338160887/5629499534213120000000000000000000), (-24139198045929109817041710379/1125899906842624000000000000000000), (-944398217009546229241169721/281474976710656000000000000000000), (2568359017964180224567434519/5629499534213120000000000000000000), (69373778364200511916293279/1407374883553280000000000000000000), (-29855774235813802028685459/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial160.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial160.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial160.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial160 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 649562156039484757581947464686352), (Int.negOfNat 175530248497037449941526940575304), (Int.negOfNat 7560241908209078619166305508345), (Int.ofNat 512341623790019927040099290764), (Int.negOfNat 693762599582903975233426000042), (Int.negOfNat 80493988104039786188106877171), (Int.ofNat 23381128015453445631743861861), (Int.ofNat 1674966489533844389960351081), (Int.negOfNat 357073633535238656767364226), (Int.negOfNat 19726077726089376436316013), (Int.ofNat 3327195705876152470028537), (Int.ofNat 153665168037317971844064), (Int.negOfNat 20930960764160838541294), (Int.negOfNat 843323663320796945008), (Int.ofNat 94642769376567688957), (Int.ofNat 3534204010889237400), (Int.negOfNat 315061471525066923), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-40597634752467797348871716542897/351843720888320000000000000000000), (-21941281062129681242690867571913/703687441776640000000000000000000), (-1512048381641815723833261101669/1125899906842624000000000000000000), (128085405947504981760024822691/1407374883553280000000000000000000), (-346881299791451987616713000021/2814749767106560000000000000000000), (-80493988104039786188106877171/5629499534213120000000000000000000), (23381128015453445631743861861/5629499534213120000000000000000000), (1674966489533844389960351081/5629499534213120000000000000000000), (-178536816767619328383682113/2814749767106560000000000000000000), (-19726077726089376436316013/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial160.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial160.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial160.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial160 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 1038827988829768273627025653274132), (Int.negOfNat 223416351238222178661634481598898), (Int.negOfNat 21528594329005762290891001384125), (Int.negOfNat 4269412999887799096774467317372), (Int.negOfNat 57950890849843748994758680026), (Int.ofNat 170118784611348882711372233626), (Int.ofNat 5689340512691587922512832743), (Int.negOfNat 3451225136167231276721473143), (Int.negOfNat 91062424149951611111615867), (Int.ofNat 40780304337020949091759688), (Int.ofNat 915235506021449800947048), (Int.negOfNat 311274206832336346509070), (Int.negOfNat 6344160027714959405248), (Int.ofNat 1654096517199283419913), (Int.ofNat 31218738206737643160), (Int.negOfNat 6537260474997503764), (Int.negOfNat 59396813118636571), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-259706997207442068406756413318533/1407374883553280000000000000000000), (-111708175619111089330817240799449/2814749767106560000000000000000000), (-172228754632046098327128011073/45035996273704960000000000000000), (-1067353249971949774193616829343/1407374883553280000000000000000000), (-28975445424921874497379340013/2814749767106560000000000000000000), (85059392305674441355686116813/2814749767106560000000000000000000), (5689340512691587922512832743/5629499534213120000000000000000000), (-3451225136167231276721473143/5629499534213120000000000000000000), (-91062424149951611111615867/5629499534213120000000000000000000), (5097538042127618636469961/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial160.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial160.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial160.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial160 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 1601493569680812074869550890860456), (Int.negOfNat 349460581909412719832262993296219), (Int.negOfNat 35853821174591068162914505438933), (Int.ofNat 1106081484936329666745921114185), (Int.ofNat 1079658545974895450922230835768), (Int.negOfNat 12004457668285338009698365458), (Int.negOfNat 26953739533948097169756149427), (Int.ofNat 223033437126575495846527523), (Int.ofNat 415321962608110395194528850), (Int.negOfNat 1734606564475338716968796), (Int.negOfNat 3949168308024047005259968), (Int.ofNat 2701448896715071875978), (Int.ofNat 25144810522769363442280), (Int.ofNat 46128321478415276859), (Int.negOfNat 114127417991344136092), (Int.negOfNat 490297189231090712), (Int.ofNat 338807225872551957), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-200186696210101509358693861357557/703687441776640000000000000000000), (-349460581909412719832262993296219/5629499534213120000000000000000000), (-35853821174591068162914505438933/5629499534213120000000000000000000), (221216296987265933349184222837/1125899906842624000000000000000000), (134957318246861931365278854471/703687441776640000000000000000000), (-6002228834142669004849182729/2814749767106560000000000000000000), (-26953739533948097169756149427/5629499534213120000000000000000000), (223033437126575495846527523/5629499534213120000000000000000000), (8306439252162207903890577/112589990684262400000000000000000), (-433651641118834679242199/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial160.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial160.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial160.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial160 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 2419685965878610087952670027344566), (Int.negOfNat 450687659680362728875401525620787), (Int.negOfNat 9892392664378866196259096189063), (Int.ofNat 5752620207749008094498117693301), (Int.negOfNat 186869228513993196124055203318), (Int.negOfNat 163464119323177112079917065948), (Int.ofNat 9701219855702707095810386030), (Int.ofNat 3435169641527785450993325760), (Int.negOfNat 143182870767234960402793755), (Int.negOfNat 42238856291949589966816725), (Int.ofNat 1176609039150823138369559), (Int.ofNat 330497815603687687852439), (Int.negOfNat 6246147336223959069674), (Int.negOfNat 1782918928595627506269), (Int.ofNat 22950916791275346085), (Int.ofNat 7075651656008048720), (Int.negOfNat 130947963571042109), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-1209842982939305043976335013672283/2814749767106560000000000000000000), (-450687659680362728875401525620787/5629499534213120000000000000000000), (-9892392664378866196259096189063/5629499534213120000000000000000000), (5752620207749008094498117693301/5629499534213120000000000000000000), (-93434614256996598062027601659/2814749767106560000000000000000000), (-40866029830794278019979266487/1407374883553280000000000000000000), (970121985570270709581038603/562949953421312000000000000000000), (10734905129774329534354143/17592186044416000000000000000000), (-28636574153446992080558751/1125899906842624000000000000000000), (-1689554251677983598672669/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial160.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial160.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial160.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial160 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 3321826512913305039104850842742602), (Int.negOfNat 437115577226169687897527780175327), (Int.ofNat 11269012817921350299151894679050), (Int.ofNat 742169024769083889441252001625), (Int.negOfNat 579889497428320406052104332065), (Int.ofNat 110289227155431101075525992457), (Int.ofNat 21485841241164210649187097446), (Int.negOfNat 2396732423103568553883365443), (Int.negOfNat 368560825980153688993950987), (Int.ofNat 26128444051804125382641363), (Int.ofNat 3683515185689290558221822), (Int.negOfNat 178991488070598032451653), (Int.negOfNat 24167445709402842464362), (Int.ofNat 845650323035478141343), (Int.ofNat 112332359215423696954), (Int.negOfNat 2838811179203408656), (Int.negOfNat 362552980220036991), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-1660913256456652519552425421371301/2814749767106560000000000000000000), (-437115577226169687897527780175327/5629499534213120000000000000000000), (225380256358427005983037893581/112589990684262400000000000000000), (5937352198152671115530016013/45035996273704960000000000000000), (-115977899485664081210420866413/1125899906842624000000000000000000), (110289227155431101075525992457/5629499534213120000000000000000000), (10742920620582105324593548723/2814749767106560000000000000000000), (-2396732423103568553883365443/5629499534213120000000000000000000), (-368560825980153688993950987/5629499534213120000000000000000000), (26128444051804125382641363/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial160.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial160.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial160.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial160 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 4149802587306775782242464095096724), (Int.negOfNat 390116177897375803976276178915553), (Int.ofNat 13669687751253707686869939096949), (Int.ofNat 2136812119679645124572434778215), (Int.ofNat 872926826555255885342466987809), (Int.ofNat 76696205521426810257319808706), (Int.negOfNat 27226196979466290731009429191), (Int.negOfNat 2417385967652671965186840414), (Int.ofNat 389924970973581938899827936), (Int.ofNat 33306310230881639790592447), (Int.negOfNat 3354808759367652982165546), (Int.negOfNat 276988126777398278300734), (Int.ofNat 19287176579793841371775), (Int.ofNat 1552209784284492605055), (Int.negOfNat 79348331658209640412), (Int.negOfNat 6329247156189079120), (Int.ofNat 321292740260720789), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-1037450646826693945560616023774181/1407374883553280000000000000000000), (-390116177897375803976276178915553/5629499534213120000000000000000000), (13669687751253707686869939096949/5629499534213120000000000000000000), (427362423935929024914486955643/1125899906842624000000000000000000), (872926826555255885342466987809/5629499534213120000000000000000000), (38348102760713405128659904353/2814749767106560000000000000000000), (-27226196979466290731009429191/5629499534213120000000000000000000), (-1208692983826335982593420207/2814749767106560000000000000000000), (12185155342924435590619623/175921860444160000000000000000000), (33306310230881639790592447/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial160.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial160.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial160.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial160 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 4843779528087773824912945222868006), (Int.negOfNat 281580474822119885197533017034622), (Int.ofNat 46225020853992829387866370909529), (Int.ofNat 7295275392538551769458489752399), (Int.negOfNat 153416893417311873035601106167), (Int.negOfNat 244121064131802038256199874310), (Int.negOfNat 8976374973206670042317672922), (Int.ofNat 4550306134611968546092253249), (Int.ofNat 217239710225518035824876981), (Int.negOfNat 49653077138299259109112593), (Int.negOfNat 2512974319600500091319790), (Int.ofNat 348617976524438525862048), (Int.ofNat 17942693914992184740680), (Int.negOfNat 1699414356100061065242), (Int.negOfNat 87474163459072339593), (Int.ofNat 6135978212070444324), (Int.ofNat 322850475670962465), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-2421889764043886912456472611434003/2814749767106560000000000000000000), (-140790237411059942598766508517311/2814749767106560000000000000000000), (46225020853992829387866370909529/5629499534213120000000000000000000), (7295275392538551769458489752399/5629499534213120000000000000000000), (-153416893417311873035601106167/5629499534213120000000000000000000), (-24412106413180203825619987431/562949953421312000000000000000000), (-4488187486603335021158836461/2814749767106560000000000000000000), (4550306134611968546092253249/5629499534213120000000000000000000), (217239710225518035824876981/5629499534213120000000000000000000), (-49653077138299259109112593/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial160.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial160.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial160.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial160 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 5173908394309725368108019750492583), (Int.negOfNat 33161584035463848947676685023283), (Int.ofNat 67830732413359735384861338861568), (Int.negOfNat 2484995347368358408102897519555), (Int.negOfNat 1833485095040382613283261512048), (Int.ofNat 18844498085921136164998910274), (Int.ofNat 43040367164664505760423045588), (Int.ofNat 545440167249787026534203161), (Int.negOfNat 607588931518040258491343069), (Int.negOfNat 14403053317289855104143437), (Int.ofNat 5298841520766311840098590), (Int.ofNat 154831528763535926280332), (Int.negOfNat 30892278813214347459320), (Int.negOfNat 988175667304326447918), (Int.ofNat 128827019313740105307), (Int.ofNat 4296311122860616636), (Int.negOfNat 464019760952163265), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-5173908394309725368108019750492583/5629499534213120000000000000000000), (-33161584035463848947676685023283/5629499534213120000000000000000000), (2070029675700675518336832851/171798691840000000000000000000), (-496999069473671681620579503911/1125899906842624000000000000000000), (-114592818440023913330203844503/351843720888320000000000000000000), (9422249042960568082499455137/2814749767106560000000000000000000), (10760091791166126440105761397/1407374883553280000000000000000000), (545440167249787026534203161/5629499534213120000000000000000000), (-607588931518040258491343069/5629499534213120000000000000000000), (-14403053317289855104143437/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial160.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial160.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial160.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial160 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 5014854239670774826670133942278354), (Int.ofNat 159058268143413178391956326022115), (Int.ofNat 20028941150388138685394213790356), (Int.negOfNat 10289157742336284753305731157837), (Int.ofNat 425153536297582966458503282616), (Int.ofNat 323901602366367747218850850790), (Int.negOfNat 8896479964206204643018501791), (Int.negOfNat 6175934333883512080987367026), (Int.ofNat 32824514899403554893678016), (Int.ofNat 68946119241965337516895603), (Int.ofNat 536764199824360859041894), (Int.negOfNat 488685594071446840958166), (Int.negOfNat 7222049318560863372565), (Int.ofNat 2395194982071702159785), (Int.ofNat 44552808953250262008), (Int.negOfNat 8798410161365352120), (Int.negOfNat 211784460776166701), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-2507427119835387413335066971139177/2814749767106560000000000000000000), (31811653628682635678391265204423/1125899906842624000000000000000000), (5007235287597034671348553447589/1407374883553280000000000000000000), (-10289157742336284753305731157837/5629499534213120000000000000000000), (53144192037197870807312910327/703687441776640000000000000000000), (32390160236636774721885085079/562949953421312000000000000000000), (-8896479964206204643018501791/5629499534213120000000000000000000), (-3087967166941756040493683513/2814749767106560000000000000000000), (512883045303180545213719/87960930222080000000000000000000), (68946119241965337516895603/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial160.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial160.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial160.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial160 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 4683084544394857003109836384627749), (Int.ofNat 150935899240821537285560954255555), (Int.negOfNat 11506724537404815719845465342763), (Int.ofNat 1603157505528073562271196404694), (Int.ofNat 1702427512082764767936521743420), (Int.negOfNat 157979933098264644955335918061), (Int.negOfNat 50662480683803909454985858624), (Int.ofNat 2297249899997843738780935133), (Int.ofNat 767983637552624783795788523), (Int.negOfNat 13170251997202057325229103), (Int.negOfNat 6789280077510770625184608), (Int.ofNat 20860066552555800393983), (Int.ofNat 39572570216308768868778), (Int.ofNat 171130880910614643977), (Int.negOfNat 164818708442735312546), (Int.negOfNat 1375351959586852584), (Int.ofNat 551213774196207859), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-4683084544394857003109836384627749/5629499534213120000000000000000000), (30187179848164307457112190851111/1125899906842624000000000000000000), (-11506724537404815719845465342763/5629499534213120000000000000000000), (801578752764036781135598202347/2814749767106560000000000000000000), (85121375604138238396826087171/281474976710656000000000000000000), (-157979933098264644955335918061/5629499534213120000000000000000000), (-791601260684436085234154041/87960930222080000000000000000000), (2297249899997843738780935133/5629499534213120000000000000000000), (767983637552624783795788523/5629499534213120000000000000000000), (-13170251997202057325229103/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial160.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial160.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial160.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial160 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 4394996140541340892217537759983291), (Int.ofNat 158010656064758908350596399575590), (Int.ofNat 16957395933696986518115566424296), (Int.ofNat 3290248894172813326746291469173), (Int.negOfNat 1552310097104066714144011207393), (Int.negOfNat 305687874054444433661246325118), (Int.ofNat 38410812387029120910215995168), (Int.ofNat 7230908088751004189216332350), (Int.negOfNat 374291913623417057016246305), (Int.negOfNat 83014884022415197379517455), (Int.ofNat 1997687589225334361020589), (Int.ofNat 584952520727954601536691), (Int.negOfNat 6386098443517907391254), (Int.negOfNat 2843052549271049718211), (Int.ofNat 10735021364494234705), (Int.ofNat 10336339806100489520), (Int.ofNat 21439684086488021), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-4394996140541340892217537759983291/5629499534213120000000000000000000), (15801065606475890835059639957559/562949953421312000000000000000000), (2119674491712123314764445803037/703687441776640000000000000000000), (3290248894172813326746291469173/5629499534213120000000000000000000), (-1552310097104066714144011207393/5629499534213120000000000000000000), (-152843937027222216830623162559/2814749767106560000000000000000000), (1200337887094660028444249849/175921860444160000000000000000000), (144618161775020083784326647/112589990684262400000000000000000), (-74858382724683411403249261/1125899906842624000000000000000000), (-16602976804483039475903491/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial160.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial160.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial160.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial160 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 4016193506491927609641322717353476), (Int.ofNat 201250567559670839791715609002606), (Int.negOfNat 11948468817939057262439287889869), (Int.negOfNat 12223859612983055770148909057993), (Int.negOfNat 984062205318821656617190173307), (Int.ofNat 459460487991412778602257820424), (Int.ofNat 56328816179138973492992447605), (Int.negOfNat 6158547611064200986590069813), (Int.negOfNat 894318301776607973575734220), (Int.ofNat 45670833223723561234302286), (Int.ofNat 7765810388317628015160602), (Int.negOfNat 221605284684196211814328), (Int.negOfNat 44388396812163836664320), (Int.ofNat 767059561145395385821), (Int.ofNat 182639678680969269248), (Int.negOfNat 1894158597220842288), (Int.negOfNat 574959528543692893), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-1004048376622981902410330679338369/1407374883553280000000000000000000), (100625283779835419895857804501303/2814749767106560000000000000000000), (-11948468817939057262439287889869/5629499534213120000000000000000000), (-12223859612983055770148909057993/5629499534213120000000000000000000), (-984062205318821656617190173307/5629499534213120000000000000000000), (57432560998926597325282227553/703687441776640000000000000000000), (11265763235827794698598489521/1125899906842624000000000000000000), (-6158547611064200986590069813/5629499534213120000000000000000000), (-44715915088830398678786711/281474976710656000000000000000000), (22835416611861780617151143/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial160.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial160.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial160.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial160 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 3757700869394578333674232302561202), (Int.ofNat 19319007338296206548620724229525), (Int.negOfNat 64083666116631167306472253201239), (Int.ofNat 2594071049905831730300680918779), (Int.ofNat 4538231916947259831633173094911), (Int.ofNat 361506115964384041755196960203), (Int.negOfNat 78872444273751137678496004947), (Int.negOfNat 8572906552279393361330953647), (Int.ofNat 744806340679023443353218903), (Int.ofNat 93169687087733366345921532), (Int.negOfNat 4607143456958005891052592), (Int.negOfNat 630549571038980205608390), (Int.ofNat 20492033395174225850072), (Int.ofNat 2987335130664218767287), (Int.negOfNat 69366670955231456500), (Int.negOfNat 10621134775802759076), (Int.ofNat 168905092603190659), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-1878850434697289166837116151280601/2814749767106560000000000000000000), (772760293531848261944828969181/225179981368524800000000000000000), (-64083666116631167306472253201239/5629499534213120000000000000000000), (2594071049905831730300680918779/5629499534213120000000000000000000), (4538231916947259831633173094911/5629499534213120000000000000000000), (361506115964384041755196960203/5629499534213120000000000000000000), (-78872444273751137678496004947/5629499534213120000000000000000000), (-8572906552279393361330953647/5629499534213120000000000000000000), (744806340679023443353218903/5629499534213120000000000000000000), (23292421771933341586480383/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial160.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial160.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial160.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial160 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 3876377741715001771339776761981713), (Int.negOfNat 49779759539631412476139376595979), (Int.ofNat 66323451582090012963170454458837), (Int.ofNat 37681038100817546138019846033267), (Int.ofNat 2145412967747108251259935611691), (Int.negOfNat 836419814727176358720438701909), (Int.negOfNat 75877105484160426943417875529), (Int.ofNat 9809428273773430986719916969), (Int.ofNat 1024481838879991715101758734), (Int.negOfNat 74845329835451073332685147), (Int.negOfNat 8200432594704431658174123), (Int.ofNat 406798854436676255406656), (Int.ofNat 44774999960509138310646), (Int.negOfNat 1661706582907796965392), (Int.negOfNat 179281149585473651903), (Int.ofNat 5195077665218651600), (Int.ofNat 598705282891177927), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-3876377741715001771339776761981713/5629499534213120000000000000000000), (-49779759539631412476139376595979/5629499534213120000000000000000000), (66323451582090012963170454458837/5629499534213120000000000000000000), (37681038100817546138019846033267/5629499534213120000000000000000000), (2145412967747108251259935611691/5629499534213120000000000000000000), (-836419814727176358720438701909/5629499534213120000000000000000000), (-75877105484160426943417875529/5629499534213120000000000000000000), (9809428273773430986719916969/5629499534213120000000000000000000), (512240919439995857550879367/2814749767106560000000000000000000), (-74845329835451073332685147/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial160.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial160.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial160.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial160 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 3405017954702806065265320098448578), (Int.ofNat 660092568035415477142234999544391), (Int.ofNat 266778106694547618926180097985903), (Int.ofNat 16069655016911535389975535486068), (Int.negOfNat 7267258610206089530133299076520), (Int.negOfNat 665144901888486441545522535855), (Int.ofNat 106524067713264235326799378232), (Int.ofNat 10583998957034952305494631801), (Int.negOfNat 1004166056777159164344255054), (Int.negOfNat 98663572959519403599087131), (Int.ofNat 6639994292978291435338962), (Int.ofNat 617985840185235860548148), (Int.negOfNat 32397633647800497157533), (Int.negOfNat 2800604889143764335379), (Int.ofNat 120948693547651710856), (Int.ofNat 9599250410311273506), (Int.negOfNat 367165120742031017), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-1702508977351403032632660049224289/2814749767106560000000000000000000), (660092568035415477142234999544391/5629499534213120000000000000000000), (266778106694547618926180097985903/5629499534213120000000000000000000), (4017413754227883847493883871517/1407374883553280000000000000000000), (-181681465255152238253332476913/140737488355328000000000000000000), (-133028980377697288309104507171/1125899906842624000000000000000000), (13315508464158029415849922279/703687441776640000000000000000000), (10583998957034952305494631801/5629499534213120000000000000000000), (-502083028388579582172127527/2814749767106560000000000000000000), (-98663572959519403599087131/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial160.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial160.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial160.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial160.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial160 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial160 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial160 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 4989969201867667155513115869446298), (Int.negOfNat 896603922253122597949133870370316), (Int.ofNat 313731605346841353164818507569837), (Int.negOfNat 14061642891914631726243156687947), (Int.negOfNat 7517858310454435103166395337949), (Int.ofNat 659365069375602716344375058045), (Int.ofNat 107083919741607262335877670010), (Int.negOfNat 10575344885577278392730894651), (Int.negOfNat 1004852402411700718447245754), (Int.ofNat 98655598863346447879329281), (Int.ofNat 6640523562436157066094212), (Int.negOfNat 617980620359249285649348), (Int.negOfNat 32397633647800497157533), (Int.ofNat 2800604889143764335379), (Int.ofNat 120948693547651710856), (Int.negOfNat 9599250410311273506), (Int.negOfNat 367165120742031017), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-2494984600933833577756557934723149/2814749767106560000000000000000000), (-224150980563280649487283467592579/1407374883553280000000000000000000), (313731605346841353164818507569837/5629499534213120000000000000000000), (-14061642891914631726243156687947/5629499534213120000000000000000000), (-7517858310454435103166395337949/5629499534213120000000000000000000), (131873013875120543268875011609/1125899906842624000000000000000000), (10708391974160726233587767001/562949953421312000000000000000000), (-10575344885577278392730894651/5629499534213120000000000000000000), (-502426201205850359223622877/2814749767106560000000000000000000), (98655598863346447879329281/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial160.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial160.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial160.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 5734631396535285521743600875932632), (Int.ofNat 16807618606707792636774565890854), (Int.ofNat 118987163148016517517231086169174), (Int.negOfNat 37815858758426998494436937343709), (Int.ofNat 1872235639676737890720995135940), (Int.ofNat 837765980195925652107159640824), (Int.negOfNat 75276489134616324441664229829), (Int.negOfNat 9812376466775510166174057269), (Int.ofNat 1023751585351969970958884034), (Int.ofNat 74848531807322696701090747), (Int.negOfNat 8199871299013159955969023), (Int.negOfNat 406800811871421220993706), (Int.ofNat 44774999960509138310646), (Int.ofNat 1661706582907796965392), (Int.negOfNat 179281149585473651903), (Int.negOfNat 5195077665218651600), (Int.ofNat 598705282891177927), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-716828924566910690217950109491579/703687441776640000000000000000000), (8403809303353896318387282945427/2814749767106560000000000000000000), (59493581574008258758615543084587/2814749767106560000000000000000000), (-37815858758426998494436937343709/5629499534213120000000000000000000), (93611781983836894536049756797/281474976710656000000000000000000), (104720747524490706513394955103/703687441776640000000000000000000), (-75276489134616324441664229829/5629499534213120000000000000000000), (-9812376466775510166174057269/5629499534213120000000000000000000), (511875792675984985479442017/2814749767106560000000000000000000), (74848531807322696701090747/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial160.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial160.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial160.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 5476612407690787886033927108972601), (Int.ofNat 148225128828841477858382840552108), (Int.negOfNat 18536561868647077114652536361678), (Int.negOfNat 4767298988365038997272484796769), (Int.ofNat 4312930173226930379345056029563), (Int.negOfNat 353516467286369529438394482589), (Int.negOfNat 78390902019243888863613454697), (Int.ofNat 8559255653299416349484884747), (Int.ofNat 744229662946371869136601653), (Int.negOfNat 93156231301590040914499582), (Int.negOfNat 4606703050702597640539892), (Int.ofNat 630541088821752021397840), (Int.ofNat 20492033395174225850072), (Int.negOfNat 2987335130664218767287), (Int.negOfNat 69366670955231456500), (Int.ofNat 10621134775802759076), (Int.ofNat 168905092603190659), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-5476612407690787886033927108972601/5629499534213120000000000000000000), (37056282207210369464595710138027/1407374883553280000000000000000000), (-9268280934323538557326268180839/2814749767106560000000000000000000), (-4767298988365038997272484796769/5629499534213120000000000000000000), (4312930173226930379345056029563/5629499534213120000000000000000000), (-353516467286369529438394482589/5629499534213120000000000000000000), (-78390902019243888863613454697/5629499534213120000000000000000000), (8559255653299416349484884747/5629499534213120000000000000000000), (744229662946371869136601653/5629499534213120000000000000000000), (-46578115650795020457249791/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial160.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial160.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial160.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 5238534407030115848526708616144250), (Int.ofNat 115918549578532228929538079329165), (Int.ofNat 15896627991751898355431419323092), (Int.ofNat 8636251232077554554588528155863), (Int.negOfNat 1104983281398363621825386078833), (Int.negOfNat 447066961051820967827187871971), (Int.ofNat 56565038429013876013499895333), (Int.ofNat 6137978951153598788305312613), (Int.negOfNat 894586625987783429240521120), (Int.negOfNat 45650834590789558691742586), (Int.ofNat 7766009377621157176603802), (Int.ofNat 221592887597478096429678), (Int.negOfNat 44388396812163836664320), (Int.negOfNat 767059561145395385821), (Int.ofNat 182639678680969269248), (Int.ofNat 1894158597220842288), (Int.negOfNat 574959528543692893), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-20954137628120463394106834464577/22517998136852480000000000000000), (23183709915706445785907615865833/1125899906842624000000000000000000), (3974156997937974588857854830773/1407374883553280000000000000000000), (8636251232077554554588528155863/5629499534213120000000000000000000), (-1104983281398363621825386078833/5629499534213120000000000000000000), (-447066961051820967827187871971/5629499534213120000000000000000000), (56565038429013876013499895333/5629499534213120000000000000000000), (6137978951153598788305312613/5629499534213120000000000000000000), (-5591166412423646432753257/35184372088832000000000000000000), (-22825417295394779345871293/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial160.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial160.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial160.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 4901845003805561031344507024835222), (Int.ofNat 224645467560724348608748192171907), (Int.ofNat 21408703232797232688668893830252), (Int.negOfNat 7323578510821459398719610043336), (Int.negOfNat 1541099556370588106328254319560), (Int.ofNat 319109628155305527302504669539), (Int.ofNat 38342935634244403270750754850), (Int.negOfNat 7252768350563415127733347600), (Int.negOfNat 374181842786336001462935755), (Int.ofNat 83035944284697096281538455), (Int.ofNat 1997591839320545947839239), (Int.negOfNat 584966222771169360646041), (Int.negOfNat 6386098443517907391254), (Int.ofNat 2843052549271049718211), (Int.ofNat 10735021364494234705), (Int.negOfNat 10336339806100489520), (Int.ofNat 21439684086488021), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-2450922501902780515672253512417611/2814749767106560000000000000000000), (224645467560724348608748192171907/5629499534213120000000000000000000), (5352175808199308172167223457563/1407374883553280000000000000000000), (-915447313852682424839951255417/703687441776640000000000000000000), (-38527488909264702658206357989/140737488355328000000000000000000), (319109628155305527302504669539/5629499534213120000000000000000000), (766858712684888065415015097/112589990684262400000000000000000), (-18131920876408537819333369/14073748835532800000000000000000), (-74836368557267200292587151/1125899906842624000000000000000000), (16607188856939419256307691/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial160.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial160.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial160.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 4438480806751496378590943271194510), (Int.ofNat 202535310676906115586964793788984), (Int.negOfNat 29943289327238998290932804873351), (Int.negOfNat 5032726214154593435542705643013), (Int.ofNat 1837868472455460552189669079843), (Int.ofNat 168841516733607426993877526218), (Int.negOfNat 51010434116881248599453107274), (Int.negOfNat 2314476424661409954466345583), (Int.ofNat 768438658190659441781816823), (Int.ofNat 13186626148030535720601503), (Int.negOfNat 6789642510059198772909458), (Int.negOfNat 20870506204528950191583), (Int.ofNat 39572570216308768868778), (Int.negOfNat 171130880910614643977), (Int.negOfNat 164818708442735312546), (Int.ofNat 1375351959586852584), (Int.ofNat 551213774196207859), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-443848080675149637859094327119451/562949953421312000000000000000000), (25316913834613264448370599223623/703687441776640000000000000000000), (-29943289327238998290932804873351/5629499534213120000000000000000000), (-5032726214154593435542705643013/5629499534213120000000000000000000), (1837868472455460552189669079843/5629499534213120000000000000000000), (84420758366803713496938763109/2814749767106560000000000000000000), (-25505217058440624299726553637/2814749767106560000000000000000000), (-2314476424661409954466345583/5629499534213120000000000000000000), (768438658190659441781816823/5629499534213120000000000000000000), (13186626148030535720601503/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial160.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial160.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial160.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 4162000614515204854756113483196660), (Int.ofNat 84640872693702941451941186892952), (Int.negOfNat 14959724799709646805883405839985), (Int.ofNat 8313158107883753094375876207768), (Int.ofNat 644080066620553637952477680742), (Int.negOfNat 318428833031874939280928290451), (Int.negOfNat 9424996055458121625034276991), (Int.ofNat 6167949223136951538810510026), (Int.ofNat 33497166179449766414090366), (Int.negOfNat 68938870219860968732418153), (Int.ofNat 536235330523372336223094), (Int.ofNat 488681679201956909784066), (Int.negOfNat 7222049318560863372565), (Int.negOfNat 2395194982071702159785), (Int.ofNat 44552808953250262008), (Int.ofNat 8798410161365352120), (Int.negOfNat 211784460776166701), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-208100030725760242737805674159833/281474976710656000000000000000000), (10580109086712867681492648361619/703687441776640000000000000000000), (-2991944959941929361176681167997/1125899906842624000000000000000000), (1039144763485469136796984525971/703687441776640000000000000000000), (322040033310276818976238840371/2814749767106560000000000000000000), (-318428833031874939280928290451/5629499534213120000000000000000000), (-9424996055458121625034276991/5629499534213120000000000000000000), (3083974611568475769405255013/2814749767106560000000000000000000), (16748583089724883207045183/2814749767106560000000000000000000), (-68938870219860968732418153/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial160.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial160.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial160.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 3985775867015506099129890131830856), (Int.ofNat 120533186302012876312799647501386), (Int.ofNat 26547149670252960427654801201048), (Int.ofNat 2391520574765808076027641285350), (Int.negOfNat 1593002329841268506392102898174), (Int.negOfNat 20073076383253642736057009998), (Int.ofNat 42478442159193232640330680538), (Int.negOfNat 542142862852052113912917111), (Int.negOfNat 606884572331823688374335669), (Int.ofNat 14399257790398252704901787), (Int.ofNat 5298292134081224831999890), (Int.negOfNat 154828266372294316968582), (Int.negOfNat 30892278813214347459320), (Int.ofNat 988175667304326447918), (Int.ofNat 128827019313740105307), (Int.negOfNat 4296311122860616636), (Int.negOfNat 464019760952163265), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-498221983376938262391236266478857/703687441776640000000000000000000), (60266593151006438156399823750693/2814749767106560000000000000000000), (3318393708781620053456850150131/703687441776640000000000000000000), (47830411495316161520552825707/112589990684262400000000000000000), (-796501164920634253196051449087/2814749767106560000000000000000000), (-10036538191626821368028504999/2814749767106560000000000000000000), (21239221079596616320165340269/2814749767106560000000000000000000), (-542142862852052113912917111/5629499534213120000000000000000000), (-606884572331823688374335669/5629499534213120000000000000000000), (14399257790398252704901787/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial160.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial160.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial160.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 3643012879005351776306394281322098), (Int.ofNat 210187508398947749964068354910212), (Int.ofNat 9922481843957036772437077936419), (Int.negOfNat 5600859181961407767605268405224), (Int.ofNat 42754169261086619876399738954), (Int.ofNat 236729932895304467159663552031), (Int.negOfNat 9417591976588238478577730112), (Int.negOfNat 4536792455542743865084712299), (Int.ofNat 217782472863124246420289831), (Int.ofNat 49639353749589951185805193), (Int.negOfNat 2513394153672571556357890), (Int.negOfNat 348608841828962019789148), (Int.ofNat 17942693914992184740680), (Int.ofNat 1699414356100061065242), (Int.negOfNat 87474163459072339593), (Int.negOfNat 6135978212070444324), (Int.ofNat 322850475670962465), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-1821506439502675888153197140661049/2814749767106560000000000000000000), (52546877099736937491017088727553/1407374883553280000000000000000000), (9922481843957036772437077936419/5629499534213120000000000000000000), (-700107397745175970950658550653/703687441776640000000000000000000), (21377084630543309938199869477/2814749767106560000000000000000000), (236729932895304467159663552031/5629499534213120000000000000000000), (-147149874634191226227777033/87960930222080000000000000000000), (-4536792455542743865084712299/5629499534213120000000000000000000), (217782472863124246420289831/5629499534213120000000000000000000), (49639353749589951185805193/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial160.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial160.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial160.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 3220600853250316115878567248206511), (Int.ofNat 199454096057092055713868575029545), (Int.negOfNat 8445445057231304527749346943292), (Int.ofNat 769193087209370366642861348939), (Int.ofNat 973044708554799463944347927588), (Int.negOfNat 88034401203024848002510632774), (Int.negOfNat 27427921682637965788703261441), (Int.ofNat 2437256945829818139382528014), (Int.ofNat 390158514027759962938411536), (Int.negOfNat 33326124919533743248295697), (Int.negOfNat 3354983316417593727154746), (Int.ofNat 277001176342364715547734), (Int.ofNat 19287176579793841371775), (Int.negOfNat 1552209784284492605055), (Int.negOfNat 79348331658209640412), (Int.ofNat 6329247156189079120), (Int.ofNat 321292740260720789), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-3220600853250316115878567248206511/5629499534213120000000000000000000), (39890819211418411142773715005909/1125899906842624000000000000000000), (-2111361264307826131937336735823/1407374883553280000000000000000000), (769193087209370366642861348939/5629499534213120000000000000000000), (243261177138699865986086981897/1407374883553280000000000000000000), (-44017200601512424001255316387/2814749767106560000000000000000000), (-27427921682637965788703261441/5629499534213120000000000000000000), (1218628472914909069691264007/2814749767106560000000000000000000), (24384907126734997683650721/351843720888320000000000000000000), (-33326124919533743248295697/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial160.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial160.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial160.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 2837932685672599021772691744027801), (Int.ofNat 195132107004386078019809260540773), (Int.ofNat 8050949685304840788585340120383), (Int.ofNat 2490413052280331174300717899516), (Int.negOfNat 599513307608767025470703464172), (Int.negOfNat 122315302085101886063806950916), (Int.ofNat 21574756679090499715621355146), (Int.ofNat 2417387931335265440953918793), (Int.negOfNat 368698095946141259543901637), (Int.negOfNat 26148853952342440388141013), (Int.ofNat 3683631579138863063646022), (Int.ofNat 179004537635564469698653), (Int.negOfNat 24167445709402842464362), (Int.negOfNat 845650323035478141343), (Int.ofNat 112332359215423696954), (Int.ofNat 2838811179203408656), (Int.negOfNat 362552980220036991), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-2837932685672599021772691744027801/5629499534213120000000000000000000), (195132107004386078019809260540773/5629499534213120000000000000000000), (8050949685304840788585340120383/5629499534213120000000000000000000), (622603263070082793575179474879/1407374883553280000000000000000000), (-149878326902191756367675866043/1407374883553280000000000000000000), (-30578825521275471515951737729/1407374883553280000000000000000000), (10787378339545249857810677573/2814749767106560000000000000000000), (2417387931335265440953918793/5629499534213120000000000000000000), (-368698095946141259543901637/5629499534213120000000000000000000), (-26148853952342440388141013/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial160.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial160.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial160.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 2407461201307853851425292517019135), (Int.ofNat 233059012519639358097651515079734), (Int.ofNat 4886861106765429725535438925204), (Int.negOfNat 3132631426443694210175193356774), (Int.negOfNat 315869240714311183538203976243), (Int.ofNat 154138770321404098579146732454), (Int.ofNat 10050803959469291712697670640), (Int.negOfNat 3419470389137490582321748510), (Int.negOfNat 143649936511351275384749355), (Int.ofNat 42223487988798943002082975), (Int.ofNat 1176985118943227745009059), (Int.negOfNat 330488028429962859917189), (Int.negOfNat 6246147336223959069674), (Int.ofNat 1782918928595627506269), (Int.ofNat 22950916791275346085), (Int.negOfNat 7075651656008048720), (Int.negOfNat 130947963571042109), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-481492240261570770285058503403827/1125899906842624000000000000000000), (116529506259819679048825757539867/2814749767106560000000000000000000), (1221715276691357431383859731301/1407374883553280000000000000000000), (-1566315713221847105087596678387/2814749767106560000000000000000000), (-315869240714311183538203976243/5629499534213120000000000000000000), (77069385160702049289573366227/2814749767106560000000000000000000), (125635049493366146408720883/70368744177664000000000000000000), (-341947038913749058232174851/562949953421312000000000000000000), (-28729987302270255076949871/1125899906842624000000000000000000), (1688939519551957720083319/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial160.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial160.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial160.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 1946787329606806576185625519643614), (Int.ofNat 217588428653749534450304019939215), (Int.negOfNat 9103116060659087246976492563745), (Int.ofNat 172704828823386809410129135837), (Int.ofNat 882196232768021934110968397799), (Int.ofNat 7955921693695668581435133051), (Int.negOfNat 26445611514897306134634065665), (Int.negOfNat 216613706906396261192377173), (Int.ofNat 414657022198810523316821450), (Int.ofNat 1728505850728263895052496), (Int.negOfNat 3948639131602448968320568), (Int.negOfNat 2697534027225140701878), (Int.ofNat 25144810522769363442280), (Int.negOfNat 46128321478415276859), (Int.negOfNat 114127417991344136092), (Int.ofNat 490297189231090712), (Int.ofNat 338807225872551957), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-973393664803403288092812759821807/2814749767106560000000000000000000), (43517685730749906890060803987843/1125899906842624000000000000000000), (-1820623212131817449395298512749/1125899906842624000000000000000000), (172704828823386809410129135837/5629499534213120000000000000000000), (882196232768021934110968397799/5629499534213120000000000000000000), (7955921693695668581435133051/5629499534213120000000000000000000), (-5289122302979461226926813133/1125899906842624000000000000000000), (-216613706906396261192377173/5629499534213120000000000000000000), (8293140443976210466336429/112589990684262400000000000000000), (108031615670516493440781/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial160.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial160.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial160.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 1533888725344836233798032422559648), (Int.ofNat 207349521712139427518038291403813), (Int.ofNat 7956901555382388115839691941999), (Int.ofNat 3890238788550835408874180090911), (Int.negOfNat 264375451163359536165920529553), (Int.negOfNat 167836367235916159445930586874), (Int.ofNat 6210589805053407600090096693), (Int.ofNat 3446648396217214634067803043), (Int.negOfNat 91739123138135316739745317), (Int.negOfNat 40775484767085870506673088), (Int.ofNat 915771678743855471214648), (Int.ofNat 311270944441094737197320), (Int.negOfNat 6344160027714959405248), (Int.negOfNat 1654096517199283419913), (Int.ofNat 31218738206737643160), (Int.ofNat 6537260474997503764), (Int.negOfNat 59396813118636571), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-47934022667026132306188513204989/175921860444160000000000000000000), (207349521712139427518038291403813/5629499534213120000000000000000000), (7956901555382388115839691941999/5629499534213120000000000000000000), (3890238788550835408874180090911/5629499534213120000000000000000000), (-264375451163359536165920529553/5629499534213120000000000000000000), (-83918183617958079722965293437/2814749767106560000000000000000000), (6210589805053407600090096693/5629499534213120000000000000000000), (3446648396217214634067803043/5629499534213120000000000000000000), (-91739123138135316739745317/5629499534213120000000000000000000), (-637116949485716726666767/87960930222080000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial160.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial160.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial160.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1065045113462033526190439046209613), (Int.ofNat 266529669787831229856742580475816), (Int.ofNat 14999452551859240980280278547428), (Int.negOfNat 2371957364640421563382536799136), (Int.negOfNat 848100940940396641347600695741), (Int.ofNat 88357712409580265071050423288), (Int.ofNat 23767491512386966279575291111), (Int.negOfNat 1689184938413183814490808931), (Int.negOfNat 357573355152451010367949576), (Int.ofNat 19740449792888604171662763), (Int.ofNat 3327590998096158918223237), (Int.negOfNat 153674955211042799779314), (Int.negOfNat 20930960764160838541294), (Int.ofNat 843323663320796945008), (Int.ofNat 94642769376567688957), (Int.negOfNat 3534204010889237400), (Int.negOfNat 315061471525066923), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-1065045113462033526190439046209613/5629499534213120000000000000000000), (33316208723478903732092822559477/703687441776640000000000000000000), (3749863137964810245070069636857/1407374883553280000000000000000000), (-74123667645013173855704274973/175921860444160000000000000000000), (-848100940940396641347600695741/5629499534213120000000000000000000), (11044714051197533133881302911/703687441776640000000000000000000), (23767491512386966279575291111/5629499534213120000000000000000000), (-1689184938413183814490808931/5629499534213120000000000000000000), (-44696669394056376295993697/703687441776640000000000000000000), (19740449792888604171662763/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial160.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial160.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial160.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 500479303415718812084961883230183), (Int.ofNat 281494155544147965383163215526150), (Int.negOfNat 8466080742801584351209509293186), (Int.negOfNat 3257675350623017374545905765936), (Int.ofNat 703638512173352988089498948778), (Int.ofNat 131809720331067053604327881030), (Int.negOfNat 18745789909986272890910051970), (Int.negOfNat 2588177702135102184920590119), (Int.ofNat 277311509965508689831917266), (Int.ofNat 29875688333030576501495609), (Int.negOfNat 2592212290607438697863438), (Int.negOfNat 225586102897706435328822), (Int.ofNat 16546844973720333665367), (Int.ofNat 1195266798507768102661), (Int.negOfNat 76208032615278986804), (Int.negOfNat 4767618273318331534), (Int.ofNat 241826338359153573), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-500479303415718812084961883230183/5629499534213120000000000000000000), (5629883110882959307663264310523/112589990684262400000000000000000), (-4233040371400792175604754646593/2814749767106560000000000000000000), (-203604709413938585909119110371/351843720888320000000000000000000), (351819256086676494044749474389/2814749767106560000000000000000000), (13180972033106705360432788103/562949953421312000000000000000000), (-1874578990998627289091005197/562949953421312000000000000000000), (-2588177702135102184920590119/5629499534213120000000000000000000), (138655754982754344915958633/2814749767106560000000000000000000), (29875688333030576501495609/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial160.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial160.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial160.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 16611639700573454507418448722268), (Int.ofNat 237177691121698915052387230017930), (Int.negOfNat 6218603910526999592409090892718), (Int.ofNat 3805474194995258105015952781453), (Int.ofNat 561423585091333411844474115433), (Int.negOfNat 151673994571537478781493442585), (Int.negOfNat 14716844473148337700434585660), (Int.ofNat 2982532668008440910591727241), (Int.ofNat 213498047139314444757810644), (Int.negOfNat 34724653640348442985999941), (Int.negOfNat 1960148161043467679067912), (Int.ofNat 265156185734399647042738), (Int.ofNat 12337077277846974282713), (Int.negOfNat 1420856749436094424079), (Int.negOfNat 56205604631638051176), (Int.ofNat 5666243536115616066), (Int.ofNat 172334450833624447), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(4152909925143363626854612180567/1407374883553280000000000000000000), (23717769112169891505238723001793/562949953421312000000000000000000), (-3109301955263499796204545446359/2814749767106560000000000000000000), (3805474194995258105015952781453/5629499534213120000000000000000000), (561423585091333411844474115433/5629499534213120000000000000000000), (-30334798914307495756298688517/1125899906842624000000000000000000), (-735842223657416885021729283/281474976710656000000000000000000), (2982532668008440910591727241/5629499534213120000000000000000000), (53374511784828611189452661/1407374883553280000000000000000000), (-34724653640348442985999941/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial160.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial160.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial160.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 500140946025062404459057356902912), (Int.ofNat 262442931193887007459576997272644), (Int.ofNat 16634761229328543020034560267825), (Int.ofNat 1723370198291748456400963290856), (Int.negOfNat 918251607717446700977890777298), (Int.negOfNat 59324114896185390076472724169), (Int.ofNat 25339218877161162892006041739), (Int.ofNat 1058403975637688100280727099), (Int.negOfNat 380938063400002943186418434), (Int.negOfNat 11768216261123361518812067), (Int.ofNat 3571487250266576707062363), (Int.ofNat 89090317852732489725416), (Int.negOfNat 22711663312587164924886), (Int.negOfNat 483733243858162587672), (Int.ofNat 103676844697826733523), (Int.ofNat 2077786946684146480), (Int.negOfNat 352892353253949337), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(976837785205200008709096400201/10995116277760000000000000000000), (65610732798471751864894249318161/1407374883553280000000000000000000), (665390449173141720801382410713/225179981368524800000000000000000), (215421274786468557050120411357/703687441776640000000000000000000), (-459125803858723350488945388649/2814749767106560000000000000000000), (-59324114896185390076472724169/5629499534213120000000000000000000), (25339218877161162892006041739/5629499534213120000000000000000000), (1058403975637688100280727099/5629499534213120000000000000000000), (-190469031700001471593209217/2814749767106560000000000000000000), (-11768216261123361518812067/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial160.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial160.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial160.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1090419802169785665695643154832052), (Int.ofNat 320473256092659832698446537103778), (Int.ofNat 6288885395094869792985934648125), (Int.negOfNat 4038532376459190330729394082708), (Int.negOfNat 120068683971890734889508080754), (Int.ofNat 168349437579138904721499434374), (Int.ofNat 1533316443488983971024680277), (Int.negOfNat 3414275324400288194432759117), (Int.negOfNat 11748275450262868901679733), (Int.ofNat 40495076807581667472078752), (Int.ofNat 92410870739921067341332), (Int.negOfNat 312532404317507271797970), (Int.negOfNat 797375187629517972772), (Int.ofNat 1683186550926283770647), (Int.ofNat 5324780113792045880), (Int.negOfNat 6688127901607101636), (Int.ofNat 25925577305215911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(272604950542446416423910788708013/1407374883553280000000000000000000), (160236628046329916349223268551889/2814749767106560000000000000000000), (10062216632151791668777495437/9007199254740992000000000000000), (-1009633094114797582682348520677/1407374883553280000000000000000000), (-60034341985945367444754040377/2814749767106560000000000000000000), (84174718789569452360749717187/2814749767106560000000000000000000), (1533316443488983971024680277/5629499534213120000000000000000000), (-3414275324400288194432759117/5629499534213120000000000000000000), (-11748275450262868901679733/5629499534213120000000000000000000), (1265471150236927108502461/175921860444160000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial160.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial160.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial160.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 1727357975873727227181975081430916), (Int.ofNat 305635259926264034990922017789679), (Int.negOfNat 9124375926030145452404028375527), (Int.ofNat 253493698058833623453630486915), (Int.ofNat 838088616471984581695165940192), (Int.negOfNat 31711698731413171091409559122), (Int.negOfNat 24369675681361453027523294153), (Int.ofNat 823886452051444385064499317), (Int.ofNat 379975558245857991298514350), (Int.negOfNat 10263445220691758150755884), (Int.negOfNat 3660502069825035966004852), (Int.ofNat 75559193702145322904082), (Int.ofNat 23732767688070584550420), (Int.negOfNat 367419467146734537319), (Int.negOfNat 109869247776854200508), (Int.ofNat 1223132121313662832), (Int.ofNat 329146598906464303), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(431839493968431806795493770357729/1407374883553280000000000000000000), (305635259926264034990922017789679/5629499534213120000000000000000000), (-9124375926030145452404028375527/5629499534213120000000000000000000), (50698739611766724690726097383/1125899906842624000000000000000000), (26190269264749518177973935631/175921860444160000000000000000000), (-15855849365706585545704779561/2814749767106560000000000000000000), (-24369675681361453027523294153/5629499534213120000000000000000000), (823886452051444385064499317/5629499534213120000000000000000000), (7599511164917159825970287/112589990684262400000000000000000), (-2565861305172939537688971/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial160.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial160.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial160.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 2315187901052238760205915697622326), (Int.ofNat 292499812770482516697595363950747), (Int.ofNat 5273793894581895553056678722463), (Int.ofNat 2827157132098531991814244933399), (Int.negOfNat 369569112156556017472657118422), (Int.negOfNat 130508021542582957306542643032), (Int.ofNat 12887323129777459124952191810), (Int.ofNat 2827518811961800647273868100), (Int.negOfNat 209978427904633050627318205), (Int.negOfNat 35401524813312173445696035), (Int.ofNat 1965149688352809887585621), (Int.ofNat 284980260600139070665101), (Int.negOfNat 11882804453236347240686), (Int.negOfNat 1581332866613335446631), (Int.ofNat 50277638618146658555), (Int.ofNat 6403332931904832080), (Int.negOfNat 216270353994894591), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(1157593950526119380102957848811163/2814749767106560000000000000000000), (292499812770482516697595363950747/5629499534213120000000000000000000), (5273793894581895553056678722463/5629499534213120000000000000000000), (2827157132098531991814244933399/5629499534213120000000000000000000), (-184784556078278008736328559211/2814749767106560000000000000000000), (-16313502692822869663317830379/703687441776640000000000000000000), (1288732312977745912495219181/562949953421312000000000000000000), (28275188119618006472738681/56294995342131200000000000000000), (-41995685580926610125463641/1125899906842624000000000000000000), (-7080304962662434689139207/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial160.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial160.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial160.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 2934927963119404690124339699751462), (Int.ofNat 328711434638377451811672453358247), (Int.ofNat 7409706581886610185713771902250), (Int.negOfNat 2230465253907221443564322488705), (Int.negOfNat 451187167474540207852187055195), (Int.ofNat 118828500737758115242788708603), (Int.ofNat 14984416724297093367145621114), (Int.negOfNat 2682237896121092772227055117), (Int.negOfNat 262368980388265297904722413), (Int.ofNat 32516846049937841594671857), (Int.ofNat 2774321189224678915772158), (Int.negOfNat 243051637617325256916947), (Int.negOfNat 19221261273981357687038), (Int.ofNat 1229666166178852082457), (Int.ofNat 93065776274282377166), (Int.negOfNat 4492642678121357704), (Int.negOfNat 305400844558979269), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(1467463981559702345062169849875731/2814749767106560000000000000000000), (328711434638377451811672453358247/5629499534213120000000000000000000), (29638826327546440742855087609/22517998136852480000000000000000), (-446093050781444288712864497741/1125899906842624000000000000000000), (-90237433494908041570437411039/1125899906842624000000000000000000), (118828500737758115242788708603/5629499534213120000000000000000000), (7492208362148546683572810557/2814749767106560000000000000000000), (-2682237896121092772227055117/5629499534213120000000000000000000), (-262368980388265297904722413/5629499534213120000000000000000000), (32516846049937841594671857/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial160.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial160.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial160.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 3601296888256755276037687364645284), (Int.ofNat 328145656317472477406452796132593), (Int.negOfNat 5797784909227337728904697317349), (Int.negOfNat 456122068737076100452820908155), (Int.ofNat 747506256798221991729262507791), (Int.ofNat 35067192861050768168948090854), (Int.negOfNat 25181450318271731026664861149), (Int.negOfNat 1137994291891027305866482466), (Int.ofNat 413150053854685993985249464), (Int.ofNat 18894023708462241570622793), (Int.negOfNat 3908120965349243380106894), (Int.negOfNat 181813294832798398071506), (Int.ofNat 23866409812382490501845), (Int.ofNat 1119313978750183975185), (Int.negOfNat 102329248527732028828), (Int.negOfNat 4865403287169694680), (Int.ofNat 406615130684573271), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(900324222064188819009421841161321/1407374883553280000000000000000000), (328145656317472477406452796132593/5629499534213120000000000000000000), (-5797784909227337728904697317349/5629499534213120000000000000000000), (-91224413747415220090564181631/1125899906842624000000000000000000), (747506256798221991729262507791/5629499534213120000000000000000000), (17533596430525384084474045427/2814749767106560000000000000000000), (-25181450318271731026664861149/5629499534213120000000000000000000), (-568997145945513652933241233/2814749767106560000000000000000000), (51643756731835749248156183/703687441776640000000000000000000), (18894023708462241570622793/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial160.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial160.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial160.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 4242184229889440581634880097153526), (Int.ofNat 321307140938741218831434655136542), (Int.ofNat 6181765306042798459065380397991), (Int.ofNat 3037469875444155586833659150221), (Int.negOfNat 249325080671781940070083183093), (Int.negOfNat 173739372079794166322460259030), (Int.ofNat 3606168353265554649578475182), (Int.ofNat 4158429023435053083666514531), (Int.ofNat 22495337055575736508251599), (Int.negOfNat 52005045785512986296846687), (Int.negOfNat 952482986148331068314230), (Int.ofNat 391163861803876033574472), (Int.ofNat 9638642259100378837100), (Int.negOfNat 1983704224465882337738), (Int.negOfNat 55361206672097758187), (Int.ofNat 7413601841395121756), (Int.ofNat 218206831314934675), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(2121092114944720290817440048576763/2814749767106560000000000000000000), (160653570469370609415717327568271/2814749767106560000000000000000000), (6181765306042798459065380397991/5629499534213120000000000000000000), (3037469875444155586833659150221/5629499534213120000000000000000000), (-249325080671781940070083183093/5629499534213120000000000000000000), (-17373937207979416632246025903/562949953421312000000000000000000), (1803084176632777324789237591/2814749767106560000000000000000000), (4158429023435053083666514531/5629499534213120000000000000000000), (22495337055575736508251599/5629499534213120000000000000000000), (-52005045785512986296846687/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial160.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial160.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial160.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 4925018525043315940231688128473303), (Int.ofNat 363064520589651971215828810438823), (Int.ofNat 7984613051284008248667247551072), (Int.negOfNat 3237895438071156625996257543125), (Int.negOfNat 786296576541679244620524051252), (Int.ofNat 128254308720083974925450044346), (Int.ofNat 32090646867691265007300907832), (Int.negOfNat 1804373811002574781530323181), (Int.negOfNat 578216900377223345163814491), (Int.ofNat 8255163620218010729112237), (Int.ofNat 5532441382184995177769830), (Int.ofNat 14808520727462244036308), (Int.negOfNat 33635454121543823886820), (Int.negOfNat 361505807632525005982), (Int.ofNat 143526089886270753313), (Int.ofNat 2202971337874786884), (Int.negOfNat 517681145579369035), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(4925018525043315940231688128473303/5629499534213120000000000000000000), (363064520589651971215828810438823/5629499534213120000000000000000000), (249519157852625257770851485971/175921860444160000000000000000000), (-5180632700913850601594012069/9007199254740992000000000000000), (-196574144135419811155131012813/1407374883553280000000000000000000), (64127154360041987462725022173/2814749767106560000000000000000000), (4011330858461408125912613479/703687441776640000000000000000000), (-1804373811002574781530323181/5629499534213120000000000000000000), (-578216900377223345163814491/5629499534213120000000000000000000), (8255163620218010729112237/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial160.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial160.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial160.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 5650390849452680311141349750902134), (Int.ofNat 346054716084211297154458428077765), (Int.negOfNat 14500567336132717548278303089476), (Int.negOfNat 1184008269199034777024897335003), (Int.ofNat 1372879250390886843962379043524), (Int.ofNat 161048168788913518526237502730), (Int.negOfNat 35531791623868529858038268809), (Int.negOfNat 5305993112868742913804927514), (Int.ofNat 332329271857952082631955504), (Int.ofNat 68036186166713418086289077), (Int.negOfNat 1580931532263025607709774), (Int.negOfNat 505230694068647123609794), (Int.ofNat 3585453815511536436385), (Int.ofNat 2531572455499585410215), (Int.ofNat 2548620170774832992), (Int.negOfNat 9446537874723584240), (Int.negOfNat 75479810623492199), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(2825195424726340155570674875451067/2814749767106560000000000000000000), (69210943216842259430891685615553/1125899906842624000000000000000000), (-3625141834033179387069575772369/1407374883553280000000000000000000), (-1184008269199034777024897335003/5629499534213120000000000000000000), (343219812597721710990594760881/1407374883553280000000000000000000), (16104816878891351852623750273/562949953421312000000000000000000), (-35531791623868529858038268809/5629499534213120000000000000000000), (-2652996556434371456902463757/2814749767106560000000000000000000), (20770579491122005164497219/351843720888320000000000000000000), (68036186166713418086289077/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial160.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial160.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial160.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 6299309646138764585541884795096069), (Int.ofNat 321944644267704329356196838730185), (Int.ofNat 13012325954048785386487571562883), (Int.ofNat 8501311922864148526630345464646), (Int.negOfNat 28924997043462701347672450080), (Int.negOfNat 451508007527812599691672710159), (Int.negOfNat 38909437617908706996576046896), (Int.ofNat 5978029689884161766892536467), (Int.ofNat 731131847915045887724867737), (Int.negOfNat 42193834260687238108703977), (Int.negOfNat 6771737106619993628523752), (Int.ofNat 188472601864154403056077), (Int.ofNat 40113982767020572320022), (Int.negOfNat 568145872334767089377), (Int.negOfNat 169085483717196359734), (Int.ofNat 1094195694992248784), (Int.ofNat 557383650128443561), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(6299309646138764585541884795096069/5629499534213120000000000000000000), (64388928853540865871239367746037/1125899906842624000000000000000000), (13012325954048785386487571562883/5629499534213120000000000000000000), (4250655961432074263315172732323/2814749767106560000000000000000000), (-180781231521641883422952813/35184372088832000000000000000000), (-451508007527812599691672710159/5629499534213120000000000000000000), (-2431839851119294187286002931/351843720888320000000000000000000), (5978029689884161766892536467/5629499534213120000000000000000000), (731131847915045887724867737/5629499534213120000000000000000000), (-42193834260687238108703977/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial160.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial160.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial160.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 7046781836674159177994232355410351), (Int.ofNat 434790848794226044329420053753290), (Int.ofNat 22929943347488955224847690650624), (Int.negOfNat 11676689578987240529158828842873), (Int.negOfNat 4634322628334584505765357098707), (Int.negOfNat 219102446196026692821873716562), (Int.ofNat 80473626351014516454683488852), (Int.ofNat 6979494845113027323452513350), (Int.negOfNat 733995921786287226569893515), (Int.negOfNat 81768511206317336161195565), (Int.ofNat 4327903720876937732549171), (Int.ofNat 576022738947113514671629), (Int.negOfNat 18087509628716889956746), (Int.negOfNat 2802028866839016724409), (Int.ofNat 56682668679691310975), (Int.ofNat 10192942374542553840), (Int.negOfNat 114864966066186481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(7046781836674159177994232355410351/5629499534213120000000000000000000), (43479084879422604432942005375329/562949953421312000000000000000000), (22392522800282182836765322901/5497558138880000000000000000000), (-11676689578987240529158828842873/5629499534213120000000000000000000), (-4634322628334584505765357098707/5629499534213120000000000000000000), (-109551223098013346410936858281/2814749767106560000000000000000000), (20118406587753629113670872213/1407374883553280000000000000000000), (139589896902260546469050267/112589990684262400000000000000000), (-146799184357257445313978703/1125899906842624000000000000000000), (-16353702241263467232239113/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial160.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial160.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial160.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 7839328785356829695615084045465736), (Int.ofNat 238229633257365330244419042888914), (Int.negOfNat 153505914396988210025219671172031), (Int.negOfNat 42397969394918856653756585234467), (Int.negOfNat 1115171865320396005782574006973), (Int.ofNat 888445572195685504881891874596), (Int.ofNat 62470774880488107730617144575), (Int.negOfNat 10068881675053479722428957867), (Int.negOfNat 906690453301096542381811960), (Int.ofNat 74122689544675881126669154), (Int.ofNat 7556483125530836646158398), (Int.negOfNat 386267427107809563221232), (Int.negOfNat 42480492887483303491300), (Int.ofNat 1506100457658089274239), (Int.ofNat 173909773351915316232), (Int.negOfNat 4423304063426748152), (Int.negOfNat 533637895780958527), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(979916098169603711951885505683217/703687441776640000000000000000000), (119114816628682665122209521444457/2814749767106560000000000000000000), (-153505914396988210025219671172031/5629499534213120000000000000000000), (-42397969394918856653756585234467/5629499534213120000000000000000000), (-1115171865320396005782574006973/5629499534213120000000000000000000), (222111393048921376220472968649/1407374883553280000000000000000000), (2498830995219524309224685783/225179981368524800000000000000000), (-10068881675053479722428957867/5629499534213120000000000000000000), (-22667261332527413559545299/140737488355328000000000000000000), (37061344772337940563334577/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial160.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial160.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial160.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 7375690086155149524560324419760982), (Int.negOfNat 842420260520711272326675293743645), (Int.negOfNat 356565141355165005009545577845561), (Int.negOfNat 12555550415923753396388010463639), (Int.ofNat 8062185942757018482831148413289), (Int.ofNat 581406532087307192840921155237), (Int.negOfNat 112616695559983693713661446273), (Int.negOfNat 9532782955623747615138402413), (Int.ofNat 1031447763290323646694687597), (Int.ofNat 91716358428311482698182088), (Int.negOfNat 6601994596867224776185628), (Int.negOfNat 591688394942444096964290), (Int.ofNat 31087344399372991488628), (Int.ofNat 2749438285399539379513), (Int.negOfNat 111869822413366433580), (Int.negOfNat 9654551193532008884), (Int.ofNat 305209742755865161), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(3687845043077574762280162209880491/2814749767106560000000000000000000), (-168484052104142254465335058748729/1125899906842624000000000000000000), (-356565141355165005009545577845561/5629499534213120000000000000000000), (-12555550415923753396388010463639/5629499534213120000000000000000000), (8062185942757018482831148413289/5629499534213120000000000000000000), (581406532087307192840921155237/5629499534213120000000000000000000), (-112616695559983693713661446273/5629499534213120000000000000000000), (-9532782955623747615138402413/5629499534213120000000000000000000), (1031447763290323646694687597/5629499534213120000000000000000000), (11464544803538935337272761/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial160.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial160.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial160.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 4303620100659552012753258652832033), (Int.negOfNat 2139510105088670949970792408167041), (Int.negOfNat 223146738304251117871189513660797), (Int.ofNat 54060397935976073544582222265553), (Int.ofNat 5866175570443990212557796894969), (Int.negOfNat 990575835128110411647229974891), (Int.negOfNat 97515575540549280306395976991), (Int.ofNat 11742615044463217186389174811), (Int.ofNat 1044276274095571077676700966), (Int.negOfNat 93982860278977317708428073), (Int.negOfNat 7623525707807163983909577), (Int.ofNat 536885333740113602315704), (Int.ofNat 40003306843150130380974), (Int.negOfNat 2288846391903692772568), (Int.negOfNat 157661345145297995537), (Int.ofNat 7467210885084894840), (Int.ofNat 509892141433473493), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(4303620100659552012753258652832033/5629499534213120000000000000000000), (-2139510105088670949970792408167041/5629499534213120000000000000000000), (-223146738304251117871189513660797/5629499534213120000000000000000000), (54060397935976073544582222265553/5629499534213120000000000000000000), (5866175570443990212557796894969/5629499534213120000000000000000000), (-990575835128110411647229974891/5629499534213120000000000000000000), (-97515575540549280306395976991/5629499534213120000000000000000000), (11742615044463217186389174811/5629499534213120000000000000000000), (522138137047785538838350483/2814749767106560000000000000000000), (-93982860278977317708428073/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial160.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial160.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial160.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 377868787597817604369866847681962), (Int.negOfNat 2287542367892482131516487104273571), (Int.ofNat 148612947737233966492573890092337), (Int.ofNat 53615547659066934684243844638592), (Int.negOfNat 5887622541609539756681916948000), (Int.negOfNat 938451443825565192620360967085), (Int.ofNat 104770300318249958963590362208), (Int.ofNat 11141756639826914031323188819), (Int.negOfNat 1111155733058831212138945486), (Int.negOfNat 91232038774305902537636669), (Int.ofNat 7901405338800127395508558), (Int.ofNat 536834839500297166630032), (Int.negOfNat 40334382687785058361867), (Int.negOfNat 2357362338543913652521), (Int.ofNat 155146236348718365484), (Int.ofNat 7884908991852836654), (Int.negOfNat 487639267996382163), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-188934393798908802184933423840981/2814749767106560000000000000000000), (-2287542367892482131516487104273571/5629499534213120000000000000000000), (148612947737233966492573890092337/5629499534213120000000000000000000), (418871466086460427220655036239/43980465111040000000000000000000), (-1471905635402384939170479237/1407374883553280000000000000000), (-187690288765113038524072193417/1125899906842624000000000000000000), (3274071884945311217612198819/175921860444160000000000000000000), (11141756639826914031323188819/5629499534213120000000000000000000), (-555577866529415606069472743/2814749767106560000000000000000000), (-91232038774305902537636669/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial160.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial160.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial160.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial160.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial160.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial160.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial160.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial160.reflect := by
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

end Bin160
end
end ErdosOverlap.OuterNumerics
