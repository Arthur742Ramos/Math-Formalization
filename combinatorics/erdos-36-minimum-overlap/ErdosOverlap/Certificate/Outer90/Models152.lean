/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.IntegerOuterBindings
public import ErdosOverlap.Numerics.OuterTruncation
public import ErdosOverlap.Certificate.OuterData12
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

/-! # Exact integer weighted outer models for source bin 152

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin152

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 2140265121190715600)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 2149545558216032000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 2042325421464058500)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 1478523347974583200)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 929466610217185700)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 601372048901455700)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 331085053309506240)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 125156929617364400)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial152.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial152.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9580097493255600000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 2590802931775610400)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1583069383657120200)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 992108641887464400)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 461951329484759200)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 256908221110919700)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 69771009168521384)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 22762233661944805)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 20754271048333680)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial152.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial152.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9580097493255600000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 2590802931775610400)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1583069383657120200)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 992108641887464400)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 461951329484759200)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 256908221110919700)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 69771009168521384)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 22762233661944805)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 20754271048333680)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial152.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial152.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial152.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 6963664319676325986909787805377927), (Int.ofNat 4913591435516371558380540224833959), (Int.ofNat 716447438569583486753825512008146), (Int.negOfNat 150952063267025396331207264362275), (Int.negOfNat 18860771446462778204437774640354), (Int.ofNat 2859616302218643619570641423729), (Int.ofNat 270768973212321763633162546829), (Int.negOfNat 33972561404312704905575116667), (Int.negOfNat 2501109777825420020058596076), (Int.ofNat 272492507478657626526024515), (Int.ofNat 16090138186797157180779110), (Int.negOfNat 1562406195511559004017388), (Int.negOfNat 76013779213346008947136), (Int.ofNat 6689126197358241855744), (Int.ofNat 273925846312084648838), (Int.negOfNat 21784276426997431288), (Int.negOfNat 809581841444381355), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-6963664319676325986909787805377927/11258999068426240000000000000000000), (4913591435516371558380540224833959/11258999068426240000000000000000000), (358223719284791743376912756004073/5629499534213120000000000000000000), (-6038082530681015853248290574491/450359962737049600000000000000000), (-9430385723231389102218887320177/5629499534213120000000000000000000), (2859616302218643619570641423729/11258999068426240000000000000000000), (270768973212321763633162546829/11258999068426240000000000000000000), (-33972561404312704905575116667/11258999068426240000000000000000000), (-625277444456355005014649019/2814749767106560000000000000000000), (54498501495731525305204903/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial152.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial152.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial152.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial152 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 4323920160180504910658760102680535), (Int.ofNat 5628078966493843079198879537138496), (Int.negOfNat 374088128200453800546083069036352), (Int.negOfNat 165997544589409010716539229304668), (Int.ofNat 14909946255008413776610263362115), (Int.ofNat 2762256017545090369236482271027), (Int.negOfNat 273768373559284045978120130723), (Int.negOfNat 28665444603053630498816570509), (Int.ofNat 2943789347359880749051582664), (Int.ofNat 203048209114740590730700793), (Int.negOfNat 21018906299453127826950098), (Int.negOfNat 1042337431906963953446008), (Int.ofNat 107272546994183226375948), (Int.ofNat 4050064728735290345040), (Int.negOfNat 411771470362675754470), (Int.negOfNat 12082638563039077956), (Int.ofNat 1312962878486336565), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(864784032036100982131752020536107/2251799813685248000000000000000000), (87938733851466298112482492767789/175921860444160000000000000000000), (-5845127003132090633532547953693/175921860444160000000000000000000), (-41499386147352252679134807326167/2814749767106560000000000000000000), (2981989251001682755322052672423/2251799813685248000000000000000000), (2762256017545090369236482271027/11258999068426240000000000000000000), (-273768373559284045978120130723/11258999068426240000000000000000000), (-28665444603053630498816570509/11258999068426240000000000000000000), (367973668419985093631447833/1407374883553280000000000000000000), (203048209114740590730700793/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial152.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial152.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial152.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial152 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 13062340581683215541415392714076881), (Int.ofNat 2775814741485359421659326601027514), (Int.negOfNat 870274630291010505742051395241573), (Int.ofNat 9929602366892719048295673592350), (Int.ofNat 21883921823013588894909182538694), (Int.negOfNat 1391253536312647287454514877273), (Int.negOfNat 288068841016734551246737149349), (Int.ofNat 24962713097182881097500866095), (Int.ofNat 2370910896482755179946186640), (Int.negOfNat 239881501016778585213862347), (Int.negOfNat 13461733085655269422210450), (Int.ofNat 1512464500384486766191076), (Int.ofNat 56096187697403562042876), (Int.negOfNat 6842636086619344827336), (Int.negOfNat 178854348505631069070), (Int.ofNat 23426902159475257692), (Int.ofNat 413356781543954475), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(13062340581683215541415392714076881/11258999068426240000000000000000000), (1387907370742679710829663300513757/5629499534213120000000000000000000), (-870274630291010505742051395241573/11258999068426240000000000000000000), (198592047337854380965913471847/225179981368524800000000000000000), (10941960911506794447454591269347/5629499534213120000000000000000000), (-1391253536312647287454514877273/11258999068426240000000000000000000), (-288068841016734551246737149349/11258999068426240000000000000000000), (4992542619436576219500173219/2251799813685248000000000000000000), (29636386206034439749327333/140737488355328000000000000000000), (-239881501016778585213862347/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial152.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial152.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial152.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial152 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 15503163438027398176313121525172678), (Int.negOfNat 39445020095317049352659159106963), (Int.negOfNat 446111291550344385115384632543177), (Int.ofNat 100059350111702297904941266152663), (Int.negOfNat 747518030685728203352874466871), (Int.negOfNat 2233156500520025917280830661303), (Int.ofNat 144618309452806860636228634955), (Int.ofNat 24048338853258659849901953305), (Int.negOfNat 2225604174814638201995834476), (Int.negOfNat 159641868004217036549952961), (Int.ofNat 18418064387396230605781714), (Int.ofNat 725955068566281237967720), (Int.negOfNat 101254237216876114013504), (Int.negOfNat 2403162515434112893540), (Int.ofNat 404184389482162719598), (Int.ofNat 5583249025614374140), (Int.negOfNat 1250700065341335525), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(7751581719013699088156560762586339/5629499534213120000000000000000000), (-39445020095317049352659159106963/11258999068426240000000000000000000), (-446111291550344385115384632543177/11258999068426240000000000000000000), (100059350111702297904941266152663/11258999068426240000000000000000000), (-747518030685728203352874466871/11258999068426240000000000000000000), (-2233156500520025917280830661303/11258999068426240000000000000000000), (28923661890561372127245726991/2251799813685248000000000000000000), (4809667770651731969980390661/2251799813685248000000000000000000), (-556401043703659550498958619/2814749767106560000000000000000000), (-159641868004217036549952961/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial152.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial152.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial152.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial152 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 14368583923070924362722627433117072), (Int.negOfNat 789757635794191176145279721674995), (Int.ofNat 4022367428890081053050718334040), (Int.ofNat 36814191671798017965982140832719), (Int.negOfNat 10539887511722774049303834118903), (Int.ofNat 362768908534098590258577510317), (Int.ofNat 191165905970722489984507537973), (Int.negOfNat 15685125210917595649551095079), (Int.negOfNat 1647930738647661388498223768), (Int.ofNat 188762732304168885999671011), (Int.ofNat 8586438127524402773803254), (Int.negOfNat 1314761466512573883397708), (Int.negOfNat 29446739945040946007304), (Int.ofNat 6260763557684953713088), (Int.ofNat 67149717693347419778), (Int.negOfNat 22372092664147272632), (Int.negOfNat 37885992691861275), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(898036495191932772670164214569817/703687441776640000000000000000000), (-157951527158838235229055944334999/2251799813685248000000000000000000), (100559185722252026326267958351/281474976710656000000000000000000), (36814191671798017965982140832719/11258999068426240000000000000000000), (-10539887511722774049303834118903/11258999068426240000000000000000000), (362768908534098590258577510317/11258999068426240000000000000000000), (191165905970722489984507537973/11258999068426240000000000000000000), (-15685125210917595649551095079/11258999068426240000000000000000000), (-205991342330957673562277971/1407374883553280000000000000000000), (188762732304168885999671011/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial152.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial152.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial152.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial152 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 12952549788592123734319316369269436), (Int.negOfNat 611699642553143489865650932989818), (Int.ofNat 34288778065391467038115584285410), (Int.negOfNat 13054702796169674108975938710393), (Int.negOfNat 860236081268504991955895553952), (Int.ofNat 1010927247863087703029999869379), (Int.negOfNat 77102948706550407009011580871), (Int.negOfNat 13634079893943698554923853021), (Int.ofNat 1579661897624155311365475124), (Int.ofNat 88508391959143167168232985), (Int.negOfNat 14733367981565447684626194), (Int.negOfNat 321394662795867465079696), (Int.ofNat 86035554546542621143996), (Int.ofNat 558260305298595062500), (Int.negOfNat 354986226648454937870), (Int.ofNat 751368950078384876), (Int.ofNat 1188437252196334485), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(3238137447148030933579829092317359/2814749767106560000000000000000000), (-305849821276571744932825466494909/5629499534213120000000000000000000), (3428877806539146703811558428541/1125899906842624000000000000000000), (-13054702796169674108975938710393/11258999068426240000000000000000000), (-26882377539640780998621736061/351843720888320000000000000000000), (1010927247863087703029999869379/11258999068426240000000000000000000), (-77102948706550407009011580871/11258999068426240000000000000000000), (-13634079893943698554923853021/11258999068426240000000000000000000), (394915474406038827841368781/2814749767106560000000000000000000), (17701678391828633433646597/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial152.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial152.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial152.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial152 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 11774208452880484761697186580123778), (Int.negOfNat 597021626288432513008496861293704), (Int.negOfNat 8412138014705592555893349054218), (Int.ofNat 3605233173332905258454277045775), (Int.ofNat 2730565053251466006109597162683), (Int.negOfNat 293208532268949428374460234993), (Int.negOfNat 80887906442463431489049397265), (Int.ofNat 10637865245921608280691781599), (Int.ofNat 736720687815971714497986524), (Int.negOfNat 140079635358410770096285339), (Int.negOfNat 2917478274196133603060538), (Int.ofNat 1036121911174342600026972), (Int.ofNat 1407235201872049125320), (Int.negOfNat 5104482053420174787904), (Int.ofNat 43834325369877318102), (Int.ofNat 18855653118568666932), (Int.negOfNat 337584796160231925), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(5887104226440242380848593290061889/5629499534213120000000000000000000), (-74627703286054064126062107661713/1407374883553280000000000000000000), (-4206069007352796277946674527109/5629499534213120000000000000000000), (144209326933316210338171081831/450359962737049600000000000000000), (2730565053251466006109597162683/11258999068426240000000000000000000), (-293208532268949428374460234993/11258999068426240000000000000000000), (-16177581288492686297809879453/2251799813685248000000000000000000), (10637865245921608280691781599/11258999068426240000000000000000000), (184180171953992928624496631/2814749767106560000000000000000000), (-140079635358410770096285339/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial152.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial152.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial152.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial152 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 10605965681625619406027244210498385), (Int.negOfNat 533822531608107648893979355226921), (Int.ofNat 43701282821248167470824301479132), (Int.ofNat 7301368729400663985286714573492), (Int.negOfNat 1812909097274448436787719864720), (Int.negOfNat 316964924789600422883731122552), (Int.ofNat 60975559911799193908564678611), (Int.ofNat 4445633977812660505601358165), (Int.negOfNat 1119304565897866857611821912), (Int.negOfNat 18433532807326929039427089), (Int.ofNat 10776352549228613049988062), (Int.negOfNat 67814530213128483315332), (Int.negOfNat 64789257613215869389528), (Int.ofNat 1125833493999988344060), (Int.ofNat 270315699146362600278), (Int.negOfNat 6521331976001739592), (Int.negOfNat 1001017509433969045), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(2121193136325123881205448842099677/2251799813685248000000000000000000), (-533822531608107648893979355226921/11258999068426240000000000000000000), (10925320705312041867706075369783/2814749767106560000000000000000000), (1825342182350165996321678643373/2814749767106560000000000000000000), (-22661363715930605459846498309/140737488355328000000000000000000), (-39620615598700052860466390319/1407374883553280000000000000000000), (60975559911799193908564678611/11258999068426240000000000000000000), (889126795562532101120271633/2251799813685248000000000000000000), (-139913070737233357201477739/1407374883553280000000000000000000), (-18433532807326929039427089/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial152.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial152.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial152.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial152 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 9736573417551870347446970849795135), (Int.negOfNat 342208040019864567383187112433397), (Int.ofNat 34291476871581302316857191274553), (Int.negOfNat 9583870042545725414154112735766), (Int.negOfNat 1272766188057543254415526774348), (Int.ofNat 328514419873895981418691839957), (Int.ofNat 17272895110795799140830234381), (Int.negOfNat 7544487862264904298094931395), (Int.negOfNat 23161783276896035852722832), (Int.ofNat 95316986570624783598317679), (Int.negOfNat 1866941546141548572306998), (Int.negOfNat 713617222237032023911668), (Int.ofNat 21901621160854107070712), (Int.ofNat 3553054624667839934260), (Int.negOfNat 131827585298926963022), (Int.negOfNat 13078249340526619368), (Int.ofNat 546390113298293365), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(1947314683510374069489394169959027/2251799813685248000000000000000000), (-342208040019864567383187112433397/11258999068426240000000000000000000), (34291476871581302316857191274553/11258999068426240000000000000000000), (-4791935021272862707077056367883/5629499534213120000000000000000000), (-318191547014385813603881693587/2814749767106560000000000000000000), (328514419873895981418691839957/11258999068426240000000000000000000), (17272895110795799140830234381/11258999068426240000000000000000000), (-1508897572452980859618986279/2251799813685248000000000000000000), (-1447611454806002240795177/703687441776640000000000000000000), (95316986570624783598317679/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial152.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial152.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial152.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial152 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 9102979873853588333685788982902869), (Int.negOfNat 334380466874849470613760763237487), (Int.negOfNat 28043278195367919728500533857503), (Int.negOfNat 7671185368549671809857579557623), (Int.ofNat 1243347346499119199272420382393), (Int.ofNat 50901957039288306584323970868), (Int.negOfNat 41767145892316733515478471895), (Int.ofNat 1120600981012868753976444831), (Int.ofNat 700628207336424881282011204), (Int.negOfNat 31388816289456616073206451), (Int.negOfNat 6650629629636169244478598), (Int.ofNat 352637129649790475613828), (Int.ofNat 39953468781295622903960), (Int.negOfNat 2327905097726863605416), (Int.negOfNat 166297841327096416998), (Int.ofNat 10457343509743382628), (Int.ofNat 709195108102572885), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(9102979873853588333685788982902869/11258999068426240000000000000000000), (-334380466874849470613760763237487/11258999068426240000000000000000000), (-28043278195367919728500533857503/11258999068426240000000000000000000), (-7671185368549671809857579557623/11258999068426240000000000000000000), (1243347346499119199272420382393/11258999068426240000000000000000000), (12725489259822076646080992717/2814749767106560000000000000000000), (-8353429178463346703095694379/2251799813685248000000000000000000), (1120600981012868753976444831/11258999068426240000000000000000000), (175157051834106220320502801/2814749767106560000000000000000000), (-31388816289456616073206451/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial152.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial152.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial152.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial152 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 8279826448063714013898986070764503), (Int.negOfNat 501649909192862814250234762585286), (Int.negOfNat 48382491396669644898136674024879), (Int.negOfNat 740297929022277549844626534343), (Int.ofNat 147833650911548955013018685329), (Int.negOfNat 145627204922683803407419381493), (Int.ofNat 15918942039750485006714669959), (Int.ofNat 3991156096622477716393025051), (Int.negOfNat 397662686933309730093728156), (Int.negOfNat 49958837600158573566913575), (Int.ofNat 4828054343872240355518266), (Int.ofNat 368518540976439708845096), (Int.negOfNat 36048379501681308883044), (Int.negOfNat 1795426206711954457620), (Int.ofNat 183034891578218720030), (Int.ofNat 6131030743849537884), (Int.negOfNat 609284229770656725), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(8279826448063714013898986070764503/11258999068426240000000000000000000), (-250824954596431407125117381292643/5629499534213120000000000000000000), (-48382491396669644898136674024879/11258999068426240000000000000000000), (-740297929022277549844626534343/11258999068426240000000000000000000), (147833650911548955013018685329/11258999068426240000000000000000000), (-145627204922683803407419381493/11258999068426240000000000000000000), (15918942039750485006714669959/11258999068426240000000000000000000), (3991156096622477716393025051/11258999068426240000000000000000000), (-99415671733327432523432039/2814749767106560000000000000000000), (-1998353504006342942676543/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial152.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial152.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial152.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial152 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 7076187387659084079424484861749368), (Int.negOfNat 706632875217800754115858191710924), (Int.negOfNat 55303320979664780569917950738923), (Int.negOfNat 1496545667058617748156257747222), (Int.ofNat 192834848779508079583768409802), (Int.ofNat 147571062098008161634554487428), (Int.ofNat 12979363516233053010282369803), (Int.negOfNat 4009316184851479722358843751), (Int.negOfNat 263004342292257775613554248), (Int.ofNat 56340214848504005278415579), (Int.ofNat 2469428147433927896188914), (Int.negOfNat 487955150826380239422692), (Int.negOfNat 14024966637656141109544), (Int.ofNat 2844610299557040363032), (Int.ofNat 53152037383984510478), (Int.negOfNat 11898355950488620328), (Int.negOfNat 333724319250479685), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(884523423457385509928060607718671/1407374883553280000000000000000000), (-176658218804450188528964547927731/2814749767106560000000000000000000), (-55303320979664780569917950738923/11258999068426240000000000000000000), (-748272833529308874078128873611/5629499534213120000000000000000000), (96417424389754039791884204901/5629499534213120000000000000000000), (36892765524502040408638621857/2814749767106560000000000000000000), (12979363516233053010282369803/11258999068426240000000000000000000), (-4009316184851479722358843751/11258999068426240000000000000000000), (-32875542786532221951694281/1407374883553280000000000000000000), (56340214848504005278415579/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial152.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial152.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial152.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial152 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 5437824119124639620342333474828442), (Int.negOfNat 927264994250812858295005553915491), (Int.negOfNat 47625551557271487569316542888174), (Int.ofNat 5628628325944868424406894038424), (Int.ofNat 1269161377822774647796151987919), (Int.negOfNat 32683827702084310287689674167), (Int.negOfNat 33857464035156171951235249755), (Int.negOfNat 349258061207369082627486535), (Int.ofNat 558107872096323282112243804), (Int.ofNat 5885711703163571986469351), (Int.negOfNat 5725718181964293950484346), (Int.negOfNat 31900489393975341783120), (Int.ofNat 39089637026329933211536), (Int.ofNat 47783791184791960260), (Int.negOfNat 187700160653770982302), (Int.ofNat 550671960663600700), (Int.ofNat 547021416625655685), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(2718912059562319810171166737414221/5629499534213120000000000000000000), (-927264994250812858295005553915491/11258999068426240000000000000000000), (-23812775778635743784658271444087/5629499534213120000000000000000000), (703578540743108553050861754803/1407374883553280000000000000000000), (1269161377822774647796151987919/11258999068426240000000000000000000), (-32683827702084310287689674167/11258999068426240000000000000000000), (-6771492807031234390247049951/2251799813685248000000000000000000), (-69851612241473816525497307/2251799813685248000000000000000000), (139526968024080820528060951/2814749767106560000000000000000000), (5885711703163571986469351/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial152.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial152.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial152.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial152 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 3455010185919468840254853072728714), (Int.negOfNat 1018325973305881511970260840186569), (Int.ofNat 6593865169603425994560089571036), (Int.ofNat 9808543795097098289315413706108), (Int.negOfNat 611622815600333042609624016706), (Int.negOfNat 249736571987086178996206159672), (Int.ofNat 10189498431679794665149547221), (Int.ofNat 4680350511739660723977021735), (Int.negOfNat 130959213747589016225113480), (Int.negOfNat 57336231064887605447133643), (Int.ofNat 1336725670234153416150890), (Int.ofNat 465254803213145511869324), (Int.negOfNat 9896221684003170058884), (Int.negOfNat 2620089478161337428384), (Int.ofNat 52197154538221266030), (Int.ofNat 10794721256789902668), (Int.negOfNat 41746469601613515), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(1727505092959734420127426536364357/5629499534213120000000000000000000), (-1018325973305881511970260840186569/11258999068426240000000000000000000), (1648466292400856498640022392759/2814749767106560000000000000000000), (2452135948774274572328853426527/2814749767106560000000000000000000), (-305811407800166521304812008353/5629499534213120000000000000000000), (-31217071498385772374525769959/1407374883553280000000000000000000), (10189498431679794665149547221/11258999068426240000000000000000000), (936070102347932144795404347/2251799813685248000000000000000000), (-3273980343689725405627837/281474976710656000000000000000000), (-57336231064887605447133643/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial152.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial152.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial152.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial152 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 1506615106891058364014626840305728), (Int.negOfNat 910000156684960623475306571970456), (Int.ofNat 35906487021678849800198234968079), (Int.negOfNat 1327143822175577414314918433506), (Int.negOfNat 1529488093581346797953827737742), (Int.ofNat 114180991730033715976458217859), (Int.ofNat 32791432884308274836773450907), (Int.negOfNat 2431231611237937326377532861), (Int.negOfNat 476665605837725229035199016), (Int.ofNat 30680674008023956766664017), (Int.ofNat 4659960057169085405006562), (Int.negOfNat 253500571271578171238992), (Int.negOfNat 31213098958541155912092), (Int.ofNat 1457547709983853807640), (Int.ofNat 148821255814706979030), (Int.negOfNat 6566975384975336884), (Int.negOfNat 484758603480654645), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(23540861045172786937728544379777/175921860444160000000000000000000), (-113750019585620077934413321496307/1407374883553280000000000000000000), (35906487021678849800198234968079/11258999068426240000000000000000000), (-663571911087788707157459216753/5629499534213120000000000000000000), (-764744046790673398976913868871/5629499534213120000000000000000000), (114180991730033715976458217859/11258999068426240000000000000000000), (32791432884308274836773450907/11258999068426240000000000000000000), (-2431231611237937326377532861/11258999068426240000000000000000000), (-59583200729715653629399877/1407374883553280000000000000000000), (30680674008023956766664017/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial152.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial152.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial152.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial152 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 199509151625860875506347314033788), (Int.negOfNat 817299398613923678685580704115650), (Int.ofNat 5938454183033869751377799708199), (Int.negOfNat 5742036881228706980983473323373), (Int.ofNat 537534706993377617187973434445), (Int.ofNat 179289294459033180857532870632), (Int.negOfNat 23535506217155766548054088941), (Int.negOfNat 3082876936054104380820936963), (Int.ofNat 414794386695727353375054644), (Int.ofNat 36831563006594441323272675), (Int.negOfNat 4228801703762827443240030), (Int.negOfNat 300714811937870890894412), (Int.ofNat 28478183262404098107424), (Int.ofNat 1720902722261042868776), (Int.negOfNat 134903464306260909662), (Int.negOfNat 7382244606202420472), (Int.ofNat 396462987405373035), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-49877287906465218876586828508447/2814749767106560000000000000000000), (-16345987972278473573711614082313/225179981368524800000000000000000), (5938454183033869751377799708199/11258999068426240000000000000000000), (-5742036881228706980983473323373/11258999068426240000000000000000000), (107506941398675523437594686889/2251799813685248000000000000000000), (22411161807379147607191608829/1407374883553280000000000000000000), (-23535506217155766548054088941/11258999068426240000000000000000000), (-3082876936054104380820936963/11258999068426240000000000000000000), (103698596673931838343763661/2814749767106560000000000000000000), (1473262520263777652930907/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial152.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial152.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial152.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial152 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 1843733267817492215316604715153014), (Int.negOfNat 836320371357325661563901804965489), (Int.negOfNat 8132014482686950391008692684233), (Int.ofNat 1104980783676479700213334635487), (Int.ofNat 602711561210975884749425558758), (Int.negOfNat 141714040958330536801194223439), (Int.negOfNat 12199406671908328207071457419), (Int.ofNat 4052309391304810121781456597), (Int.ofNat 185735360622212802109598916), (Int.negOfNat 54314349464073306560510005), (Int.negOfNat 1973473072284455158731290), (Int.ofNat 445758590758350494636788), (Int.ofNat 14311894983725261292656), (Int.negOfNat 2498106880077258037464), (Int.negOfNat 73286954704417900138), (Int.ofNat 10461163243910997848), (Int.ofNat 192936202149258485), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-921866633908746107658302357576507/5629499534213120000000000000000000), (-836320371357325661563901804965489/11258999068426240000000000000000000), (-8132014482686950391008692684233/11258999068426240000000000000000000), (1104980783676479700213334635487/11258999068426240000000000000000000), (301355780605487942374712779379/5629499534213120000000000000000000), (-141714040958330536801194223439/11258999068426240000000000000000000), (-12199406671908328207071457419/11258999068426240000000000000000000), (4052309391304810121781456597/11258999068426240000000000000000000), (46433840155553200527399729/2814749767106560000000000000000000), (-10862869892814661312102001/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial152.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial152.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial152.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial152 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 3535197084265181138874115962070093), (Int.negOfNat 848105682178265019710626293863367), (Int.ofNat 1494044139940365952933897660363), (Int.ofNat 605705682511908862342995409642), (Int.negOfNat 429559199989303938095027179097), (Int.ofNat 23850622326331428405107650068), (Int.ofNat 29064177355798547513198140053), (Int.negOfNat 264156998004026273150485901), (Int.negOfNat 553453928455225889825856944), (Int.negOfNat 334284561645876661682063), (Int.ofNat 5760737237679493456699358), (Int.ofNat 31073633583688396722608), (Int.negOfNat 38852782000584038104988), (Int.negOfNat 314867947112673134800), (Int.ofNat 184557754461732648570), (Int.ofNat 2216308334317112036), (Int.negOfNat 605268304543434475), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-3535197084265181138874115962070093/11258999068426240000000000000000000), (-848105682178265019710626293863367/11258999068426240000000000000000000), (1494044139940365952933897660363/11258999068426240000000000000000000), (302852841255954431171497704821/5629499534213120000000000000000000), (-429559199989303938095027179097/11258999068426240000000000000000000), (5962655581582857101276912517/2814749767106560000000000000000000), (29064177355798547513198140053/11258999068426240000000000000000000), (-264156998004026273150485901/11258999068426240000000000000000000), (-34590870528451618114116059/703687441776640000000000000000000), (-334284561645876661682063/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial152.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial152.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial152.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial152 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 5225006110031616575110237484063303), (Int.negOfNat 841775514660140407488046911677714), (Int.ofNat 2596098209833418656656302099346), (Int.ofNat 1717477843882706003688617591272), (Int.ofNat 931505118875774943182827633987), (Int.ofNat 145330145200724609261378728078), (Int.negOfNat 19255599832186605106654489661), (Int.negOfNat 4412213256881567438096174425), (Int.ofNat 232603807706533650283451320), (Int.ofNat 61180775475587903557046437), (Int.negOfNat 1736236477785130703694570), (Int.negOfNat 512451547596439027397676), (Int.ofNat 8402373360339940173604), (Int.ofNat 2903682834513426598856), (Int.negOfNat 28204898323775670630), (Int.negOfNat 12103788976388824252), (Int.ofNat 203288857751168395), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-5225006110031616575110237484063303/11258999068426240000000000000000000), (-420887757330070203744023455838857/5629499534213120000000000000000000), (1298049104916709328328151049673/5629499534213120000000000000000000), (214684730485338250461077198909/1407374883553280000000000000000000), (931505118875774943182827633987/11258999068426240000000000000000000), (72665072600362304630689364039/5629499534213120000000000000000000), (-19255599832186605106654489661/11258999068426240000000000000000000), (-176488530275262697523846977/450359962737049600000000000000000), (5815095192663341257086283/281474976710656000000000000000000), (61180775475587903557046437/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial152.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial152.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial152.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial152 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 6866587297808392160355622010178289), (Int.negOfNat 774655718882560737540308449097272), (Int.ofNat 39962474872659282110000001646736), (Int.ofNat 10130163279135567666625399929309), (Int.ofNat 458334416534304481574412923092), (Int.negOfNat 256224057086996624536944204116), (Int.negOfNat 26186856051971934533126899085), (Int.ofNat 4248200241740317668977408305), (Int.ofNat 516603692551742183561646756), (Int.negOfNat 43534505240234681763416369), (Int.negOfNat 5611935779740942543956974), (Int.ofNat 291404641900269532970480), (Int.ofNat 39067730945037908561744), (Int.negOfNat 1352641644494433360500), (Int.negOfNat 188638089346047681498), (Int.ofNat 4283081203107591780), (Int.ofNat 543005491398433435), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-6866587297808392160355622010178289/11258999068426240000000000000000000), (-96831964860320092192538556137159/1407374883553280000000000000000000), (2497654679541205131875000102921/703687441776640000000000000000000), (10130163279135567666625399929309/11258999068426240000000000000000000), (114583604133576120393603230773/2814749767106560000000000000000000), (-64056014271749156134236051029/2814749767106560000000000000000000), (-5237371210394386906625379817/2251799813685248000000000000000000), (849640048348063533795481661/2251799813685248000000000000000000), (129150923137935545890411689/2814749767106560000000000000000000), (-43534505240234681763416369/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial152.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial152.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial152.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial152 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 8176900581076828918396174453592995), (Int.negOfNat 501795650087689400406655122416331), (Int.ofNat 88486563375008839544183371685141), (Int.ofNat 2358668353798133579047682771973), (Int.negOfNat 2141392792046815375700508704443), (Int.negOfNat 103242364199952766724674020202), (Int.ofNat 49228964716169468586609308237), (Int.ofNat 3165632864395670002356143409), (Int.negOfNat 669413942781623045160479792), (Int.negOfNat 48169730856371506948719701), (Int.ofNat 5722862683092733455646966), (Int.ofNat 433799395770044421927908), (Int.negOfNat 32964999162001754406376), (Int.negOfNat 2582992947535072388808), (Int.ofNat 135042878465431031322), (Int.ofNat 11048979481060839192), (Int.negOfNat 578759646603261595), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-1635380116215365783679234890718599/2251799813685248000000000000000000), (-501795650087689400406655122416331/11258999068426240000000000000000000), (88486563375008839544183371685141/11258999068426240000000000000000000), (2358668353798133579047682771973/11258999068426240000000000000000000), (-2141392792046815375700508704443/11258999068426240000000000000000000), (-51621182099976383362337010101/5629499534213120000000000000000000), (49228964716169468586609308237/11258999068426240000000000000000000), (3165632864395670002356143409/11258999068426240000000000000000000), (-41838371423851440322529987/703687441776640000000000000000000), (-48169730856371506948719701/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial152.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial152.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial152.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial152 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 8841875904374331157013292584248000), (Int.negOfNat 186222375342660454093623999039069), (Int.ofNat 55582019869868182066573543664530), (Int.negOfNat 10609453714903992058385372354136), (Int.negOfNat 187383551571003434476553269392), (Int.ofNat 411361574344371139198936407620), (Int.ofNat 9456707737921498888249270201), (Int.negOfNat 7741686958675738068646104989), (Int.negOfNat 267903392167156027026293004), (Int.ofNat 85543491659914148970430945), (Int.ofNat 3589268866378826805999854), (Int.negOfNat 610149040183353933184904), (Int.negOfNat 28359483008314260991036), (Int.ofNat 3010853432207083261740), (Int.ofNat 149444741605186582370), (Int.negOfNat 10617699178800350796), (Int.negOfNat 480742678253432395), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-1105234488046791394626661573031/1407374883553280000000000000000), (-186222375342660454093623999039069/11258999068426240000000000000000000), (5558201986986818206657354366453/1125899906842624000000000000000000), (-1326181714362999007298171544267/1407374883553280000000000000000000), (-11711471973187714654784579337/703687441776640000000000000000000), (20568078717218556959946820381/562949953421312000000000000000000), (9456707737921498888249270201/11258999068426240000000000000000000), (-7741686958675738068646104989/11258999068426240000000000000000000), (-66975848041789006756573251/2814749767106560000000000000000000), (17108698331982829794086189/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial152.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial152.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial152.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial152 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 9067110927010435508523666161482902), (Int.negOfNat 66013935107017720807193397527324), (Int.ofNat 17341091932813429118324310156473), (Int.ofNat 1530602314248466317072612889038), (Int.ofNat 2390915671137976442450098380368), (Int.negOfNat 63890089617116142904627557982), (Int.negOfNat 69340532764068945934099144545), (Int.ofNat 170896894471117707758914071), (Int.ofNat 1030128720777250820669965036), (Int.ofNat 13064346070559077543820229), (Int.negOfNat 9294140585881793282323682), (Int.negOfNat 205310817816431503685972), (Int.ofNat 55528684973912933790360), (Int.ofNat 1545211304260103288624), (Int.negOfNat 235387138648271380202), (Int.negOfNat 7532539935482233492), (Int.ofNat 954230435455354795), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-4533555463505217754261833080741451/5629499534213120000000000000000000), (-16503483776754430201798349381831/2814749767106560000000000000000000), (17341091932813429118324310156473/11258999068426240000000000000000000), (765301157124233158536306444519/5629499534213120000000000000000000), (149432229446123527653131148773/703687441776640000000000000000000), (-31945044808558071452313778991/5629499534213120000000000000000000), (-13868106552813789186819828909/2251799813685248000000000000000000), (170896894471117707758914071/11258999068426240000000000000000000), (257532180194312705167491259/2814749767106560000000000000000000), (13064346070559077543820229/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial152.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial152.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial152.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial152 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 9085474662116982520608075470364754), (Int.ofNat 80915406264912784334093670909278), (Int.ofNat 64065838008891139561859012355813), (Int.ofNat 8874857281073032527758203875162), (Int.negOfNat 1280385504732100093637979359833), (Int.negOfNat 468922579055534711330679560772), (Int.ofNat 26372044552871104969998224859), (Int.ofNat 9994058179499644710837079045), (Int.negOfNat 223860563857123216284259408), (Int.negOfNat 118818492183723940898479041), (Int.ofNat 328261701627898690669878), (Int.ofNat 878853478183693239270332), (Int.ofNat 7408246320066141965768), (Int.negOfNat 4421825856788503401700), (Int.negOfNat 65998179535990909778), (Int.ofNat 16387662204723705512), (Int.ofNat 293322935491066955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-4542737331058491260304037735182377/5629499534213120000000000000000000), (40457703132456392167046835454639/5629499534213120000000000000000000), (64065838008891139561859012355813/11258999068426240000000000000000000), (4437428640536516263879101937581/5629499534213120000000000000000000), (-1280385504732100093637979359833/11258999068426240000000000000000000), (-117230644763883677832669890193/2814749767106560000000000000000000), (26372044552871104969998224859/11258999068426240000000000000000000), (1998811635899928942167415809/2251799813685248000000000000000000), (-13991285241070201017766213/703687441776640000000000000000000), (-118818492183723940898479041/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial152.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial152.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial152.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial152 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 8629022293381516890967530939188876), (Int.ofNat 374240205936295235975149441224319), (Int.ofNat 61196861164584796045253950082002), (Int.negOfNat 11307170834385053773594336711600), (Int.negOfNat 2277919294775965681893042755644), (Int.ofNat 375125581368290798949315351014), (Int.ofNat 74924944666690960450675952629), (Int.negOfNat 6041610267880951246575705875), (Int.negOfNat 1265852696183547251634000728), (Int.ofNat 44638159894960268479687231), (Int.ofNat 12034585202698237912399218), (Int.negOfNat 157177698885315508460532), (Int.negOfNat 73235746360707199938792), (Int.ofNat 92784305418943995220), (Int.ofNat 312030466706261810522), (Int.ofNat 1755136157440185928), (Int.negOfNat 1163035752593416235), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-2157255573345379222741882734797219/2814749767106560000000000000000000), (374240205936295235975149441224319/11258999068426240000000000000000000), (30598430582292398022626975041001/5629499534213120000000000000000000), (-28267927085962634433985841779/28147497671065600000000000000000), (-569479823693991420473260688911/2814749767106560000000000000000000), (187562790684145399474657675507/5629499534213120000000000000000000), (74924944666690960450675952629/11258999068426240000000000000000000), (-48332882143047609972605647/90071992547409920000000000000000), (-158231587022943406454250091/1407374883553280000000000000000000), (44638159894960268479687231/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial152.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial152.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial152.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial152 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 7746922119420642041985293878281604), (Int.ofNat 451001878337011039122125232616229), (Int.negOfNat 19317477407117823541785763593732), (Int.negOfNat 7779023918219025335690972605045), (Int.ofNat 3185585676743051834810407461321), (Int.ofNat 374940940669172804198113458936), (Int.negOfNat 87397530033739903395908966775), (Int.negOfNat 10855546695374834932785649241), (Int.ofNat 978427406832420712201594116), (Int.ofNat 142050496738411367060629181), (Int.negOfNat 5877273608232574979312942), (Int.negOfNat 1074321125974612233948428), (Int.ofNat 21312001741704439235400), (Int.ofNat 5420487924255392896456), (Int.negOfNat 45259078616559772902), (Int.negOfNat 20323673738465348548), (Int.negOfNat 1500534159670795), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-1936730529855160510496323469570401/2814749767106560000000000000000000), (451001878337011039122125232616229/11258999068426240000000000000000000), (-4829369351779455885446440898433/2814749767106560000000000000000000), (-1555804783643805067138194521009/2251799813685248000000000000000000), (3185585676743051834810407461321/11258999068426240000000000000000000), (46867617583646600524764182367/1407374883553280000000000000000000), (-3495901201349596135836358671/450359962737049600000000000000000), (-10855546695374834932785649241/11258999068426240000000000000000000), (244606851708105178050398529/2814749767106560000000000000000000), (142050496738411367060629181/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial152.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial152.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial152.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial152 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 6928120815660012037949480038539769), (Int.ofNat 391961891408977858696810577833890), (Int.ofNat 14499599733537922595018569616424), (Int.ofNat 15025856612319248916629009658399), (Int.ofNat 200390001805836302139683840109), (Int.negOfNat 936306272491171579503763914762), (Int.negOfNat 67597633368517232586239845769), (Int.ofNat 15023675857222421333355002619), (Int.ofNat 1426912787042580978180157716), (Int.negOfNat 121254224694501395523532335), (Int.negOfNat 13978197397384040358778486), (Int.ofNat 607852819386224643677104), (Int.ofNat 84686538776116313699124), (Int.negOfNat 2090341052296488970060), (Int.negOfNat 358295941111788159730), (Int.ofNat 5192082439236895556), (Int.ofNat 1225929869065779595), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-6928120815660012037949480038539769/11258999068426240000000000000000000), (39196189140897785869681057783389/1125899906842624000000000000000000), (1812449966692240324377321202053/1407374883553280000000000000000000), (15025856612319248916629009658399/11258999068426240000000000000000000), (200390001805836302139683840109/11258999068426240000000000000000000), (-468153136245585789751881957381/5629499534213120000000000000000000), (-67597633368517232586239845769/11258999068426240000000000000000000), (15023675857222421333355002619/11258999068426240000000000000000000), (356728196760645244545039429/2814749767106560000000000000000000), (-24250844938900279104706467/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial152.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial152.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial152.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial152 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 5994860096892092326557973465804759), (Int.ofNat 556649407208839731784700016825108), (Int.ofNat 30291714726616891749404273138726), (Int.negOfNat 21500827547700308831857928473576), (Int.negOfNat 8055226538660683690097413192662), (Int.negOfNat 177873667691885907647666558348), (Int.ofNat 187380089259645204951711533187), (Int.ofNat 11957969952401061887315256161), (Int.negOfNat 1945932078595358569411627072), (Int.negOfNat 161740875187451424463884109), (Int.ofNat 12251314101775963972254626), (Int.ofNat 1197632529577274853231692), (Int.negOfNat 53173657184523778292616), (Int.negOfNat 5916820450705257983472), (Int.ofNat 170072298324499747222), (Int.ofNat 21764686179210586248), (Int.negOfNat 373970254692422405), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-5994860096892092326557973465804759/11258999068426240000000000000000000), (139162351802209932946175004206277/2814749767106560000000000000000000), (15145857363308445874702136569363/5629499534213120000000000000000000), (-2687603443462538603982241059197/1407374883553280000000000000000000), (-4027613269330341845048706596331/5629499534213120000000000000000000), (-44468416922971476911916639587/2814749767106560000000000000000000), (187380089259645204951711533187/11258999068426240000000000000000000), (11957969952401061887315256161/11258999068426240000000000000000000), (-30405188728052477647056673/175921860444160000000000000000000), (-161740875187451424463884109/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial152.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial152.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial152.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial152 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 5054019914714175314017056980246197), (Int.ofNat 186852674727686584020567679242461), (Int.negOfNat 257323613269245219311507535788169), (Int.negOfNat 60505727742975093683950023309446), (Int.ofNat 2132062775703539512973733969055), (Int.ofNat 2004411650392204616798484695238), (Int.ofNat 82764781883991978407850973165), (Int.negOfNat 26273631461966399496114031535), (Int.negOfNat 1687616264140907910447638564), (Int.ofNat 202318474503314472794539159), (Int.ofNat 15461531157473532555536166), (Int.negOfNat 1061501763717748639244680), (Int.negOfNat 89492053755487914150016), (Int.ofNat 4101888453550020164820), (Int.ofNat 367827860857968710602), (Int.negOfNat 11873785143750034140), (Int.negOfNat 1163667055920778555), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-5054019914714175314017056980246197/11258999068426240000000000000000000), (186852674727686584020567679242461/11258999068426240000000000000000000), (-257323613269245219311507535788169/11258999068426240000000000000000000), (-30252863871487546841975011654723/5629499534213120000000000000000000), (426412555140707902594746793811/2251799813685248000000000000000000), (1002205825196102308399242347619/5629499534213120000000000000000000), (16552956376798395681570194633/2251799813685248000000000000000000), (-5254726292393279899222806307/2251799813685248000000000000000000), (-421904066035226977611909641/2814749767106560000000000000000000), (202318474503314472794539159/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial152.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial152.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial152.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial152 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 6093781853298411274622897362853567), (Int.negOfNat 1337008032518770627897978193335605), (Int.negOfNat 408576842134638259569300660613305), (Int.ofNat 33503846487631808629701009397005), (Int.ofNat 18864528620505840660198163539190), (Int.ofNat 528330507849375736937970275297), (Int.negOfNat 306011771624947763528009165191), (Int.negOfNat 16585384597240932807448940545), (Int.ofNat 2853502428352376661922575200), (Int.ofNat 185657441185125413945829173), (Int.negOfNat 17901714334959980590012030), (Int.negOfNat 1252362454006419764406724), (Int.ofNat 81787003867082166949044), (Int.ofNat 5868330838826991470224), (Int.negOfNat 285426305339552206330), (Int.negOfNat 20661051485511868588), (Int.ofNat 749441043544515605), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-6093781853298411274622897362853567/11258999068426240000000000000000000), (-267401606503754125579595638667121/2251799813685248000000000000000000), (-81715368426927651913860132122661/2251799813685248000000000000000000), (6700769297526361725940201879401/2251799813685248000000000000000000), (1886452862050584066019816353919/1125899906842624000000000000000000), (528330507849375736937970275297/11258999068426240000000000000000000), (-306011771624947763528009165191/11258999068426240000000000000000000), (-3317076919448186561489788109/2251799813685248000000000000000000), (3566878035440470827403219/14073748835532800000000000000000), (185657441185125413945829173/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial152.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial152.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial152.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial152 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 9836238128598357943771702708828205), (Int.negOfNat 1986276136243316074354174928023644), (Int.ofNat 208606994657950584418681987596230), (Int.ofNat 153097981402003723828532004238445), (Int.ofNat 4806383129153600950007481117254), (Int.negOfNat 3055840969360597920405171090454), (Int.negOfNat 166656835704174923794884882717), (Int.ofNat 34570757858595777431299890531), (Int.ofNat 2140730932350084246055861776), (Int.negOfNat 260241422308868590857453127), (Int.negOfNat 16462398682471977592617982), (Int.ofNat 1407159845456668836251992), (Int.ofNat 87046807603475222000172), (Int.negOfNat 5733421981917958099720), (Int.negOfNat 339588738899289096330), (Int.ofNat 17890088568061770324), (Int.ofNat 1101404242775777515), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-1967247625719671588754340541765641/2251799813685248000000000000000000), (-496569034060829018588543732005911/2814749767106560000000000000000000), (20860699465795058441868198759623/1125899906842624000000000000000000), (30619596280400744765706400847689/2251799813685248000000000000000000), (2403191564576800475003740558627/5629499534213120000000000000000000), (-1527920484680298960202585545227/5629499534213120000000000000000000), (-166656835704174923794884882717/11258999068426240000000000000000000), (34570757858595777431299890531/11258999068426240000000000000000000), (133795683271880265378491361/703687441776640000000000000000000), (-260241422308868590857453127/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial152.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial152.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial152.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial152 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 11776303220124725316192021968735872), (Int.ofNat 579680063844107185766762137107290), (Int.ofNat 983806543464489654727936922245028), (Int.ofNat 64261557105476545043733031392165), (Int.negOfNat 24876474233447262390638152095263), (Int.negOfNat 1801873133774161637784210913477), (Int.ofNat 351384215633377392272864823691), (Int.ofNat 24435841353465850240218820573), (Int.negOfNat 3243655194490757711621884764), (Int.negOfNat 207059754127717619427497605), (Int.ofNat 21056340354945151668630370), (Int.ofNat 1214907694247086202241812), (Int.negOfNat 100897597562483997039184), (Int.negOfNat 5243509278066217387216), (Int.ofNat 369356580540488514962), (Int.ofNat 17248574834924386392), (Int.negOfNat 1104157561348275125), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-92002368907224416532750171630749/87960930222080000000000000000000), (57968006384410718576676213710729/1125899906842624000000000000000000), (245951635866122413681984230561257/2814749767106560000000000000000000), (12852311421095309008746606278433/2251799813685248000000000000000000), (-24876474233447262390638152095263/11258999068426240000000000000000000), (-1801873133774161637784210913477/11258999068426240000000000000000000), (351384215633377392272864823691/11258999068426240000000000000000000), (24435841353465850240218820573/11258999068426240000000000000000000), (-810913798622689427905471191/2814749767106560000000000000000000), (-41411950825543523885499521/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial152.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial152.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial152.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial152.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial152 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial152 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial152 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 13089803778105105936243664410634273), (Int.negOfNat 1004574728670074112455807524411119), (Int.ofNat 1023031749393764399083789984156374), (Int.negOfNat 57615137668966077989490612754285), (Int.negOfNat 25327908991487201185535062006166), (Int.ofNat 1739843766205697482378020448231), (Int.ofNat 354602612820697499032913317611), (Int.negOfNat 24097786984269058220843669373), (Int.negOfNat 3257122683236081197504558764), (Int.ofNat 205948024225238419462677205), (Int.ofNat 21091892462251143869302370), (Int.negOfNat 1212503615283279529958612), (Int.negOfNat 100962652589794878699984), (Int.ofNat 5240552231370268220816), (Int.ofNat 369356580540488514962), (Int.negOfNat 17248574834924386392), (Int.negOfNat 1104157561348275125), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-13089803778105105936243664410634273/11258999068426240000000000000000000), (-1004574728670074112455807524411119/11258999068426240000000000000000000), (511515874696882199541894992078187/5629499534213120000000000000000000), (-11523027533793215597898122550857/2251799813685248000000000000000000), (-12663954495743600592767531003083/5629499534213120000000000000000000), (1739843766205697482378020448231/11258999068426240000000000000000000), (354602612820697499032913317611/11258999068426240000000000000000000), (-24097786984269058220843669373/11258999068426240000000000000000000), (-814280670809020299376139691/2814749767106560000000000000000000), (41189604845047683892535441/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial152.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial152.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial152.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 11798418460376442669353158643685855), (Int.ofNat 1779384302548240437002906386792304), (Int.ofNat 272884737275338453386283881986912), (Int.negOfNat 151869431699484355881397542691452), (Int.ofNat 4003417698754600748148248303125), (Int.ofNat 3052904440761408050554962698533), (Int.negOfNat 160810633559201411181508024317), (Int.negOfNat 34563429774610318292730892531), (Int.ofNat 2116186314319760121781816176), (Int.ofNat 260221522648056766640653527), (Int.negOfNat 16397574263220812919938382), (Int.negOfNat 1407118446802925547922392), (Int.ofNat 86930004258985229927372), (Int.ofNat 5733421981917958099720), (Int.negOfNat 339588738899289096330), (Int.negOfNat 17890088568061770324), (Int.ofNat 1101404242775777515), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-2359683692075288533870631728737171/2251799813685248000000000000000000), (111211518909265027312681649174519/703687441776640000000000000000000), (8527648039854326668321371312091/351843720888320000000000000000000), (-37967357924871088970349385672863/2814749767106560000000000000000000), (1281093663601472239407439457/3602879701896396800000000000000), (3052904440761408050554962698533/11258999068426240000000000000000000), (-160810633559201411181508024317/11258999068426240000000000000000000), (-34563429774610318292730892531/11258999068426240000000000000000000), (132261644644985007611363511/703687441776640000000000000000000), (260221522648056766640653527/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial152.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial152.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial152.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 8215379032868371688060011548508881), (Int.ofNat 1377140853431733930618802428175006), (Int.negOfNat 355069216484402833805332225181627), (Int.negOfNat 37920091840874136025677986520830), (Int.ofNat 18358310014927108523699503189226), (Int.negOfNat 471020893493910497761739851487), (Int.negOfNat 302613728254254803382135070691), (Int.ofNat 16256682098573468272523914545), (Int.ofNat 2839423631946559538259822800), (Int.negOfNat 184568545664422565270358773), (Int.negOfNat 17864599076813009123402030), (Int.ofNat 1250005687789748278785924), (Int.ofNat 81718991793075336121844), (Int.negOfNat 5865373792131042303824), (Int.negOfNat 285426305339552206330), (Int.ofNat 20661051485511868588), (Int.ofNat 749441043544515605), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-8215379032868371688060011548508881/11258999068426240000000000000000000), (688570426715866965309401214087503/5629499534213120000000000000000000), (-355069216484402833805332225181627/11258999068426240000000000000000000), (-3792009184087413602567798652083/1125899906842624000000000000000000), (9179155007463554261849751594613/5629499534213120000000000000000000), (-471020893493910497761739851487/11258999068426240000000000000000000), (-302613728254254803382135070691/11258999068426240000000000000000000), (3251336419714693654504782909/2251799813685248000000000000000000), (7098559079866398845649557/28147497671065600000000000000000), (-184568545664422565270358773/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial152.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial152.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial152.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 6922744115582491888542794653735158), (Int.ofNat 3194898071126174835575745483603), (Int.negOfNat 237303149135196154607656124717183), (Int.ofNat 54672820399200808392994984634297), (Int.ofNat 2299800515428266903238281000111), (Int.negOfNat 1937824568741462236518621098057), (Int.ofNat 80802635029621116950860197885), (Int.ofNat 25898379247198894226250141135), (Int.negOfNat 1678895407398725241747844964), (Int.negOfNat 201078436597125086442969959), (Int.ofNat 15438316748929749129253366), (Int.ofNat 1058818243841174770736680), (Int.negOfNat 89449176578396651237216), (Int.negOfNat 4097452883506096415220), (Int.ofNat 367827860857968710602), (Int.ofNat 11873785143750034140), (Int.negOfNat 1163667055920778555), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-3461372057791245944271397326867579/5629499534213120000000000000000000), (3194898071126174835575745483603/11258999068426240000000000000000000), (-237303149135196154607656124717183/11258999068426240000000000000000000), (54672820399200808392994984634297/11258999068426240000000000000000000), (2299800515428266903238281000111/11258999068426240000000000000000000), (-1937824568741462236518621098057/11258999068426240000000000000000000), (16160527005924223390172039577/2251799813685248000000000000000000), (5179675849439778845250028227/2251799813685248000000000000000000), (-419723851849681310436961241/2814749767106560000000000000000000), (-201078436597125086442969959/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial152.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial152.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial152.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 7445426735236400393895745891392792), (Int.negOfNat 346353497631161095344200341647685), (Int.ofNat 23965324666096301635443923058360), (Int.ofNat 19171050787952964787263629685801), (Int.negOfNat 7430068861124308300166543917097), (Int.ofNat 195539622944770743279193844443), (Int.ofNat 181860094269212490967324676067), (Int.negOfNat 12050100486656958891356592161), (Int.negOfNat 1922125698822775961466679872), (Int.ofNat 162041850799940469560208909), (Int.ofNat 12188198938680192011471826), (Int.negOfNat 1198283079850383669839692), (Int.negOfNat 53059810886729735386216), (Int.ofNat 5918298974053232566672), (Int.ofNat 170072298324499747222), (Int.negOfNat 21764686179210586248), (Int.negOfNat 373970254692422405), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-930678341904550049236968236424099/1407374883553280000000000000000000), (-69270699526232219068840068329537/2251799813685248000000000000000000), (599133116652407540886098076459/281474976710656000000000000000000), (19171050787952964787263629685801/11258999068426240000000000000000000), (-7430068861124308300166543917097/11258999068426240000000000000000000), (195539622944770743279193844443/11258999068426240000000000000000000), (181860094269212490967324676067/11258999068426240000000000000000000), (-12050100486656958891356592161/11258999068426240000000000000000000), (-30033214044105874397916873/175921860444160000000000000000000), (162041850799940469560208909/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial152.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial152.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial152.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 7991830465103537759832008294777876), (Int.negOfNat 214586911058830599008767030949662), (Int.ofNat 9268209622727542440872570602430), (Int.negOfNat 12539230853042167006735821153007), (Int.ofNat 672226582636707637061504389712), (Int.ofNat 890748886512055262483356575181), (Int.negOfNat 71753726199632903180306392169), (Int.negOfNat 14752658027831097895209958219), (Int.ofNat 1444831555888297308791350116), (Int.ofNat 120351951831395065028021135), (Int.negOfNat 14025700677408747153234086), (Int.negOfNat 605896732996854270103504), (Int.ofNat 84772293130298839524724), (Int.ofNat 2087384005600539803660), (Int.negOfNat 358295941111788159730), (Int.negOfNat 5192082439236895556), (Int.ofNat 1225929869065779595), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-1997957616275884439958002073694469/2814749767106560000000000000000000), (-107293455529415299504383515474831/5629499534213120000000000000000000), (926820962272754244087257060243/1125899906842624000000000000000000), (-12539230853042167006735821153007/11258999068426240000000000000000000), (42014161414794227316344024357/703687441776640000000000000000000), (890748886512055262483356575181/11258999068426240000000000000000000), (-71753726199632903180306392169/11258999068426240000000000000000000), (-14752658027831097895209958219/11258999068426240000000000000000000), (361207888972074327197837529/2814749767106560000000000000000000), (24070390366279013005604227/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial152.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial152.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial152.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 8451050032322670679452585402745938), (Int.negOfNat 253919272719769021385592233184056), (Int.negOfNat 2737498336050180723248141308062), (Int.ofNat 11731463477649134098818632267665), (Int.ofNat 3044252688843676756023129873517), (Int.negOfNat 441714967541092122462838145887), (Int.negOfNat 86485166897681101424102946375), (Int.ofNat 11249859298312010182089474441), (Int.ofNat 974673002294679617067516916), (Int.negOfNat 143361948143773936161400781), (Int.negOfNat 5867385554160924051508142), (Int.ofNat 1077162847849419382858828), (Int.ofNat 21294259461528744237000), (Int.negOfNat 5424923494299316646056), (Int.negOfNat 45259078616559772902), (Int.ofNat 20323673738465348548), (Int.negOfNat 1500534159670795), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-4225525016161335339726292701372969/5629499534213120000000000000000000), (-31739909089971127673199029148007/1407374883553280000000000000000000), (-1368749168025090361624070654031/5629499534213120000000000000000000), (2346292695529826819763726453533/2251799813685248000000000000000000), (3044252688843676756023129873517/11258999068426240000000000000000000), (-441714967541092122462838145887/11258999068426240000000000000000000), (-691881335181448811392823571/90071992547409920000000000000000), (11249859298312010182089474441/11258999068426240000000000000000000), (243668250573669904266879229/2814749767106560000000000000000000), (-143361948143773936161400781/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial152.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial152.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial152.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 8845336412457318033747931850274345), (Int.negOfNat 72927945449629818848107623170959), (Int.ofNat 93228929919080139586984047947548), (Int.ofNat 11811268950745590701822660786148), (Int.negOfNat 2931086848516394772878258308160), (Int.negOfNat 401994306584863979925880868408), (Int.ofNat 80129145833548694022465641429), (Int.ofNat 6210587182081346441240432275), (Int.negOfNat 1287994429508757384342637928), (Int.negOfNat 45204767062545297440674431), (Int.ofNat 12093174647408426720865618), (Int.ofNat 158407830310830361682932), (Int.negOfNat 73340721518413395345992), (Int.negOfNat 94262828766918578420), (Int.ofNat 312030466706261810522), (Int.negOfNat 1755136157440185928), (Int.negOfNat 1163035752593416235), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-1769067282491463606749586370054869/2251799813685248000000000000000000), (-72927945449629818848107623170959/11258999068426240000000000000000000), (23307232479770034896746011986887/2814749767106560000000000000000000), (2952817237686397675455665196537/2814749767106560000000000000000000), (-9159646401613733665244557213/35184372088832000000000000000000), (-50249288323107997490735108551/1407374883553280000000000000000000), (80129145833548694022465641429/11258999068426240000000000000000000), (248423487283253857649617291/450359962737049600000000000000000), (-160999303688594673042829741/1407374883553280000000000000000000), (-45204767062545297440674431/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial152.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial152.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial152.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 8577964878738115542802212699702575), (Int.ofNat 332574687720809816284636081970397), (Int.ofNat 82617950172843510312269414864927), (Int.negOfNat 13785333919876178433411100705714), (Int.negOfNat 1868932591557900048610387684732), (Int.ofNat 508134166054994943884637506923), (Int.ofNat 31289764632803984259146679659), (Int.negOfNat 10201027416571131396954784645), (Int.negOfNat 244919494497225405471723008), (Int.ofNat 119495876728386418426965441), (Int.ofNat 384036347963146977360278), (Int.negOfNat 880317216298188076638332), (Int.ofNat 7307706732403870308168), (Int.ofNat 4424782903484452568100), (Int.negOfNat 65998179535990909778), (Int.negOfNat 16387662204723705512), (Int.ofNat 293322935491066955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-343118595149524621712088507988103/450359962737049600000000000000000), (332574687720809816284636081970397/11258999068426240000000000000000000), (82617950172843510312269414864927/11258999068426240000000000000000000), (-6892666959938089216705550352857/5629499534213120000000000000000000), (-467233147889475012152596921183/2814749767106560000000000000000000), (508134166054994943884637506923/11258999068426240000000000000000000), (31289764632803984259146679659/11258999068426240000000000000000000), (-2040205483314226279390956929/2251799813685248000000000000000000), (-478358387689893370061959/21990232555520000000000000000000), (119495876728386418426965441/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial152.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial152.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial152.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 7705575051239878746285301153841429), (Int.ofNat 479921921384014197944643616029727), (Int.negOfNat 3550710689918958932422177055577), (Int.negOfNat 8943371450331204514931657478257), (Int.ofNat 2411417439923252113415410997287), (Int.ofNat 137057240829005253190298359092), (Int.negOfNat 69063390780321613567367938945), (Int.negOfNat 573705257979012337542609271), (Int.ofNat 1028687182129230078867893836), (Int.negOfNat 11737703205985710043764229), (Int.negOfNat 9290227131202073149770482), (Int.ofNat 202439525474664863111572), (Int.ofNat 55522770880521035457560), (Int.negOfNat 1540775734216179539024), (Int.negOfNat 235387138648271380202), (Int.ofNat 7532539935482233492), (Int.ofNat 954230435455354795), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-7705575051239878746285301153841429/11258999068426240000000000000000000), (479921921384014197944643616029727/11258999068426240000000000000000000), (-3550710689918958932422177055577/11258999068426240000000000000000000), (-8943371450331204514931657478257/11258999068426240000000000000000000), (2411417439923252113415410997287/11258999068426240000000000000000000), (34264310207251313297574589773/2814749767106560000000000000000000), (-13812678156064322713473587789/2251799813685248000000000000000000), (-573705257979012337542609271/11258999068426240000000000000000000), (257171795532307519716973459/2814749767106560000000000000000000), (-11737703205985710043764229/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial152.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial152.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial152.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 6792757556532128513690317020685943), (Int.ofNat 433993671514167276561878147326846), (Int.negOfNat 3641661774780076978025653250681), (Int.ofNat 6110642935360639464191750398383), (Int.ofNat 472298445266956617747926597951), (Int.negOfNat 366728521548329397518903933787), (Int.ofNat 4795832472099546826835244201), (Int.ofNat 7495748668012677410146044589), (Int.negOfNat 248427882612699948252165004), (Int.negOfNat 84733393584795092535723345), (Int.ofNat 3537865820338802183477454), (Int.ofNat 608395511492656077509704), (Int.negOfNat 28267814560739836832636), (Int.negOfNat 3007896385511134095340), (Int.ofNat 149444741605186582370), (Int.ofNat 10617699178800350796), (Int.negOfNat 480742678253432395), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-6792757556532128513690317020685943/11258999068426240000000000000000000), (216996835757083638280939073663423/5629499534213120000000000000000000), (-3641661774780076978025653250681/11258999068426240000000000000000000), (6110642935360639464191750398383/11258999068426240000000000000000000), (472298445266956617747926597951/11258999068426240000000000000000000), (-366728521548329397518903933787/11258999068426240000000000000000000), (4795832472099546826835244201/11258999068426240000000000000000000), (7495748668012677410146044589/11258999068426240000000000000000000), (-62106970653174987063041251/2814749767106560000000000000000000), (-16946678716959018507144669/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial152.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial152.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial152.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 5893466115511173763721946035988688), (Int.ofNat 482383418915085444936427619837124), (Int.ofNat 20427146785550883429225681997523), (Int.negOfNat 639763774762148089793851261538), (Int.negOfNat 1359568904470848675110059098402), (Int.ofNat 81188098076450586795043126812), (Int.ofNat 43657942283214228228721638237), (Int.negOfNat 3039323701734200216914107809), (Int.negOfNat 646103681621973067632958592), (Int.ofNat 47751390275591673739489701), (Int.ofNat 5661328795072386989038166), (Int.negOfNat 432893060957736002426308), (Int.negOfNat 32854109910903660666376), (Int.ofNat 2581514424187097805608), (Int.ofNat 135042878465431031322), (Int.negOfNat 11048979481060839192), (Int.negOfNat 578759646603261595), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-368341632219448360232621627249293/703687441776640000000000000000000), (120595854728771361234106904959281/2814749767106560000000000000000000), (20427146785550883429225681997523/11258999068426240000000000000000000), (-319881887381074044896925630769/5629499534213120000000000000000000), (-679784452235424337555029549201/5629499534213120000000000000000000), (20297024519112646698760781703/2814749767106560000000000000000000), (43657942283214228228721638237/11258999068426240000000000000000000), (-3039323701734200216914107809/11258999068426240000000000000000000), (-5047685012671664590882489/87960930222080000000000000000000), (47751390275591673739489701/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial152.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial152.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial152.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 4868994963971726421071003813958802), (Int.ofNat 525896253237488502784450389019971), (Int.negOfNat 1997079742090369345196833618986), (Int.negOfNat 3820840651388809914949731780424), (Int.ofNat 744366240687210284529129048121), (Int.ofNat 187068325687214840548095356247), (Int.negOfNat 27847141201683494322004091405), (Int.negOfNat 3860858989887400163610852305), (Int.ofNat 523298940020933721144081556), (Int.ofNat 42255634825968618947775969), (Int.negOfNat 5629515308891125842745374), (Int.negOfNat 288636846192861113220080), (Int.ofNat 39100258458693349392144), (Int.ofNat 1348206074450509610900), (Int.negOfNat 188638089346047681498), (Int.negOfNat 4283081203107591780), (Int.ofNat 543005491398433435), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-2434497481985863210535501906979401/5629499534213120000000000000000000), (525896253237488502784450389019971/11258999068426240000000000000000000), (-998539871045184672598416809493/5629499534213120000000000000000000), (-477605081423601239368716472553/1407374883553280000000000000000000), (744366240687210284529129048121/11258999068426240000000000000000000), (187068325687214840548095356247/11258999068426240000000000000000000), (-5569428240336698864400818281/2251799813685248000000000000000000), (-772171797977480032722170461/2251799813685248000000000000000000), (130824735005233430286020389/2814749767106560000000000000000000), (42255634825968618947775969/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial152.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial152.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial152.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 3839988450746378407546639840733994), (Int.ofNat 504368867217875958339519902823529), (Int.negOfNat 307408755194241136694130277036), (Int.ofNat 4070107476941906856559367859212), (Int.ofNat 537043427720762151186173904906), (Int.negOfNat 201509493313996092459965120968), (Int.negOfNat 15619861219712682568592142861), (Int.ofNat 4720588012119166455296150025), (Int.ofNat 216841656817510698757394520), (Int.negOfNat 62195965937388710888064437), (Int.negOfNat 1694420922040280588490970), (Int.ofNat 514647154768181283449676), (Int.ofNat 8326968669593236430404), (Int.negOfNat 2906639881209375765256), (Int.negOfNat 28204898323775670630), (Int.ofNat 12103788976388824252), (Int.ofNat 203288857751168395), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-1919994225373189203773319920366997/5629499534213120000000000000000000), (504368867217875958339519902823529/11258999068426240000000000000000000), (-76852188798560284173532569259/2814749767106560000000000000000000), (1017526869235476714139841964803/2814749767106560000000000000000000), (268521713860381075593086952453/5629499534213120000000000000000000), (-25188686664249511557495640121/1407374883553280000000000000000000), (-15619861219712682568592142861/11258999068426240000000000000000000), (188823520484766658211846001/450359962737049600000000000000000), (5421041420437767468934863/281474976710656000000000000000000), (-62195965937388710888064437/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial152.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial152.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial152.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 2798147540019995032137978700368448), (Int.ofNat 552236879845899369267698111395536), (Int.ofNat 20402039981587341318498381861481), (Int.ofNat 500442470834693108012616437466), (Int.negOfNat 1102427864317102743674159643498), (Int.negOfNat 19212183777737977948384719739), (Int.ofNat 34737455250431572645724864053), (Int.ofNat 223659087949242419996124701), (Int.negOfNat 577777316276115460757809744), (Int.ofNat 474832141003933891164463), (Int.ofNat 5825167314733586495760958), (Int.negOfNat 31381166440067110028208), (Int.negOfNat 38969585345074030177788), (Int.ofNat 314867947112673134800), (Int.ofNat 184557754461732648570), (Int.negOfNat 2216308334317112036), (Int.negOfNat 605268304543434475), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-43721055312812422377155917193257/175921860444160000000000000000000), (34514804990368710579231131962221/703687441776640000000000000000000), (20402039981587341318498381861481/11258999068426240000000000000000000), (250221235417346554006308218733/5629499534213120000000000000000000), (-551213932158551371837079821749/5629499534213120000000000000000000), (-19212183777737977948384719739/11258999068426240000000000000000000), (34737455250431572645724864053/11258999068426240000000000000000000), (223659087949242419996124701/11258999068426240000000000000000000), (-36111082267257216297363109/703687441776640000000000000000000), (474832141003933891164463/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial152.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial152.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial152.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 1624205812134403166439771039245612), (Int.ofNat 609243474638931806297248938058730), (Int.ofNat 2927255535984219057418304642121), (Int.negOfNat 4353066828961627590578710713307), (Int.ofNat 279447637035871658714261296235), (Int.ofNat 200915490787764738361056016408), (Int.negOfNat 9517569082263951388072659019), (Int.negOfNat 4404335959000235483482731397), (Int.ofNat 174261986581731059153324116), (Int.ofNat 55486245572839946476986805), (Int.negOfNat 1943090740967123906236090), (Int.negOfNat 448297215346822853991188), (Int.ofNat 14255711096502227131056), (Int.ofNat 2502542450121181787064), (Int.negOfNat 71808431356443316938), (Int.negOfNat 10461163243910997848), (Int.ofNat 192936202149258485), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-406051453033600791609942759811403/2814749767106560000000000000000000), (60924347463893180629724893805873/1125899906842624000000000000000000), (2927255535984219057418304642121/11258999068426240000000000000000000), (-4353066828961627590578710713307/11258999068426240000000000000000000), (55889527407174331742852259247/2251799813685248000000000000000000), (25114436348470592295132002051/1407374883553280000000000000000000), (-9517569082263951388072659019/11258999068426240000000000000000000), (-4404335959000235483482731397/11258999068426240000000000000000000), (43565496645432764788331029/2814749767106560000000000000000000), (11097249114567989295397361/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial152.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial152.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial152.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 419036607306715066173306872755466), (Int.ofNat 590222501895751749107155568486649), (Int.negOfNat 5120815835521460541656769786047), (Int.ofNat 2493950835943887715396650011993), (Int.ofNat 860798631170756941264596958802), (Int.negOfNat 120087844629742537241235342681), (Int.negOfNat 26217343806800143367052887341), (Int.ofNat 2730850368358679019119662163), (Int.ofNat 426267760736209096331329444), (Int.negOfNat 35659666897827801406795875), (Int.negOfNat 4259184035080158695735230), (Int.ofNat 298176187349398531540012), (Int.ofNat 28534367149627132269024), (Int.negOfNat 1716467152217119119176), (Int.negOfNat 136381987654235492862), (Int.ofNat 7382244606202420472), (Int.ofNat 396462987405373035), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-209518303653357533086653436377733/5629499534213120000000000000000000), (590222501895751749107155568486649/11258999068426240000000000000000000), (-5120815835521460541656769786047/11258999068426240000000000000000000), (2493950835943887715396650011993/11258999068426240000000000000000000), (430399315585378470632298479401/5629499534213120000000000000000000), (-120087844629742537241235342681/11258999068426240000000000000000000), (-26217343806800143367052887341/11258999068426240000000000000000000), (2730850368358679019119662163/11258999068426240000000000000000000), (106566940184052274082832361/2814749767106560000000000000000000), (-285277335182622411254367/90071992547409920000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial152.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial152.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial152.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 769565562648965563518818250251293), (Int.ofNat 614131354353217956296930647188447), (Int.ofNat 16998491180129001061190332383797), (Int.ofNat 2433291975519228177804644123998), (Int.negOfNat 856619429253711504417059939983), (Int.negOfNat 109542553181111515563174380508), (Int.ofNat 27118154989675249704246726907), (Int.ofNat 2390733701183153473223171661), (Int.negOfNat 452342218016835658103246216), (Int.negOfNat 30540126428665899537181617), (Int.ofNat 4595529980114992365944962), (Int.ofNat 253193038415199457933392), (Int.negOfNat 31096295614051163839292), (Int.negOfNat 1457547709983853807640), (Int.ofNat 148821255814706979030), (Int.ofNat 6566975384975336884), (Int.negOfNat 484758603480654645), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(769565562648965563518818250251293/11258999068426240000000000000000000), (614131354353217956296930647188447/11258999068426240000000000000000000), (16998491180129001061190332383797/11258999068426240000000000000000000), (1216645987759614088902322061999/5629499534213120000000000000000000), (-856619429253711504417059939983/11258999068426240000000000000000000), (-27385638295277878890793595127/2814749767106560000000000000000000), (27118154989675249704246726907/11258999068426240000000000000000000), (2390733701183153473223171661/11258999068426240000000000000000000), (-56542777252104457262905777/1407374883553280000000000000000000), (-30540126428665899537181617/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial152.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial152.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial152.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 2069992526638927519631617710323103), (Int.ofNat 680919325864563532701826012579114), (Int.ofNat 9497372134677154908985326440654), (Int.negOfNat 4020958474282670587189875619112), (Int.negOfNat 217161124445833690473184998147), (Int.ofNat 193557223873864236190170878642), (Int.ofNat 6553759819205872127087200421), (Int.negOfNat 4371975756502061706777046135), (Int.negOfNat 115197062858566064699056680), (Int.ofNat 56321040603086798116115643), (Int.ofNat 1294910114489303300947290), (Int.negOfNat 463059196041403255817324), (Int.negOfNat 9820816993256466315684), (Int.ofNat 2617132431465388261984), (Int.ofNat 52197154538221266030), (Int.negOfNat 10794721256789902668), (Int.negOfNat 41746469601613515), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(2069992526638927519631617710323103/11258999068426240000000000000000000), (340459662932281766350913006289557/5629499534213120000000000000000000), (4748686067338577454492663220327/5629499534213120000000000000000000), (-502619809285333823398734452389/1407374883553280000000000000000000), (-217161124445833690473184998147/11258999068426240000000000000000000), (96778611936932118095085439321/5629499534213120000000000000000000), (6553759819205872127087200421/11258999068426240000000000000000000), (-874395151300412341355409227/2251799813685248000000000000000000), (-2879926571464151617476417/281474976710656000000000000000000), (56321040603086798116115643/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial152.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial152.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial152.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3440231785294605141193207759831609), (Int.ofNat 678505528606694202530271438191552), (Int.negOfNat 5665996942568603595497741580896), (Int.ofNat 680694301788403705775462383411), (Int.ofNat 983129553671113671613358252068), (Int.negOfNat 36471903697512407215498241324), (Int.negOfNat 32197178885403103620261390075), (Int.ofNat 736599313060286587994042535), (Int.ofNat 551412624627131744529809004), (Int.negOfNat 7164582117429634802109751), (Int.negOfNat 5708138652814110651695946), (Int.ofNat 34668285101383761533520), (Int.ofNat 39057109512674492381136), (Int.negOfNat 52219361228715709860), (Int.negOfNat 187700160653770982302), (Int.negOfNat 550671960663600700), (Int.ofNat 547021416625655685), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(3440231785294605141193207759831609/11258999068426240000000000000000000), (10601648884479596914535491221743/175921860444160000000000000000000), (-177062404455268862359304424403/351843720888320000000000000000000), (680694301788403705775462383411/11258999068426240000000000000000000), (245782388417778417903339563017/2814749767106560000000000000000000), (-9117975924378101803874560331/2814749767106560000000000000000000), (-1287887155416124144810455603/450359962737049600000000000000000), (147319862612057317598808507/2251799813685248000000000000000000), (137853156156782936132452251/2814749767106560000000000000000000), (-7164582117429634802109751/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial152.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial152.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial152.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4792752922101685292832804070960275), (Int.ofNat 687220644045824212634067543213371), (Int.ofNat 12756095609695712012667009005059), (Int.ofNat 3215450246089987300233247215507), (Int.negOfNat 588989038797249547819632905677), (Int.negOfNat 169625328221518373414639825318), (Int.ofNat 18550385949188293368170039803), (Int.ofNat 4135625347512949507800879351), (Int.negOfNat 286314603451907753141075448), (Int.negOfNat 56758555429283838487645579), (Int.ofNat 2530962035454274362797714), (Int.ofNat 488861485638688658924292), (Int.negOfNat 14135855888754234849544), (Int.negOfNat 2846088822905014946232), (Int.ofNat 53152037383984510478), (Int.ofNat 11898355950488620328), (Int.negOfNat 333724319250479685), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(191710116884067411713312162838411/450359962737049600000000000000000), (687220644045824212634067543213371/11258999068426240000000000000000000), (12756095609695712012667009005059/11258999068426240000000000000000000), (3215450246089987300233247215507/11258999068426240000000000000000000), (-588989038797249547819632905677/11258999068426240000000000000000000), (-84812664110759186707319912659/5629499534213120000000000000000000), (18550385949188293368170039803/11258999068426240000000000000000000), (4135625347512949507800879351/11258999068426240000000000000000000), (-35789325431488469142634431/1407374883553280000000000000000000), (-56758555429283838487645579/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial152.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial152.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial152.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 6230708100230604004609517937270960), (Int.ofNat 749421205364537720977536404757149), (Int.ofNat 10841190247852435187452711451510), (Int.negOfNat 3758512850527862902588182982424), (Int.negOfNat 511848345924626484145376709248), (Int.ofNat 190260257718359428041357212820), (Int.ofNat 20579817305572437068128695959), (Int.negOfNat 4237094387285538374893085451), (Int.negOfNat 417138196487765808867856156), (Int.ofNat 50768935675277630001621175), (Int.ofNat 4879457389912264978040666), (Int.negOfNat 370272069667137564520296), (Int.negOfNat 36140047949255733041444), (Int.ofNat 1798383253407903624020), (Int.ofNat 183034891578218720030), (Int.negOfNat 6131030743849537884), (Int.negOfNat 609284229770656725), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(77883851252882550057618974215887/140737488355328000000000000000000), (749421205364537720977536404757149/11258999068426240000000000000000000), (1084119024785243518745271145151/1125899906842624000000000000000000), (-469814106315982862823522872803/1407374883553280000000000000000000), (-3998815202536144407385755541/87960930222080000000000000000000), (9513012885917971402067860641/562949953421312000000000000000000), (20579817305572437068128695959/11258999068426240000000000000000000), (-4237094387285538374893085451/11258999068426240000000000000000000), (-104284549121941452216964039/2814749767106560000000000000000000), (2030757427011105200064847/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial152.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial152.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial152.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 7741443998091878352127108135795222), (Int.ofNat 748288453151429788151417985755844), (Int.negOfNat 7151475572804022094917084496753), (Int.ofNat 258416232459911991891321578242), (Int.ofNat 1222845577711498079325550865232), (Int.ofNat 22265194173164160536119781502), (Int.negOfNat 42044287876064065882209677495), (Int.negOfNat 1523409344520763383760140031), (Int.ofNat 702069745984445623084082404), (Int.ofNat 32715459154029983573262451), (Int.negOfNat 6654543084315889377031798), (Int.negOfNat 355508421991557116188228), (Int.ofNat 39959382874687521236760), (Int.ofNat 2332340667770787355016), (Int.negOfNat 166297841327096416998), (Int.negOfNat 10457343509743382628), (Int.ofNat 709195108102572885), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(3870721999045939176063554067897611/5629499534213120000000000000000000), (187072113287857447037854496438961/2814749767106560000000000000000000), (-7151475572804022094917084496753/11258999068426240000000000000000000), (129208116229955995945660789121/5629499534213120000000000000000000), (76427848606968629957846929077/703687441776640000000000000000000), (11132597086582080268059890751/5629499534213120000000000000000000), (-8408857575212813176441935499/2251799813685248000000000000000000), (-1523409344520763383760140031/11258999068426240000000000000000000), (175517436496111405771020601/2814749767106560000000000000000000), (32715459154029983573262451/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial152.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial152.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial152.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 9229063634180283860361189160840394), (Int.ofNat 755698134004420448383840118311682), (Int.ofNat 15739364707426571173857093171347), (Int.ofNat 4673393403738242829439043845238), (Int.negOfNat 684219101231392249715362024927), (Int.negOfNat 289302832874209173836976294068), (Int.ofNat 12355175030862919851681779581), (Int.ofNat 7337518625193417611977225795), (Int.negOfNat 2102852636793846665259232), (Int.negOfNat 94639602025962306069831279), (Int.negOfNat 1922716192476796858997398), (Int.ofNat 712153484122537186543668), (Int.ofNat 22002160748516378728312), (Int.negOfNat 3550097577971890767860), (Int.negOfNat 131827585298926963022), (Int.ofNat 13078249340526619368), (Int.ofNat 546390113298293365), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(4614531817090141930180594580420197/5629499534213120000000000000000000), (377849067002210224191920059155841/5629499534213120000000000000000000), (15739364707426571173857093171347/11258999068426240000000000000000000), (2336696701869121414719521922619/5629499534213120000000000000000000), (-684219101231392249715362024927/11258999068426240000000000000000000), (-72325708218552293459244073517/2814749767106560000000000000000000), (12355175030862919851681779581/11258999068426240000000000000000000), (1467503725038683522395445159/2251799813685248000000000000000000), (-65714144899807708289351/351843720888320000000000000000000), (-94639602025962306069831279/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial152.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial152.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial152.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 10822279800705546210718522350055836), (Int.ofNat 835134792092786541189032577029001), (Int.ofNat 11669214066574912192880124674878), (Int.negOfNat 6797270613027394741067612939240), (Int.negOfNat 1159741543529043180090870487556), (Int.ofNat 290096199573117243532951536066), (Int.ofNat 55771358744941460336774989811), (Int.negOfNat 4276657063612265310936631765), (Int.negOfNat 1097162832572656724903184712), (Int.ofNat 17866925639741900078439889), (Int.ofNat 10717763104518424241521662), (Int.ofNat 69044661638643336537732), (Int.negOfNat 64684282455509673982328), (Int.negOfNat 1127312017347962927260), (Int.ofNat 270315699146362600278), (Int.ofNat 6521331976001739592), (Int.negOfNat 1001017509433969045), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(2705569950176386552679630587513959/2814749767106560000000000000000000), (835134792092786541189032577029001/11258999068426240000000000000000000), (5834607033287456096440062337439/5629499534213120000000000000000000), (-169931765325684868526690323481/281474976710656000000000000000000), (-289935385882260795022717621889/2814749767106560000000000000000000), (145048099786558621766475768033/5629499534213120000000000000000000), (55771358744941460336774989811/11258999068426240000000000000000000), (-855331412722453062187326353/2251799813685248000000000000000000), (-137145354071582090612898089/1407374883553280000000000000000000), (17866925639741900078439889/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial152.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial152.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial152.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 12478336365782124322901531625183644), (Int.ofNat 794104231903281792557951793372371), (Int.negOfNat 24992117085769686374065298466148), (Int.ofNat 347206386126480933046069079205), (Int.ofNat 2871898041151384985049481848559), (Int.ofNat 226434505396289718639756108904), (Int.negOfNat 81800269578522233460855417665), (Int.negOfNat 10243552642984433031387956399), (Int.ofNat 740475092353712809632063724), (Int.ofNat 138768183953048200995513739), (Int.negOfNat 2927366328267784530865338), (Int.negOfNat 1033280189299535451116572), (Int.ofNat 1424977482047744123720), (Int.ofNat 5100046483376251038304), (Int.ofNat 43834325369877318102), (Int.negOfNat 18855653118568666932), (Int.negOfNat 337584796160231925), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(3119584091445531080725382906295911/2814749767106560000000000000000000), (794104231903281792557951793372371/11258999068426240000000000000000000), (-6248029271442421593516324616537/2814749767106560000000000000000000), (69441277225296186609213815841/2251799813685248000000000000000000), (2871898041151384985049481848559/11258999068426240000000000000000000), (28304313174536214829969513613/1407374883553280000000000000000000), (-16360053915704446692171083533/2251799813685248000000000000000000), (-10243552642984433031387956399/11258999068426240000000000000000000), (185118773088428202408015931/2814749767106560000000000000000000), (138768183953048200995513739/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial152.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial152.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial152.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 14016259438030732132645475038552209), (Int.ofNat 789074622901275056956136043974550), (Int.ofNat 39520168176388898862204360064216), (Int.ofNat 15541328555464176017063940977481), (Int.negOfNat 1332072662105244329569395335829), (Int.negOfNat 1056484633842298037601420362118), (Int.negOfNat 72946855875434736414945034471), (Int.ofNat 13905097723335021993068897421), (Int.ofNat 1561743128778438980754282724), (Int.negOfNat 89410664822249497663744185), (Int.negOfNat 14685864701540740890170594), (Int.ofNat 323350749185237838653296), (Int.ofNat 85949800192360095318396), (Int.negOfNat 561217351994544228900), (Int.negOfNat 354986226648454937870), (Int.negOfNat 751368950078384876), (Int.ofNat 1188437252196334485), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(14016259438030732132645475038552209/11258999068426240000000000000000000), (15781492458025501139122720879491/225179981368524800000000000000000), (4940021022048612357775545008027/1407374883553280000000000000000000), (15541328555464176017063940977481/11258999068426240000000000000000000), (-1332072662105244329569395335829/11258999068426240000000000000000000), (-528242316921149018800710181059/5629499534213120000000000000000000), (-72946855875434736414945034471/11258999068426240000000000000000000), (13905097723335021993068897421/11258999068426240000000000000000000), (390435782194609745188570681/2814749767106560000000000000000000), (-17882132964449899532748837/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial152.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial152.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial152.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 15819150561407154105199834034368719), (Int.ofNat 1000053545370736297561508492320932), (Int.ofNat 10348757489642578510884189482074), (Int.negOfNat 39143968431555671813226656449744), (Int.negOfNat 11165045189260690464196477322418), (Int.negOfNat 345102953281085213075532999892), (Int.ofNat 196685900961196712510991062453), (Int.ofNat 15592994676661698645509759079), (Int.negOfNat 1671737118420243996443170968), (Int.negOfNat 188461756691679840903346211), (Int.ofNat 8649553290620174734586054), (Int.ofNat 1314110916239465066789708), (Int.negOfNat 29560586242834988913704), (Int.negOfNat 6259285034336979129888), (Int.ofNat 67149717693347419778), (Int.ofNat 22372092664147272632), (Int.negOfNat 37885992691861275), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(15819150561407154105199834034368719/11258999068426240000000000000000000), (250013386342684074390377123080233/2814749767106560000000000000000000), (5174378744821289255442094741037/5629499534213120000000000000000000), (-2446498026972229488326666028109/703687441776640000000000000000000), (-5582522594630345232098238661209/5629499534213120000000000000000000), (-86275738320271303268883249973/2814749767106560000000000000000000), (196685900961196712510991062453/11258999068426240000000000000000000), (15592994676661698645509759079/11258999068426240000000000000000000), (-208967139802530499555396371/1407374883553280000000000000000000), (-188461756691679840903346211/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial152.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial152.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial152.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 17371887638886130079861190035886837), (Int.ofNat 229492592893688288167255716958139), (Int.negOfNat 466131755684266300687576392269591), (Int.negOfNat 105892257455496804756890544922394), (Int.negOfNat 915255770411369272401947174335), (Int.ofNat 2299743582170862315111707411642), (Int.ofNat 146580456307136213551122742875), (Int.negOfNat 24423591068026165119765843705), (Int.negOfNat 2234325031556820870695628076), (Int.ofNat 160881905910406422901522161), (Int.ofNat 18441278795940014032064514), (Int.negOfNat 728638588442855106475720), (Int.negOfNat 101297114393967376926304), (Int.ofNat 2407598085478036643140), (Int.ofNat 404184389482162719598), (Int.negOfNat 5583249025614374140), (Int.negOfNat 1250700065341335525), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(17371887638886130079861190035886837/11258999068426240000000000000000000), (229492592893688288167255716958139/11258999068426240000000000000000000), (-466131755684266300687576392269591/11258999068426240000000000000000000), (-52946128727748402378445272461197/5629499534213120000000000000000000), (-183051154082273854480389434867/2251799813685248000000000000000000), (1149871791085431157555853705821/5629499534213120000000000000000000), (1172643650457089708408981943/90071992547409920000000000000000), (-4884718213605233023953168741/2251799813685248000000000000000000), (-558581257889205217673907019/2814749767106560000000000000000000), (160881905910406422901522161/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial152.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial152.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial152.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 15183937761243020399715920167480287), (Int.negOfNat 2735681920572566321635141110659275), (Int.negOfNat 923782255941222953766876529156095), (Int.negOfNat 14345847720146078824457696547645), (Int.ofNat 22390140428594629637534660672810), (Int.ofNat 1448563150667938460611904187143), (Int.negOfNat 291466884387427511392611243849), (Int.negOfNat 25291415595850345632425892095), (Int.ofNat 2384989692888572303608939040), (Int.ofNat 240970396537481433889332747), (Int.negOfNat 13498848343802240888820450), (Int.negOfNat 1514821266601158251811876), (Int.ofNat 56164199771410392870076), (Int.ofNat 6845593133315293993736), (Int.negOfNat 178854348505631069070), (Int.negOfNat 23426902159475257692), (Int.ofNat 413356781543954475), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(15183937761243020399715920167480287/11258999068426240000000000000000000), (-109427276822902652865405644426371/450359962737049600000000000000000), (-184756451188244590753375305831219/2251799813685248000000000000000000), (-2869169544029215764891539309529/2251799813685248000000000000000000), (2239014042859462963753466067281/1125899906842624000000000000000000), (1448563150667938460611904187143/11258999068426240000000000000000000), (-291466884387427511392611243849/11258999068426240000000000000000000), (-5058283119170069126485178419/2251799813685248000000000000000000), (14906185580553576897555869/70368744177664000000000000000000), (240970396537481433889332747/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial152.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial152.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial152.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 6286100491948142225479780598845165), (Int.negOfNat 5834970800189049036476179272364996), (Int.negOfNat 438365870817812843839905184333270), (Int.ofNat 167226094291930241353354121938955), (Int.ofNat 15712911685409769900268249437506), (Int.negOfNat 2765192546144332748095607148746), (Int.negOfNat 279614575704257558591496989123), (Int.ofNat 28672772687039089637385568509), (Int.ofNat 2968333965390204873325628264), (Int.negOfNat 203068108775552414947500393), (Int.negOfNat 21083730718704292499629698), (Int.ofNat 1042378830560707241775608), (Int.ofNat 107389350338673218448748), (Int.negOfNat 4050064728735290345040), (Int.negOfNat 411771470362675754470), (Int.ofNat 12082638563039077956), (Int.ofNat 1312962878486336565), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(1257220098389628445095956119769033/2251799813685248000000000000000000), (-1458742700047262259119044818091249/2814749767106560000000000000000000), (-43836587081781284383990518433327/1125899906842624000000000000000000), (33445218858386048270670824387791/2251799813685248000000000000000000), (7856455842704884950134124718753/5629499534213120000000000000000000), (-1382596273072166374047803574373/5629499534213120000000000000000000), (-279614575704257558591496989123/11258999068426240000000000000000000), (28672772687039089637385568509/11258999068426240000000000000000000), (371041745673775609165703533/1407374883553280000000000000000000), (-203068108775552414947500393/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial152.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial152.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial152.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 5650163761706618767307710258603648), (Int.negOfNat 5338486100342408198898252770020770), (Int.ofNat 677222232640336168070640268920092), (Int.ofNat 157598482703539007567822842250715), (Int.negOfNat 18409336688424226573637269364337), (Int.negOfNat 2921645669787114759518424485163), (Int.ofNat 267550576024960148331017385549), (Int.ofNat 34310615773509496924950267867), (Int.negOfNat 2487642289080096534175922076), (Int.negOfNat 273604237381136826490844915), (Int.ofNat 16054586079491164980107110), (Int.ofNat 1564810274475365676300588), (Int.negOfNat 75948724186035127286336), (Int.negOfNat 6692083244054191022144), (Int.ofNat 273925846312084648838), (Int.ofNat 21784276426997431288), (Int.negOfNat 809581841444381355), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-44141904388332959119591486395341/87960930222080000000000000000000), (-533848610034240819889825277002077/1125899906842624000000000000000000), (169305558160084042017660067230023/2814749767106560000000000000000000), (31519696540707801513564568450143/2251799813685248000000000000000000), (-18409336688424226573637269364337/11258999068426240000000000000000000), (-2921645669787114759518424485163/11258999068426240000000000000000000), (267550576024960148331017385549/11258999068426240000000000000000000), (34310615773509496924950267867/11258999068426240000000000000000000), (-621910572270024133543980519/2814749767106560000000000000000000), (-54720847476227365298168983/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial152.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial152.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial152.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial152.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial152.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial152.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial152.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial152.reflect := by
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

end Bin152
end
end ErdosOverlap.OuterNumerics
