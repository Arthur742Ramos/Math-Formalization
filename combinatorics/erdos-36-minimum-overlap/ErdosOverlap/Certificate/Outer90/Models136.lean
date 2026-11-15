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

/-! # Exact integer weighted outer models for source bin 136

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin136

def weightDenominator : ℤ := (Int.ofNat 5000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 1744130157148015850)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1577378302247259500)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 1127687052187552500)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 643405305486954300)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 334807193158226250)⟩, ⟨(19494472361809/1000000000000), (Int.negOfNat 262070381947481900)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 405316039084053650)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 162699875950474250)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 34425268798765250)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial136.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial136.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 4897684560859188000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 818183748723789200)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 840104712411675750)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 289938016136290700)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 50167317019744800)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 76991953954908795)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 51718459228665710)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 7758402149209972)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 2028033040861470)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial136.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial136.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4897684560859188000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 818183748723789200)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 840104712411675750)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 289938016136290700)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 50167317019744800)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 76991953954908795)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 51718459228665710)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 7758402149209972)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 2028033040861470)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial136.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial136.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial136.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 5343169854044776290796670095846354), (Int.ofNat 2264448185610283802931664099838409), (Int.ofNat 469073133137010253539215425363042), (Int.negOfNat 67366300834289704770031224525006), (Int.negOfNat 11815341283285457897613219756349), (Int.ofNat 1253037205029989757988001219324), (Int.ofNat 162535831994613751979318672419), (Int.negOfNat 14289961061247337639627267476), (Int.negOfNat 1406855088682213004952987994), (Int.ofNat 108171392887662653199554288), (Int.ofNat 8372327184890291582994568), (Int.negOfNat 582374731866236587699565), (Int.negOfNat 36547924320163076401987), (Int.ofNat 2347447263174136497909), (Int.ofNat 122256881916849696530), (Int.negOfNat 7187138372850534382), (Int.negOfNat 314899619549921708), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-2671584927022388145398335047923177/2814749767106560000000000000000000), (2264448185610283802931664099838409/5629499534213120000000000000000000), (234536566568505126769607712681521/2814749767106560000000000000000000), (-33683150417144852385015612262503/2814749767106560000000000000000000), (-11815341283285457897613219756349/5629499534213120000000000000000000), (313259301257497439497000304831/1407374883553280000000000000000000), (162535831994613751979318672419/5629499534213120000000000000000000), (-3572490265311834409906816869/1407374883553280000000000000000000), (-703427544341106502476493997/2814749767106560000000000000000000), (6760712055478915824972143/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial136.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial136.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial136.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial136 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 382416032000533872025872877047009), (Int.ofNat 3078146293309484898661946068386590), (Int.negOfNat 90988777625611791221451074887373), (Int.negOfNat 95603096229732478735618508857095), (Int.ofNat 5410716679167393840231427954763), (Int.ofNat 1638376760164400006252334521081), (Int.negOfNat 104451419294341685707221160656), (Int.negOfNat 16888672183687161127913421569), (Int.ofNat 1102424081498965854069497431), (Int.ofNat 115176641902279978623902552), (Int.negOfNat 7575996724898664127790147), (Int.negOfNat 559690339155890705981990), (Int.ofNat 37044217530074877656973), (Int.ofNat 2048447782912499199056), (Int.negOfNat 136311230032571186350), (Int.negOfNat 5674186159760750928), (Int.ofNat 419547291854486852), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(382416032000533872025872877047009/5629499534213120000000000000000000), (307814629330948489866194606838659/562949953421312000000000000000000), (-90988777625611791221451074887373/5629499534213120000000000000000000), (-19120619245946495747123701771419/1125899906842624000000000000000000), (5410716679167393840231427954763/5629499534213120000000000000000000), (1638376760164400006252334521081/5629499534213120000000000000000000), (-6528213705896355356701322541/351843720888320000000000000000000), (-16888672183687161127913421569/5629499534213120000000000000000000), (1102424081498965854069497431/5629499534213120000000000000000000), (14397080237784997327987819/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial136.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial136.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial136.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial136 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 5540414073652878553581388788713677), (Int.ofNat 1844896463370750586492192966476997), (Int.negOfNat 437691524838117738777439216604774), (Int.negOfNat 10492788910394244081243699708883), (Int.ofNat 12377506659292972976645488088819), (Int.negOfNat 380971965664210925622543972284), (Int.negOfNat 171228119932257983967249544309), (Int.ofNat 8204241642131519977073491476), (Int.ofNat 1421287571739982705525757564), (Int.negOfNat 80817061323629933280987443), (Int.negOfNat 7945317399219094954821448), (Int.ofNat 504951009101199221964550), (Int.ofNat 32235619939172229184552), (Int.negOfNat 2237749574855685134404), (Int.negOfNat 99781755659273186820), (Int.ofNat 7497446074627318652), (Int.ofNat 209595780112764488), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(5540414073652878553581388788713677/5629499534213120000000000000000000), (1844896463370750586492192966476997/5629499534213120000000000000000000), (-218845762419058869388719608302387/2814749767106560000000000000000000), (-10492788910394244081243699708883/5629499534213120000000000000000000), (12377506659292972976645488088819/5629499534213120000000000000000000), (-95242991416052731405635993071/1407374883553280000000000000000000), (-171228119932257983967249544309/5629499534213120000000000000000000), (2051060410532879994268372869/1407374883553280000000000000000000), (355321892934995676381439391/1407374883553280000000000000000000), (-80817061323629933280987443/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial136.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial136.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial136.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial136 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 7571754618406340721629486866322841), (Int.ofNat 305853921428924433306038686335211), (Int.negOfNat 267548331729726007500362267559380), (Int.ofNat 52500941726268022023223756546951), (Int.ofNat 1775004796307369367981900081992), (Int.negOfNat 1319431283198376044158082347361), (Int.ofNat 30633889808531726878325605591), (Int.ofNat 14886460728497749325740293849), (Int.negOfNat 646404297939881577728757951), (Int.negOfNat 101280967804090843237311057), (Int.ofNat 5744452014061249340163282), (Int.ofNat 470199822716980985446650), (Int.negOfNat 32152072874227293113323), (Int.negOfNat 1600662193923175334971), (Int.ofNat 128128589517944591845), (Int.ofNat 3870783764980900668), (Int.negOfNat 413463192731902442), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(7571754618406340721629486866322841/5629499534213120000000000000000000), (305853921428924433306038686335211/5629499534213120000000000000000000), (-13377416586486300375018113377969/281474976710656000000000000000000), (52500941726268022023223756546951/5629499534213120000000000000000000), (221875599538421170997737510249/703687441776640000000000000000000), (-1319431283198376044158082347361/5629499534213120000000000000000000), (30633889808531726878325605591/5629499534213120000000000000000000), (14886460728497749325740293849/5629499534213120000000000000000000), (-646404297939881577728757951/5629499534213120000000000000000000), (-101280967804090843237311057/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial136.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial136.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial136.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial136 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 7523110347087714774264376472849328), (Int.negOfNat 171393034025479893254415912909383), (Int.ofNat 310745833808205681108267751401), (Int.ofNat 25562833214290232768876479569337), (Int.negOfNat 6452856961598794872308361795146), (Int.negOfNat 138553622765461057442253370801), (Int.ofNat 122691978045007230359575071859), (Int.negOfNat 2973010256499989530286913731), (Int.negOfNat 1108639618655924741798626119), (Int.ofNat 51102010256812686683257723), (Int.ofNat 6182754934761546806606228), (Int.negOfNat 393524513966419967651760), (Int.negOfNat 23760822667238635801617), (Int.ofNat 1940945885268636532219), (Int.ofNat 66794024207526533385), (Int.negOfNat 7158798661412294812), (Int.negOfNat 106319973716468738), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(470194396692982173391523529553083/351843720888320000000000000000000), (-171393034025479893254415912909383/5629499534213120000000000000000000), (310745833808205681108267751401/5629499534213120000000000000000000), (25562833214290232768876479569337/5629499534213120000000000000000000), (-3226428480799397436154180897573/2814749767106560000000000000000000), (-138553622765461057442253370801/5629499534213120000000000000000000), (122691978045007230359575071859/5629499534213120000000000000000000), (-2973010256499989530286913731/5629499534213120000000000000000000), (-1108639618655924741798626119/5629499534213120000000000000000000), (51102010256812686683257723/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial136.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial136.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial136.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial136 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 7285610039174704263274847762795692), (Int.negOfNat 59737573133349923535481027236437), (Int.ofNat 13490762492923067557804316811683), (Int.negOfNat 15272021414662645059150466175430), (Int.negOfNat 2280728755588095244617885223420), (Int.ofNat 726867457182493928059066830926), (Int.ofNat 5253105582151533003812927499), (Int.negOfNat 9866426671527860285965044714), (Int.ofNat 303319448469675300419596826), (Int.ofNat 70550062786137413754511317), (Int.negOfNat 3924295273132281922689592), (Int.negOfNat 318972911463885724099520), (Int.ofNat 25531723387630996371458), (Int.ofNat 987184760590624581056), (Int.negOfNat 109841424159790388000), (Int.negOfNat 2039091493420749308), (Int.ofNat 407379093609318032), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(1821402509793676065818711940698923/1407374883553280000000000000000000), (-59737573133349923535481027236437/5629499534213120000000000000000000), (13490762492923067557804316811683/5629499534213120000000000000000000), (-1527202141466264505915046617543/562949953421312000000000000000000), (-114036437779404762230894261171/281474976710656000000000000000000), (363433728591246964029533415463/2814749767106560000000000000000000), (5253105582151533003812927499/5629499534213120000000000000000000), (-4933213335763930142982522357/2814749767106560000000000000000000), (151659724234837650209798413/2814749767106560000000000000000000), (70550062786137413754511317/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial136.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial136.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial136.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial136 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 7083872376743297886650347103633095), (Int.negOfNat 206834138349501835530568006366701), (Int.negOfNat 79282658760700660668701888098006), (Int.negOfNat 8275699372811849944151843740973), (Int.ofNat 3101973315556129674343574453726), (Int.ofNat 200961652663731362671651778411), (Int.negOfNat 67757074513894138645335412044), (Int.ofNat 400191968767517144816407031), (Int.ofNat 666957779960456028605408069), (Int.negOfNat 29092597491855339021911328), (Int.negOfNat 3730838838323378742054733), (Int.ofNat 282734904142743393450510), (Int.ofNat 13143650297530859255077), (Int.negOfNat 1540961249431705792704), (Int.negOfNat 29136795111175639810), (Int.ofNat 5873631556356207012), (Int.ofNat 3044167320172988), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(1416774475348659577330069420726619/1125899906842624000000000000000000), (-206834138349501835530568006366701/5629499534213120000000000000000000), (-39641329380350330334350944049003/2814749767106560000000000000000000), (-8275699372811849944151843740973/5629499534213120000000000000000000), (1550986657778064837171787226863/2814749767106560000000000000000000), (200961652663731362671651778411/5629499534213120000000000000000000), (-16939268628473534661333853011/1407374883553280000000000000000000), (400191968767517144816407031/5629499534213120000000000000000000), (666957779960456028605408069/5629499534213120000000000000000000), (-909143671620479344434729/175921860444160000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial136.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial136.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial136.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial136 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 6338797633123867148441140525142743), (Int.negOfNat 520162902573156346672378697349052), (Int.negOfNat 53378583681081681553072268171943), (Int.ofNat 14955970552313869462118954082441), (Int.ofNat 1750798252699725306609761004180), (Int.negOfNat 359273918624692256467302404358), (Int.negOfNat 14930087124506947702963577149), (Int.ofNat 4953795697411830750029015204), (Int.negOfNat 115390518873256215974618616), (Int.negOfNat 36085852461328446032180482), (Int.ofNat 2495650036727466632134082), (Int.ofNat 150307841279340612646315), (Int.negOfNat 18625143023889015398993), (Int.negOfNat 343808964127174842401), (Int.ofNat 84701494168733696110), (Int.ofNat 49195456386365198), (Int.negOfNat 366869725687968372), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(6338797633123867148441140525142743/5629499534213120000000000000000000), (-130040725643289086668094674337263/1407374883553280000000000000000000), (-53378583681081681553072268171943/5629499534213120000000000000000000), (14955970552313869462118954082441/5629499534213120000000000000000000), (87539912634986265330488050209/281474976710656000000000000000000), (-179636959312346128233651202179/2814749767106560000000000000000000), (-14930087124506947702963577149/5629499534213120000000000000000000), (1238448924352957687507253801/1407374883553280000000000000000000), (-14423814859157026996827327/703687441776640000000000000000000), (-18042926230664223016090241/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial136.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial136.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial136.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial136 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 5220754594313236091770215022052005), (Int.negOfNat 527756533624952067310990307905735), (Int.ofNat 49038850747305964395710441848098), (Int.ofNat 14618480122402367949811751242032), (Int.negOfNat 1587928805691122024731710308503), (Int.negOfNat 224107081788270408186905281056), (Int.ofNat 26743839430291542377688335899), (Int.ofNat 626925717545999659781866934), (Int.negOfNat 263362520420884452084593374), (Int.ofNat 15305051599231698119423898), (Int.ofNat 1346690829264135856632788), (Int.negOfNat 187342549103652251025005), (Int.negOfNat 2964302907557481978687), (Int.ofNat 1101487983302614218959), (Int.negOfNat 4846447120812525270), (Int.negOfNat 4528495864614962202), (Int.ofNat 61750304195634572), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(1044150918862647218354043004410401/1125899906842624000000000000000000), (-105551306724990413462198061581147/1125899906842624000000000000000000), (24519425373652982197855220924049/2814749767106560000000000000000000), (913655007650147996863234452627/351843720888320000000000000000000), (-1587928805691122024731710308503/5629499534213120000000000000000000), (-7003346305883450255840790033/175921860444160000000000000000000), (26743839430291542377688335899/5629499534213120000000000000000000), (313462858772999829890933467/2814749767106560000000000000000000), (-131681260210442226042296687/2814749767106560000000000000000000), (7652525799615849059711949/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial136.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial136.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial136.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial136 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 4447499743119366535142786680922515), (Int.negOfNat 219735628924024991606937221907982), (Int.ofNat 87159477774200403282926315599776), (Int.negOfNat 2796057272643124808828597844062), (Int.negOfNat 2271888624492152752239630118263), (Int.ofNat 67714792168086825377315241988), (Int.ofNat 18117143552167129287196880164), (Int.negOfNat 1042036969188519977564320139), (Int.ofNat 25018363787062597572821301), (Int.ofNat 6887615598383103006736552), (Int.negOfNat 1466745009520982944437477), (Int.negOfNat 5296622450756639565290), (Int.ofNat 12141182807860935205023), (Int.negOfNat 194838986865905609464), (Int.negOfNat 57350634500657715130), (Int.ofNat 1495148826409052392), (Int.ofNat 293963122008714932), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(889499948623873307028557336184503/1125899906842624000000000000000000), (-109867814462012495803468610953991/2814749767106560000000000000000000), (2723733680443762602591447362493/175921860444160000000000000000000), (-1398028636321562404414298922031/2814749767106560000000000000000000), (-2271888624492152752239630118263/5629499534213120000000000000000000), (16928698042021706344328810497/1407374883553280000000000000000000), (4529285888041782321799220041/1407374883553280000000000000000000), (-1042036969188519977564320139/5629499534213120000000000000000000), (25018363787062597572821301/5629499534213120000000000000000000), (860951949797887875842069/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial136.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial136.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial136.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial136 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 4301149175621160947421771253168008), (Int.ofNat 31112201651536959890553241472576), (Int.ofNat 24983150767753471505697921546887), (Int.negOfNat 15886993260256477789256888851581), (Int.negOfNat 762214078267801126698605106780), (Int.ofNat 211812382295367867931480440006), (Int.ofNat 6588709280821419301080474271), (Int.negOfNat 821546537314378333593441364), (Int.negOfNat 43195645015077281617333446), (Int.negOfNat 7460873062871715477148523), (Int.ofNat 472585739784549042839312), (Int.ofNat 109736636375183343463980), (Int.negOfNat 4673195901340218556858), (Int.negOfNat 667093907522965782884), (Int.ofNat 29764606457728908220), (Int.ofNat 2540635093994836012), (Int.negOfNat 90091473871815412), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(537643646952645118427721406646001/703687441776640000000000000000000), (486128150805264998289894398009/87960930222080000000000000000000), (24983150767753471505697921546887/5629499534213120000000000000000000), (-15886993260256477789256888851581/5629499534213120000000000000000000), (-38110703913390056334930255339/281474976710656000000000000000000), (105906191147683933965740220003/2814749767106560000000000000000000), (6588709280821419301080474271/5629499534213120000000000000000000), (-205386634328594583398360341/1407374883553280000000000000000000), (-21597822507538640808666723/2814749767106560000000000000000000), (-7460873062871715477148523/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial136.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial136.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial136.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial136 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 4331095132898784608549772858300165), (Int.negOfNat 66205907902530062858749344358882), (Int.negOfNat 70761406544527938227763164104551), (Int.negOfNat 13024400873531050410253605528897), (Int.ofNat 1452924680241600334629962700186), (Int.ofNat 193873147584425579400607335357), (Int.negOfNat 11949129797976941481970082079), (Int.negOfNat 1729309607854362845120395641), (Int.negOfNat 4754293773460582234425361), (Int.ofNat 12773405882101726796436313), (Int.ofNat 769548635782622595716982), (Int.negOfNat 89763160589990655677500), (Int.negOfNat 6436623884819952769843), (Int.ofNat 529977860179625168659), (Int.ofNat 29802024695619262495), (Int.negOfNat 2577512627378993192), (Int.negOfNat 190687315612419182), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(866219026579756921709954571660033/1125899906842624000000000000000000), (-33102953951265031429374672179441/2814749767106560000000000000000000), (-70761406544527938227763164104551/5629499534213120000000000000000000), (-13024400873531050410253605528897/5629499534213120000000000000000000), (726462340120800167314981350093/2814749767106560000000000000000000), (193873147584425579400607335357/5629499534213120000000000000000000), (-11949129797976941481970082079/5629499534213120000000000000000000), (-1729309607854362845120395641/5629499534213120000000000000000000), (-4754293773460582234425361/5629499534213120000000000000000000), (12773405882101726796436313/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial136.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial136.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial136.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial136 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 3839913029053685290088629390619277), (Int.negOfNat 446582503217410070072431878182667), (Int.negOfNat 102501318544516157526582591448730), (Int.ofNat 3541274990831968391404288055100), (Int.ofNat 2242632383563434006998227320005), (Int.negOfNat 68060683782480170694693271451), (Int.negOfNat 27097395879363594700885939721), (Int.ofNat 202757889525370571170775359), (Int.ofNat 219642864584715077732712191), (Int.ofNat 4222748384623307793247733), (Int.negOfNat 1468106124693521998223882), (Int.negOfNat 50080424263999771478190), (Int.ofNat 8534744584089459162283), (Int.ofNat 274081578162962089609), (Int.negOfNat 40147964819411343825), (Int.negOfNat 792099410483401372), (Int.ofNat 84007374749231002), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(3839913029053685290088629390619277/5629499534213120000000000000000000), (-446582503217410070072431878182667/5629499534213120000000000000000000), (-10250131854451615752658259144873/562949953421312000000000000000000), (35412749908319683914042880551/56294995342131200000000000000000), (448526476712686801399645464001/1125899906842624000000000000000000), (-68060683782480170694693271451/5629499534213120000000000000000000), (-27097395879363594700885939721/5629499534213120000000000000000000), (202757889525370571170775359/5629499534213120000000000000000000), (219642864584715077732712191/5629499534213120000000000000000000), (4222748384623307793247733/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial136.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial136.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial136.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial136 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 2597125665528032175142129250011038), (Int.negOfNat 752658178182352469984191006005124), (Int.negOfNat 38847127270599253750359226381496), (Int.ofNat 14930514100358138564523751085633), (Int.ofNat 235272186111503026378161988914), (Int.negOfNat 281691840760423189563828429332), (Int.negOfNat 1961707750449518663729330341), (Int.ofNat 2879277570586882641880929916), (Int.ofNat 36119250257629528734377626), (Int.negOfNat 20671205299524853146842313), (Int.negOfNat 350406440024602224811662), (Int.ofNat 122869660326671521906690), (Int.ofNat 1802587619987673364768), (Int.negOfNat 615100850411901789784), (Int.negOfNat 5158794522031592580), (Int.ofNat 2443174222396942252), (Int.ofNat 87411509216123432), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(1298562832764016087571064625005519/2814749767106560000000000000000000), (-188164544545588117496047751501281/1407374883553280000000000000000000), (-4855890908824906718794903297687/703687441776640000000000000000000), (14930514100358138564523751085633/5629499534213120000000000000000000), (117636093055751513189080994457/2814749767106560000000000000000000), (-70422960190105797390957107333/1407374883553280000000000000000000), (-1961707750449518663729330341/5629499534213120000000000000000000), (719819392646720660470232479/1407374883553280000000000000000000), (18059625128814764367188813/2814749767106560000000000000000000), (-20671205299524853146842313/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial136.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial136.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial136.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial136 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 1050856685224032066415001097990596), (Int.negOfNat 742984925751182161072110995225427), (Int.ofNat 35280127119299347850211440012048), (Int.ofNat 6796968954275008816045132072664), (Int.negOfNat 1935558214611491731522697139498), (Int.negOfNat 88074980664170277255580511549), (Int.ofNat 29115472184726538173861190956), (Int.ofNat 772789587099410090803025391), (Int.negOfNat 246901461336279821155338171), (Int.negOfNat 4078593293940330746687688), (Int.ofNat 1563185841839537887876327), (Int.ofNat 8627439515614294655570), (Int.negOfNat 8270553376061819996113), (Int.ofNat 43602773010751590196), (Int.ofNat 36363772304005722310), (Int.negOfNat 847025074613273368), (Int.negOfNat 77923275626646592), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(262714171306008016603750274497649/1407374883553280000000000000000000), (-742984925751182161072110995225427/5629499534213120000000000000000000), (2205007944956209240638215000753/351843720888320000000000000000000), (849621119284376102005641509083/703687441776640000000000000000000), (-967779107305745865761348569749/2814749767106560000000000000000000), (-88074980664170277255580511549/5629499534213120000000000000000000), (7278868046181634543465297739/1407374883553280000000000000000000), (772789587099410090803025391/5629499534213120000000000000000000), (-246901461336279821155338171/5629499534213120000000000000000000), (-509824161742541343335961/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial136.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial136.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial136.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial136 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 271505639282213293741248715235111), (Int.negOfNat 583602591167318132884455635317440), (Int.ofNat 29626043384929139925082216001613), (Int.negOfNat 7560150360042050129894243353197), (Int.negOfNat 1125596468532126915621285096476), (Int.ofNat 219462062717385094280782660242), (Int.ofNat 14466892510128065607982494371), (Int.negOfNat 2409034196260508858948111276), (Int.negOfNat 85035366176886418745279986), (Int.ofNat 17040412163609898135067958), (Int.ofNat 150259506666488796782692), (Int.negOfNat 95489408584722175500345), (Int.ofNat 1453887687650053805987), (Int.ofNat 454072237158748693749), (Int.negOfNat 13379208479124148370), (Int.negOfNat 1842850562403571322), (Int.ofNat 13836264139310848), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-271505639282213293741248715235111/5629499534213120000000000000000000), (-1823758097397869165263923860367/17592186044416000000000000000000), (29626043384929139925082216001613/5629499534213120000000000000000000), (-7560150360042050129894243353197/5629499534213120000000000000000000), (-281399117133031728905321274119/1407374883553280000000000000000000), (109731031358692547140391330121/2814749767106560000000000000000000), (14466892510128065607982494371/5629499534213120000000000000000000), (-602258549065127214737027819/1407374883553280000000000000000000), (-42517683088443209372639993/2814749767106560000000000000000000), (8520206081804949067533979/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial136.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial136.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial136.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial136 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 1391070160373670734381757578994399), (Int.negOfNat 572632011366804055348707061646599), (Int.negOfNat 23413680805292957539013889117863), (Int.negOfNat 6883012351967114343388897662655), (Int.ofNat 1234293003639112084852930130448), (Int.ofNat 185629475462670404573990591034), (Int.negOfNat 18068322093773620427174338171), (Int.negOfNat 1597676388515936032535095226), (Int.ofNat 148997137078270834511831136), (Int.ofNat 5440741914541234829746458), (Int.negOfNat 879954422851998932986292), (Int.ofNat 13784366463732112660155), (Int.ofNat 4380799655722378880413), (Int.negOfNat 251743502444422887651), (Int.negOfNat 19096223045712154730), (Int.ofNat 1732473473660639278), (Int.ofNat 5016671947393152), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-1391070160373670734381757578994399/5629499534213120000000000000000000), (-572632011366804055348707061646599/5629499534213120000000000000000000), (-23413680805292957539013889117863/5629499534213120000000000000000000), (-1376602470393422868677779532531/1125899906842624000000000000000000), (77143312727444505303308133153/351843720888320000000000000000000), (92814737731335202286995295517/2814749767106560000000000000000000), (-18068322093773620427174338171/5629499534213120000000000000000000), (-798838194257968016267547613/2814749767106560000000000000000000), (4656160533695963578494723/175921860444160000000000000000000), (2720370957270617414873229/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial136.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial136.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial136.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial136 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 2660684977359765190796754824187484), (Int.negOfNat 698559174635801597387137189330096), (Int.negOfNat 25365825645068575072515073796248), (Int.ofNat 6914607259592987001698329740726), (Int.ofNat 1737156421657009784241783641371), (Int.negOfNat 94017800809417562840856990332), (Int.negOfNat 22651552739796490055108282756), (Int.ofNat 875453455593450480337054141), (Int.ofNat 128750211251730579134808171), (Int.negOfNat 4986278151867209675619588), (Int.negOfNat 140968587948057674437227), (Int.ofNat 21576831325789622873870), (Int.negOfNat 2988163276055300461987), (Int.negOfNat 95827380496095972204), (Int.ofNat 24649082609538258290), (Int.ofNat 716058998120294032), (Int.negOfNat 78630735655118408), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-665171244339941297699188706046871/1407374883553280000000000000000000), (-43659948414737599836696074333131/351843720888320000000000000000000), (-3170728205633571884064384224531/703687441776640000000000000000000), (3457303629796493500849164870363/2814749767106560000000000000000000), (1737156421657009784241783641371/5629499534213120000000000000000000), (-23504450202354390710214247583/1407374883553280000000000000000000), (-5662888184949122513777070689/1407374883553280000000000000000000), (875453455593450480337054141/5629499534213120000000000000000000), (128750211251730579134808171/5629499534213120000000000000000000), (-1246569537966802418904897/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial136.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial136.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial136.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial136 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 4080471185045201477885752651001771), (Int.negOfNat 672816706210452830161756288602940), (Int.ofNat 45650599341521890874838250531716), (Int.ofNat 14119466348779386354605351249846), (Int.negOfNat 194263572301762557352618003756), (Int.negOfNat 245478300378187588642736535206), (Int.ofNat 340759162686964214626669591), (Int.ofNat 2120665051315971838156986966), (Int.ofNat 19223845528757982764138374), (Int.negOfNat 7856082015257819359837763), (Int.negOfNat 293622185707649124292088), (Int.negOfNat 13852785145782144889410), (Int.ofNat 1979419333314943334532), (Int.ofNat 317257544447932267816), (Int.negOfNat 7974459788654004420), (Int.negOfNat 2042781175437423548), (Int.ofNat 100287167489764068), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-4080471185045201477885752651001771/5629499534213120000000000000000000), (-33640835310522641508087814430147/281474976710656000000000000000000), (11412649835380472718709562632929/1407374883553280000000000000000000), (7059733174389693177302675624923/2814749767106560000000000000000000), (-48565893075440639338154500939/1407374883553280000000000000000000), (-122739150189093794321368267603/2814749767106560000000000000000000), (340759162686964214626669591/5629499534213120000000000000000000), (1060332525657985919078493483/2814749767106560000000000000000000), (9611922764378991382069187/2814749767106560000000000000000000), (-7856082015257819359837763/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial136.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial136.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial136.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial136 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 5141216157900283798399987504830274), (Int.negOfNat 345619937705231930215913759105338), (Int.ofNat 107568332399876870563387836984335), (Int.ofNat 3975745929187372261446468564835), (Int.negOfNat 2049137344255364748885807529073), (Int.negOfNat 72964567028297118150667124663), (Int.ofNat 25888721507662357696659207501), (Int.ofNat 1020685209021517054593116159), (Int.negOfNat 167475735988155850999355741), (Int.negOfNat 10692231600830329526628417), (Int.ofNat 371695235662813355665132), (Int.ofNat 76866562629485267862410), (Int.ofNat 2371213797788885215717), (Int.negOfNat 376264202579121229691), (Int.negOfNat 24831238431879906775), (Int.ofNat 1087343396659556228), (Int.ofNat 72546636532533998), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-2570608078950141899199993752415137/2814749767106560000000000000000000), (-172809968852615965107956879552669/2814749767106560000000000000000000), (21513666479975374112677567396867/1125899906842624000000000000000000), (795149185837474452289293712967/1125899906842624000000000000000000), (-2049137344255364748885807529073/5629499534213120000000000000000000), (-72964567028297118150667124663/5629499534213120000000000000000000), (25888721507662357696659207501/5629499534213120000000000000000000), (1020685209021517054593116159/5629499534213120000000000000000000), (-167475735988155850999355741/5629499534213120000000000000000000), (-10692231600830329526628417/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial136.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial136.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial136.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial136 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 5403758077945079209735609228267212), (Int.ofNat 66187358795868429597230101712824), (Int.ofNat 82962692390672533936080107365371), (Int.negOfNat 10970656882045281615708043323992), (Int.negOfNat 1161967590882409061446841962019), (Int.ofNat 232219048679323338898323135461), (Int.ofNat 16663826078915251451739344729), (Int.negOfNat 2425319310788855598933114691), (Int.negOfNat 191656846331287310881962689), (Int.ofNat 12487973876640277225340563), (Int.ofNat 1602654145260256289473918), (Int.negOfNat 15219015074398155220900), (Int.negOfNat 9348960413610295310857), (Int.negOfNat 209546996021107245941), (Int.ofNat 38529512470788972005), (Int.ofNat 1704133762222399708), (Int.negOfNat 203562973886059818), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-1350939519486269802433902307066803/1407374883553280000000000000000000), (8273419849483553699653762714103/703687441776640000000000000000000), (82962692390672533936080107365371/5629499534213120000000000000000000), (-1371332110255660201963505415499/703687441776640000000000000000000), (-1161967590882409061446841962019/5629499534213120000000000000000000), (232219048679323338898323135461/5629499534213120000000000000000000), (16663826078915251451739344729/5629499534213120000000000000000000), (-2425319310788855598933114691/5629499534213120000000000000000000), (-191656846331287310881962689/5629499534213120000000000000000000), (12487973876640277225340563/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial136.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial136.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial136.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial136 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 5037743373437573029176495191773861), (Int.ofNat 249738032010989366420430363530082), (Int.ofNat 9930036262701574755560886994255), (Int.negOfNat 9923025286522343514368918305166), (Int.ofNat 1336337500934883066402097636643), (Int.ofNat 179272075220087053003106661978), (Int.negOfNat 25770473194549384334643828621), (Int.negOfNat 2476457619550977116627619614), (Int.ofNat 227155935954479975106022846), (Int.ofNat 25133374336588230146316327), (Int.negOfNat 977617471025235191105612), (Int.negOfNat 177280065261435277137720), (Int.ofNat 853653192386161231258), (Int.ofNat 874048826451327670616), (Int.ofNat 13661435505805347480), (Int.negOfNat 2919035668219707588), (Int.negOfNat 66462537409949588), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-5037743373437573029176495191773861/5629499534213120000000000000000000), (124869016005494683210215181765041/2814749767106560000000000000000000), (1986007252540314951112177398851/1125899906842624000000000000000000), (-4961512643261171757184459152583/2814749767106560000000000000000000), (1336337500934883066402097636643/5629499534213120000000000000000000), (89636037610043526501553330989/2814749767106560000000000000000000), (-25770473194549384334643828621/5629499534213120000000000000000000), (-1238228809775488558313809807/2814749767106560000000000000000000), (113577967977239987553011423/2814749767106560000000000000000000), (25133374336588230146316327/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial136.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial136.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial136.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial136 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 4552709890265265550215758349695538), (Int.ofNat 221712636764835082311625999512467), (Int.negOfNat 10536519288699086044613535154011), (Int.ofNat 2948497797956497981702932735958), (Int.ofNat 1224979456999243776226723957196), (Int.negOfNat 198308415708865530380114032631), (Int.negOfNat 23771136669132572213498325064), (Int.ofNat 3020768360179330804810167861), (Int.ofNat 312177218082492193901585299), (Int.negOfNat 22127452385509040246499048), (Int.negOfNat 2758883080742645573795373), (Int.ofNat 82077132555731498474610), (Int.ofNat 16440505020711579370077), (Int.negOfNat 86198921078775488164), (Int.negOfNat 69178194573781185370), (Int.negOfNat 681037039113793808), (Int.ofNat 306838780282355568), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-2276354945132632775107879174847769/2814749767106560000000000000000000), (221712636764835082311625999512467/5629499534213120000000000000000000), (-10536519288699086044613535154011/5629499534213120000000000000000000), (1474248898978248990851466367979/2814749767106560000000000000000000), (306244864249810944056680989299/1407374883553280000000000000000000), (-198308415708865530380114032631/5629499534213120000000000000000000), (-2971392083641571526687290633/703687441776640000000000000000000), (3020768360179330804810167861/5629499534213120000000000000000000), (312177218082492193901585299/5629499534213120000000000000000000), (-2765931548188630030812381/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial136.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial136.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial136.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial136 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 4115657607282884317623504552653572), (Int.ofNat 235328326910409488270833661161224), (Int.ofNat 17443243525331358599654639359277), (Int.ofNat 3107575141396817508540552410640), (Int.negOfNat 1109768726648405520051483062725), (Int.negOfNat 152824361009700120328674323188), (Int.ofNat 31457737414959061038542382251), (Int.ofNat 2991160276552760043003505834), (Int.negOfNat 360805678631139644472207776), (Int.negOfNat 35611684896682529431016102), (Int.ofNat 2133631583705608744369812), (Int.ofNat 265125926763979386946695), (Int.negOfNat 6938487753633797523013), (Int.negOfNat 1329378852246630350641), (Int.ofNat 9389712750476518070), (Int.ofNat 4908931705254091698), (Int.ofNat 25953169488599928), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-1028914401820721079405876138163393/1407374883553280000000000000000000), (29416040863801186033854207645153/703687441776640000000000000000000), (17443243525331358599654639359277/5629499534213120000000000000000000), (38844689267460218856756905133/70368744177664000000000000000000), (-44390749065936220802059322509/225179981368524800000000000000000), (-38206090252425030082168580797/1407374883553280000000000000000000), (31457737414959061038542382251/5629499534213120000000000000000000), (1495580138276380021501752917/2814749767106560000000000000000000), (-11275177457223113889756493/175921860444160000000000000000000), (-17805842448341264715508051/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial136.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial136.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial136.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial136 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 3570725804321643392932289887611060), (Int.ofNat 301595737118828432333493003736492), (Int.ofNat 6008921951012720279505998020063), (Int.negOfNat 5970457167072284698277594548087), (Int.negOfNat 422180056494447591923074850051), (Int.ofNat 266419442627883785214135362976), (Int.ofNat 19398306340972287915765958549), (Int.negOfNat 4771636515809656632143214796), (Int.negOfNat 371838183242473085488578934), (Int.ofNat 40057246651257655328941318), (Int.ofNat 3683255952259165622593318), (Int.negOfNat 191266763014820632324785), (Int.negOfNat 22553293551692797045707), (Int.ofNat 556189965877205154599), (Int.ofNat 95004303131388107190), (Int.negOfNat 664098652627451002), (Int.negOfNat 371633251798163128), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-178536290216082169646614494380553/281474976710656000000000000000000), (75398934279707108083373250934123/1407374883553280000000000000000000), (6008921951012720279505998020063/5629499534213120000000000000000000), (-5970457167072284698277594548087/5629499534213120000000000000000000), (-422180056494447591923074850051/5629499534213120000000000000000000), (8325607582121368287941730093/175921860444160000000000000000000), (19398306340972287915765958549/5629499534213120000000000000000000), (-1192909128952414158035803699/1407374883553280000000000000000000), (-185919091621236542744289467/2814749767106560000000000000000000), (20028623325628827664470659/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial136.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial136.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial136.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial136 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 2988932423852764391874768407765540), (Int.ofNat 263104233553704989482386972673670), (Int.negOfNat 17629639532626776223920594905829), (Int.ofNat 1335692767116362665287839668559), (Int.ofNat 1853769280055696604136206249705), (Int.ofNat 34589326123977661308821909488), (Int.negOfNat 53726815447299147745931716506), (Int.negOfNat 2898528871636487298116939519), (Int.ofNat 620639573885593002225743181), (Int.ofNat 43718579605436902613098322), (Int.negOfNat 3909317395542515551877067), (Int.negOfNat 339635947014967294010590), (Int.ofNat 15512403788599815672723), (Int.ofNat 1704911759391457491796), (Int.negOfNat 40783060628232900690), (Int.negOfNat 6453275988049509288), (Int.ofNat 46953434190653512), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-149446621192638219593738420388277/281474976710656000000000000000000), (26310423355370498948238697267367/562949953421312000000000000000000), (-17629639532626776223920594905829/5629499534213120000000000000000000), (1335692767116362665287839668559/5629499534213120000000000000000000), (370753856011139320827241249941/1125899906842624000000000000000000), (2161832882748603831801369343/351843720888320000000000000000000), (-26863407723649573872965858253/2814749767106560000000000000000000), (-2898528871636487298116939519/5629499534213120000000000000000000), (620639573885593002225743181/5629499534213120000000000000000000), (21859289802718451306549161/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial136.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial136.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial136.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial136 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 2495422688146344188870797312061860), (Int.ofNat 259800549157125400375203625627624), (Int.ofNat 24060220856049799645811165618942), (Int.ofNat 8604982116721700981896054677623), (Int.negOfNat 1028501124421365507070009437867), (Int.negOfNat 526918683718993866635193335206), (Int.negOfNat 12326861189172339692288836599), (Int.ofNat 8333831309795635395620078936), (Int.ofNat 436098288819011058037687124), (Int.negOfNat 66786182766046584267655683), (Int.negOfNat 4559159900899169632690458), (Int.ofNat 332972280689893127374480), (Int.ofNat 27634163550908791180742), (Int.negOfNat 1138635500385825445744), (Int.negOfNat 114922029669211867400), (Int.ofNat 2914029805195059092), (Int.ofNat 399974421474343968), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-124771134407317209443539865603093/281474976710656000000000000000000), (32475068644640675046900453203453/703687441776640000000000000000000), (12030110428024899822905582809471/2814749767106560000000000000000000), (8604982116721700981896054677623/5629499534213120000000000000000000), (-1028501124421365507070009437867/5629499534213120000000000000000000), (-263459341859496933317596667603/2814749767106560000000000000000000), (-12326861189172339692288836599/5629499534213120000000000000000000), (1041728913724454424452509867/703687441776640000000000000000000), (109024572204752764509421781/1407374883553280000000000000000000), (-66786182766046584267655683/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial136.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial136.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial136.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial136 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 1843706891975693842100221219913705), (Int.ofNat 385876189549706849176615325588326), (Int.ofNat 11926718141410740503008248680974), (Int.negOfNat 17635944575818982226796764442783), (Int.negOfNat 4528911676535525207426078953587), (Int.ofNat 61332107225691711941693598887), (Int.ofNat 99218876541022542792183410321), (Int.ofNat 3606808364141361599217241769), (Int.negOfNat 993936399207785912103439981), (Int.negOfNat 55105900643213047555305177), (Int.ofNat 6045154336296680066027022), (Int.ofNat 409958215911623104822840), (Int.negOfNat 25154250398100598740983), (Int.negOfNat 1983582218179286521681), (Int.ofNat 76434396388292114415), (Int.ofNat 7273569407071968188), (Int.negOfNat 150229240586949262), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-368741378395138768420044243982741/1125899906842624000000000000000000), (192938094774853424588307662794163/2814749767106560000000000000000000), (5963359070705370251504124340487/2814749767106560000000000000000000), (-17635944575818982226796764442783/5629499534213120000000000000000000), (-4528911676535525207426078953587/5629499534213120000000000000000000), (61332107225691711941693598887/5629499534213120000000000000000000), (99218876541022542792183410321/5629499534213120000000000000000000), (3606808364141361599217241769/5629499534213120000000000000000000), (-993936399207785912103439981/5629499534213120000000000000000000), (-55105900643213047555305177/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial136.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial136.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial136.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial136 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 1229299226669080705776547034867288), (Int.ofNat 101489097188707328146839784941070), (Int.negOfNat 173395815715015527225180378723980), (Int.negOfNat 35489679373839152341482202079584), (Int.ofNat 1806798425928518419419334450217), (Int.ofNat 1056317388120448669932543539471), (Int.ofNat 25886169431617401605895631279), (Int.negOfNat 13075182414439964309172881351), (Int.negOfNat 617848758886541730751433849), (Int.ofNat 95790290830837955862062793), (Int.ofNat 5647334053246846959334668), (Int.negOfNat 475366552468325980029650), (Int.negOfNat 31800887363469781215977), (Int.ofNat 1721876139453085920829), (Int.ofNat 126427714890768579355), (Int.negOfNat 4662565488706493732), (Int.negOfNat 393890322351759558), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-153662403333635088222068379358411/703687441776640000000000000000000), (10148909718870732814683978494107/562949953421312000000000000000000), (-8669790785750776361259018936199/281474976710656000000000000000000), (-1109052480432473510671318814987/175921860444160000000000000000000), (1806798425928518419419334450217/5629499534213120000000000000000000), (1056317388120448669932543539471/5629499534213120000000000000000000), (25886169431617401605895631279/5629499534213120000000000000000000), (-13075182414439964309172881351/5629499534213120000000000000000000), (-617848758886541730751433849/5629499534213120000000000000000000), (95790290830837955862062793/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial136.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial136.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial136.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial136 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 1941232137005910097212436874192712), (Int.negOfNat 876924007851956856265736151093727), (Int.negOfNat 261655124778427559703185027875976), (Int.ofNat 17508541726803270903825560957497), (Int.ofNat 10008862178941237280789073260422), (Int.ofNat 213892892909765134195050676700), (Int.negOfNat 151467315456063369893471053491), (Int.negOfNat 6826590797705507151258565874), (Int.ofNat 1333747323150669697521009486), (Int.ofNat 73984181808403537495285557), (Int.negOfNat 7860399498172140036649802), (Int.negOfNat 479198798822906824298550), (Int.ofNat 33502082763243775436548), (Int.ofNat 2150622586414273653196), (Int.negOfNat 108457059375906910780), (Int.negOfNat 7401301384037399148), (Int.ofNat 253505046983245012), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-242654017125738762151554609274089/703687441776640000000000000000000), (-876924007851956856265736151093727/5629499534213120000000000000000000), (-32706890597303444962898128484497/703687441776640000000000000000000), (17508541726803270903825560957497/5629499534213120000000000000000000), (5004431089470618640394536630211/2814749767106560000000000000000000), (2138928929097651341950506767/56294995342131200000000000000000), (-151467315456063369893471053491/5629499534213120000000000000000000), (-3413295398852753575629282937/2814749767106560000000000000000000), (666873661575334848760504743/2814749767106560000000000000000000), (73984181808403537495285557/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial136.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial136.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial136.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial136 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 4444843220770217931577714699742289), (Int.negOfNat 1406695524662711135114255000738929), (Int.ofNat 62410134529536501607813169346713), (Int.ofNat 80728641167308726853122297335105), (Int.ofNat 2819426413532448815962834054870), (Int.negOfNat 1504058566170577258691879049671), (Int.negOfNat 79083668343616729802104433544), (Int.ofNat 16118557487138504633932576381), (Int.ofNat 946257006534064158432038069), (Int.negOfNat 113843171960747478730306498), (Int.negOfNat 6888974729876771341706103), (Int.ofNat 572857464979171835463910), (Int.ofNat 34572054972169944169627), (Int.negOfNat 2167456842748690740344), (Int.negOfNat 128341717458984228550), (Int.ofNat 6301689973803168472), (Int.ofNat 387806223229175148), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-4444843220770217931577714699742289/5629499534213120000000000000000000), (-1406695524662711135114255000738929/5629499534213120000000000000000000), (62410134529536501607813169346713/5629499534213120000000000000000000), (16145728233461745370624459467021/1125899906842624000000000000000000), (281942641353244881596283405487/562949953421312000000000000000000), (-1504058566170577258691879049671/5629499534213120000000000000000000), (-9885458542952091225263054193/703687441776640000000000000000000), (16118557487138504633932576381/5629499534213120000000000000000000), (946257006534064158432038069/5629499534213120000000000000000000), (-56921585980373739365153249/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial136.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial136.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial136.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial136 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 6368603638581290555162445490976038), (Int.negOfNat 225698708265491933753056131370227), (Int.ofNat 487084942950816829809718310805618), (Int.ofNat 40499946904842804072486227266727), (Int.negOfNat 11917104967034164958212649887479), (Int.negOfNat 940621090053422756906946288800), (Int.ofNat 162865281974832483457357762501), (Int.ofNat 11870710260866564206651180124), (Int.negOfNat 1420595415112150719748271256), (Int.negOfNat 95279891768514559702084962), (Int.ofNat 8586409844182707897584232), (Int.ofNat 529464792962611619114935), (Int.negOfNat 38201272847218467916313), (Int.negOfNat 2164583252733942429091), (Int.ofNat 130394196021574887570), (Int.ofNat 6800977724044028218), (Int.negOfNat 354752820338679292), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-3184301819290645277581222745488019/2814749767106560000000000000000000), (-225698708265491933753056131370227/5629499534213120000000000000000000), (243542471475408414904859155402809/2814749767106560000000000000000000), (40499946904842804072486227266727/5629499534213120000000000000000000), (-11917104967034164958212649887479/5629499534213120000000000000000000), (-1175776362566778446133682861/7036874417766400000000000000000), (162865281974832483457357762501/5629499534213120000000000000000000), (2967677565216641051662795031/1407374883553280000000000000000000), (-177574426889018839968533907/703687441776640000000000000000000), (-47639945884257279851042481/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial136.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial136.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial136.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial136.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial136 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial136 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial136 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 7674160468263200050372756963687946), (Int.negOfNat 22126586031477304779573003171409), (Int.ofNat 535161741573498784005305295839658), (Int.negOfNat 46223922279306583312891782446694), (Int.negOfNat 12472422551846639110764287815151), (Int.ofNat 1129805601389652562613578176176), (Int.ofNat 166510388317798981438207165881), (Int.negOfNat 13804311333858978468767432424), (Int.negOfNat 1435954286583824282302893206), (Int.ofNat 105860879936989777942088712), (Int.ofNat 8632308208248451935966632), (Int.negOfNat 566206435777580786127135), (Int.negOfNat 38305535383807154442113), (Int.ofNat 2252845107224609705391), (Int.ofNat 130394196021574887570), (Int.negOfNat 6800977724044028218), (Int.negOfNat 354752820338679292), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-3837080234131600025186378481843973/2814749767106560000000000000000000), (-22126586031477304779573003171409/5629499534213120000000000000000000), (267580870786749392002652647919829/2814749767106560000000000000000000), (-23111961139653291656445891223347/2814749767106560000000000000000000), (-12472422551846639110764287815151/5629499534213120000000000000000000), (70612850086853285163348636011/351843720888320000000000000000000), (166510388317798981438207165881/5629499534213120000000000000000000), (-1725538916732372308595929053/703687441776640000000000000000000), (-717977143291912141151446603/2814749767106560000000000000000000), (13232609992123722242761089/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial136.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial136.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial136.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 6102379181028238457216399627875309), (Int.ofNat 1279696400108862021626267848054610), (Int.ofNat 77546400685652850023300415185073), (Int.negOfNat 83798848863517686570922955652605), (Int.ofNat 3857796643265246924491165276437), (Int.ofNat 1588314547953922389990785886519), (Int.negOfNat 97494612797826507784817746044), (Int.negOfNat 16917228992346323036418271131), (Int.ofNat 1083859472118375407291167069), (Int.ofNat 118053809144431050174361648), (Int.negOfNat 7487580607598135235941153), (Int.negOfNat 587188169014986640877110), (Int.ofNat 36301200143125638041427), (Int.ofNat 2201788062783810869244), (Int.negOfNat 132010702806248975150), (Int.negOfNat 6301689973803168472), (Int.ofNat 387806223229175148), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-6102379181028238457216399627875309/5629499534213120000000000000000000), (127969640010886202162626784805461/562949953421312000000000000000000), (77546400685652850023300415185073/5629499534213120000000000000000000), (-16759769772703537314184591130521/1125899906842624000000000000000000), (3857796643265246924491165276437/5629499534213120000000000000000000), (1588314547953922389990785886519/5629499534213120000000000000000000), (-24373653199456626946204436511/1407374883553280000000000000000000), (-16917228992346323036418271131/5629499534213120000000000000000000), (1083859472118375407291167069/5629499534213120000000000000000000), (7378363071526940635897603/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial136.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial136.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial136.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 3798716611566435295670897574578077), (Int.ofNat 809850499120723898362047821706903), (Int.negOfNat 237975267010763935398307732687526), (Int.negOfNat 12034933410036178072998478396817), (Int.ofNat 10724176774877410975696949139581), (Int.negOfNat 352590278267101929579013828016), (Int.negOfNat 164934934989447442885559087391), (Int.ofNat 8231494521624458300834501224), (Int.ofNat 1434857799158707940004345936), (Int.negOfNat 81704489848021182901969057), (Int.negOfNat 8299727555017215659617652), (Int.ofNat 506112527948855296686550), (Int.ofNat 34767971578584042392048), (Int.negOfNat 2216425793581855110996), (Int.negOfNat 111077763195381729780), (Int.ofNat 7401301384037399148), (Int.ofNat 253505046983245012), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-3798716611566435295670897574578077/5629499534213120000000000000000000), (809850499120723898362047821706903/5629499534213120000000000000000000), (-118987633505381967699153866343763/2814749767106560000000000000000000), (-12034933410036178072998478396817/5629499534213120000000000000000000), (10724176774877410975696949139581/5629499534213120000000000000000000), (-22036892391693870598688364251/351843720888320000000000000000000), (-164934934989447442885559087391/5629499534213120000000000000000000), (1028936815203057287604312653/703687441776640000000000000000000), (89678612447419246250271621/351843720888320000000000000000000), (-81704489848021182901969057/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial136.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial136.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial136.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 3076076262512216372707274649277141), (Int.ofNat 1761845822822639639745520149389), (Int.negOfNat 112949296039146391022023860283420), (Int.ofNat 39904032178134402254392508810649), (Int.ofNat 797937023348387962414895032808), (Int.negOfNat 1211523298008504099411801433839), (Int.ofNat 37204160651723237528927800909), (Int.ofNat 14730476643626090286706304051), (Int.negOfNat 692307528393033658085124149), (Int.negOfNat 105018481224866138198379843), (Int.ofNat 5956225317157109549066818), (Int.ofNat 507687867536698541074650), (Int.negOfNat 32674475000808683178677), (Int.negOfNat 1800401530794502001229), (Int.ofNat 128262207564400952655), (Int.ofNat 4662565488706493732), (Int.negOfNat 393890322351759558), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-3076076262512216372707274649277141/5629499534213120000000000000000000), (1761845822822639639745520149389/5629499534213120000000000000000000), (-5647464801957319551101193014171/281474976710656000000000000000000), (39904032178134402254392508810649/5629499534213120000000000000000000), (99742127918548495301861879101/703687441776640000000000000000000), (-1211523298008504099411801433839/5629499534213120000000000000000000), (37204160651723237528927800909/5629499534213120000000000000000000), (14730476643626090286706304051/5629499534213120000000000000000000), (-692307528393033658085124149/5629499534213120000000000000000000), (-105018481224866138198379843/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial136.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial136.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial136.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 3227076691086511990867151297213928), (Int.negOfNat 29747933096806323745639789253517), (Int.ofNat 65887327936935451765304424390999), (Int.ofNat 10331962194313297526723078733763), (Int.negOfNat 6062492776796574388779884038454), (Int.ofNat 9695355333313082945256313501), (Int.ofNat 120618744413328548179300830241), (Int.negOfNat 4034298503495709100887420869), (Int.negOfNat 1145944802172507872729333481), (Int.ofNat 56884684605438879626605077), (Int.ofNat 6695175461008613618706172), (Int.negOfNat 415328844135149629850040), (Int.negOfNat 27017869685412230344283), (Int.ofNat 1996622336960702750181), (Int.ofNat 80365452117504342915), (Int.negOfNat 7273569407071968188), (Int.negOfNat 150229240586949262), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-403384586385813998858393912151741/703687441776640000000000000000000), (-29747933096806323745639789253517/5629499534213120000000000000000000), (65887327936935451765304424390999/5629499534213120000000000000000000), (10331962194313297526723078733763/5629499534213120000000000000000000), (-3031246388398287194389942019227/2814749767106560000000000000000000), (9695355333313082945256313501/5629499534213120000000000000000000), (120618744413328548179300830241/5629499534213120000000000000000000), (-4034298503495709100887420869/5629499534213120000000000000000000), (-1145944802172507872729333481/5629499534213120000000000000000000), (56884684605438879626605077/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial136.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial136.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial136.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 3030112296484565513149769637397592), (Int.ofNat 184898883327943632968295852690637), (Int.ofNat 7664893788700616018319592492517), (Int.negOfNat 22405212934779313883329378087970), (Int.negOfNat 842308690829211952341020361980), (Int.ofNat 759223422051955675147443462074), (Int.negOfNat 10741527207398252020570536399), (Int.negOfNat 10385951065468237823305301286), (Int.ofNat 412457184357671332652698374), (Int.ofNat 77472097685708312220113483), (Int.negOfNat 4435156231559324468599508), (Int.negOfNat 369357706064624513523080), (Int.ofNat 27248586711786330171742), (Int.ofNat 1225666408491152937444), (Int.negOfNat 114135818523369421700), (Int.negOfNat 2914029805195059092), (Int.ofNat 399974421474343968), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-378764037060570689143721204674699/703687441776640000000000000000000), (184898883327943632968295852690637/5629499534213120000000000000000000), (7664893788700616018319592492517/5629499534213120000000000000000000), (-2240521293477931388332937808797/562949953421312000000000000000000), (-42115434541460597617051018099/281474976710656000000000000000000), (379611711025977837573721731037/2814749767106560000000000000000000), (-10741527207398252020570536399/5629499534213120000000000000000000), (-5192975532734118911652650643/2814749767106560000000000000000000), (206228592178835666326349187/2814749767106560000000000000000000), (77472097685708312220113483/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial136.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial136.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial136.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 2799955230757587188963345899552195), (Int.negOfNat 25660675632671864927763642129399), (Int.negOfNat 94764630640730577728180761275794), (Int.negOfNat 5234295507097710677593979126627), (Int.ofNat 3900256197088227715853059266074), (Int.ofNat 55226966854942977521158661089), (Int.negOfNat 76462776746914754037039820356), (Int.ofNat 1933732705966664984120473069), (Int.ofNat 764195072891071674481851631), (Int.negOfNat 38237673569302986403946672), (Int.negOfNat 4490157208784981040112667), (Int.ofNat 320186433989040824733390), (Int.ofNat 17134427068839098335623), (Int.negOfNat 1657310673119844275596), (Int.negOfNat 44189975593550165390), (Int.ofNat 6191205606102027388), (Int.ofNat 46953434190653512), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-559991046151517437792669179910439/1125899906842624000000000000000000), (-25660675632671864927763642129399/5629499534213120000000000000000000), (-47382315320365288864090380637897/2814749767106560000000000000000000), (-5234295507097710677593979126627/5629499534213120000000000000000000), (1950128098544113857926529633037/2814749767106560000000000000000000), (55226966854942977521158661089/5629499534213120000000000000000000), (-19115694186728688509259955089/1407374883553280000000000000000000), (1933732705966664984120473069/5629499534213120000000000000000000), (764195072891071674481851631/5629499534213120000000000000000000), (-2389854598081436650246667/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial136.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial136.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial136.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 3212512036324856201519944977803143), (Int.negOfNat 351443547117244542078922736464548), (Int.negOfNat 44046285451384927480789683674557), (Int.ofNat 18135529437058364412529374230759), (Int.ofNat 1062641717492896242254475196920), (Int.negOfNat 460197643818567348450633031342), (Int.ofNat 781085493683844693303824149), (Int.ofNat 6277456845996682923023511896), (Int.negOfNat 245730966051436205534844684), (Int.negOfNat 47303597377591680737670318), (Int.ofNat 3153379849289681909596718), (Int.ofNat 214894182512282041877085), (Int.negOfNat 21042301113423082922207), (Int.negOfNat 611081940245820862199), (Int.ofNat 91859458548018324390), (Int.ofNat 926169034574932902), (Int.negOfNat 371633251798163128), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-3212512036324856201519944977803143/5629499534213120000000000000000000), (-87860886779311135519730684116137/1407374883553280000000000000000000), (-44046285451384927480789683674557/5629499534213120000000000000000000), (18135529437058364412529374230759/5629499534213120000000000000000000), (26566042937322406056361879923/140737488355328000000000000000000), (-230098821909283674225316515671/2814749767106560000000000000000000), (781085493683844693303824149/5629499534213120000000000000000000), (784682105749585365377938987/703687441776640000000000000000000), (-61432741512859051383711171/1407374883553280000000000000000000), (-23651798688795840368835159/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial136.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial136.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial136.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 3943454137121949950325410062036005), (Int.negOfNat 310193932289247985468947667813665), (Int.ofNat 57242960775018449930463874914102), (Int.ofNat 11229486008209075862701834595368), (Int.negOfNat 2152064972814965622392203430797), (Int.negOfNat 99426447305978552044070627644), (Int.ofNat 41820456600293526035274726601), (Int.negOfNat 863998369080295123833106734), (Int.negOfNat 420139417393261187064565826), (Int.ofNat 24830023032581693392035302), (Int.ofNat 2357495273171495845584512), (Int.negOfNat 228874509191308279234595), (Int.negOfNat 7535080707174190385113), (Int.ofNat 1243658296051040268441), (Int.ofNat 10700064660213927570), (Int.negOfNat 4908931705254091698), (Int.ofNat 25953169488599928), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-788690827424389990065082012407201/1125899906842624000000000000000000), (-62038786457849597093789533562733/1125899906842624000000000000000000), (28621480387509224965231937457051/2814749767106560000000000000000000), (1403685751026134482837729324421/703687441776640000000000000000000), (-2152064972814965622392203430797/5629499534213120000000000000000000), (-24856611826494638011017656911/1407374883553280000000000000000000), (41820456600293526035274726601/5629499534213120000000000000000000), (-431999184540147561916553367/2814749767106560000000000000000000), (-210069708696630593532282913/2814749767106560000000000000000000), (12415011516290846696017651/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial136.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial136.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial136.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 4280175957017477225569590487868915), (Int.negOfNat 16009636556271236049142674093118), (Int.ofNat 73854433901400731007247554818024), (Int.negOfNat 4350003065513196563687783908438), (Int.negOfNat 1227947486940349049218253779637), (Int.ofNat 203564307632129185545660848612), (Int.ofNat 3716333889911745809151851836), (Int.negOfNat 3013041625664447480694109461), (Int.ofNat 138982836213450176226984699), (Int.ofNat 21881083167624956223375648), (Int.negOfNat 2060381251993849006177823), (Int.negOfNat 80714571126659671219810), (Int.ofNat 14495719954778709388677), (Int.ofNat 82101518210444267364), (Int.negOfNat 65247138844568956870), (Int.ofNat 681037039113793808), (Int.ofNat 306838780282355568), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-856035191403495445113918097573783/1125899906842624000000000000000000), (-8004818278135618024571337046559/2814749767106560000000000000000000), (9231804237675091375905944352253/703687441776640000000000000000000), (-2175001532756598281843891954219/2814749767106560000000000000000000), (-1227947486940349049218253779637/5629499534213120000000000000000000), (50891076908032296386415212153/1407374883553280000000000000000000), (929083472477936452287962959/1407374883553280000000000000000000), (-3013041625664447480694109461/5629499534213120000000000000000000), (138982836213450176226984699/5629499534213120000000000000000000), (683783848988279881980489/175921860444160000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial136.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial136.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial136.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 4064813878358880207561826715547308), (Int.ofNat 203744208245666606572521375007324), (Int.ofNat 33760822708553704437954816869313), (Int.negOfNat 6790457236778075914057727230519), (Int.ofNat 401611576754426684010540355080), (Int.ofNat 83873221315649275643845280894), (Int.negOfNat 15483977974859901008321145471), (Int.ofNat 307313411422290529601808464), (Int.ofNat 162225340329606602946693046), (Int.negOfNat 14334045747431861855308877), (Int.negOfNat 711175272696128205659212), (Int.ofNat 141516114598375440151620), (Int.ofNat 97970203160061171058), (Int.negOfNat 789947775144949481616), (Int.ofNat 15233857797490238880), (Int.ofNat 2919035668219707588), (Int.negOfNat 66462537409949588), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-1016203469589720051890456678886827/1407374883553280000000000000000000), (50936052061416651643130343751831/1407374883553280000000000000000000), (33760822708553704437954816869313/5629499534213120000000000000000000), (-6790457236778075914057727230519/5629499534213120000000000000000000), (10040289418860667100263508877/140737488355328000000000000000000), (41936610657824637821922640447/2814749767106560000000000000000000), (-15483977974859901008321145471/5629499534213120000000000000000000), (19207088213893158100113029/351843720888320000000000000000000), (81112670164803301473346523/2814749767106560000000000000000000), (-14334045747431861855308877/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial136.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial136.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial136.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 3568413992587551634826142969225865), (Int.ofNat 274159201704303895103093825344782), (Int.ofNat 6077311987148433276719702729351), (Int.negOfNat 2319478842731815438482986314503), (Int.ofNat 517415944749836367834524412814), (Int.negOfNat 34118015212752280107407859057), (Int.negOfNat 3091661799684068649862504621), (Int.ofNat 829861638718259805216454341), (Int.negOfNat 63794826548874034562040039), (Int.negOfNat 4544779429267250959263813), (Int.ofNat 1085402012534126613885318), (Int.negOfNat 11281372706310076951300), (Int.negOfNat 7916504809967817360257), (Int.ofNat 272062552764963429541), (Int.ofNat 35908808651314153005), (Int.negOfNat 1966204144169881608), (Int.negOfNat 203562973886059818), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-713682798517510326965228593845173/1125899906842624000000000000000000), (137079600852151947551546912672391/2814749767106560000000000000000000), (6077311987148433276719702729351/5629499534213120000000000000000000), (-2319478842731815438482986314503/5629499534213120000000000000000000), (258707972374918183917262206407/2814749767106560000000000000000000), (-34118015212752280107407859057/5629499534213120000000000000000000), (-3091661799684068649862504621/5629499534213120000000000000000000), (829861638718259805216454341/5629499534213120000000000000000000), (-63794826548874034562040039/5629499534213120000000000000000000), (-4544779429267250959263813/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial136.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial136.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial136.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 3007264537136632167909120356473977), (Int.ofNat 284170208186238025146372198078867), (Int.ofNat 1541092196682667994329852234930), (Int.ofNat 301838016449036147903664976800), (Int.ofNat 146561591071445953866183283795), (Int.negOfNat 31515030165226715362686395649), (Int.ofNat 1421518854415036637185844621), (Int.negOfNat 21220669298955106340080759), (Int.negOfNat 11415058074054113725701291), (Int.ofNat 5488103310386784443901067), (Int.negOfNat 260782777823882543716018), (Int.negOfNat 59485207131987897770910), (Int.ofNat 4134219924960787946717), (Int.ofNat 335023429370538081791), (Int.negOfNat 28238153397197171475), (Int.negOfNat 1087343396659556228), (Int.ofNat 72546636532533998), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-3007264537136632167909120356473977/5629499534213120000000000000000000), (284170208186238025146372198078867/5629499534213120000000000000000000), (154109219668266799432985223493/562949953421312000000000000000000), (377297520561295184879581221/7036874417766400000000000000000), (29312318214289190773236656759/1125899906842624000000000000000000), (-31515030165226715362686395649/5629499534213120000000000000000000), (1421518854415036637185844621/5629499534213120000000000000000000), (-21220669298955106340080759/5629499534213120000000000000000000), (-11415058074054113725701291/5629499534213120000000000000000000), (5488103310386784443901067/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial136.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial136.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial136.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 2428920764429069132427944150784738), (Int.ofNat 296387892675789303664594289781824), (Int.ofNat 4675775827185317449810673732196), (Int.ofNat 432359719501681584363900243667), (Int.negOfNat 85299042027553715123231536414), (Int.negOfNat 13653526566876780239961769068), (Int.ofNat 2072294773580908029034861741), (Int.ofNat 149747846667689376574685984), (Int.ofNat 2378153504533031477392574), (Int.negOfNat 3736629504308697830155887), (Int.negOfNat 219568594577543411072538), (Int.ofNat 52623204474840712824610), (Int.ofNat 1773384984365956932632), (Int.negOfNat 408696566448839950016), (Int.negOfNat 7450319024759040620), (Int.ofNat 2042781175437423548), (Int.ofNat 100287167489764068), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-1214460382214534566213972075392369/2814749767106560000000000000000000), (4631060823059207869759285777841/87960930222080000000000000000000), (1168943956796329362452668433049/1407374883553280000000000000000000), (432359719501681584363900243667/5629499534213120000000000000000000), (-42649521013776857561615768207/2814749767106560000000000000000000), (-3413381641719195059990442267/1407374883553280000000000000000000), (2072294773580908029034861741/5629499534213120000000000000000000), (4679620208365293017958937/175921860444160000000000000000000), (1189076752266515738696287/2814749767106560000000000000000000), (-3736629504308697830155887/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial136.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial136.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial136.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1815634318488540053840765492863996), (Int.ofNat 316915744895980824971244421849827), (Int.ofNat 4714505718871466738056563213552), (Int.negOfNat 397645354997712434098372196864), (Int.negOfNat 68624443819834678154792893902), (Int.ofNat 17154638367357912306135537749), (Int.ofNat 1979136044331777014138665744), (Int.negOfNat 282976936586582838465113091), (Int.negOfNat 37458320198629494439008729), (Int.ofNat 2068537063243037388002488), (Int.ofNat 543156186367214334267773), (Int.negOfNat 11882132121878756229670), (Int.negOfNat 4899422092535810056487), (Int.ofNat 73027257266665046904), (Int.ofNat 28580138338750486790), (Int.negOfNat 716058998120294032), (Int.negOfNat 78630735655118408), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-453908579622135013460191373215999/1407374883553280000000000000000000), (316915744895980824971244421849827/5629499534213120000000000000000000), (294656607429466671128535200847/351843720888320000000000000000000), (-776651083979907097848383197/10995116277760000000000000000000), (-34312221909917339077396446951/2814749767106560000000000000000000), (17154638367357912306135537749/5629499534213120000000000000000000), (123696002770736063383666609/351843720888320000000000000000000), (-282976936586582838465113091/5629499534213120000000000000000000), (-37458320198629494439008729/5629499534213120000000000000000000), (258567132905379673500311/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial136.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial136.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial136.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 1166592585077164669919256822715489), (Int.ofNat 330400575155499605184710350256640), (Int.ofNat 2286869897198925832224164849687), (Int.negOfNat 150934926521603397651672205203), (Int.ofNat 115055016409652086101480326076), (Int.ofNat 8106261003423846060614379358), (Int.negOfNat 3392071609290595954681186571), (Int.negOfNat 230612800236445665090014024), (Int.ofNat 50884787831497193563366786), (Int.ofNat 4082669477986312645280542), (Int.negOfNat 476843601421267002119292), (Int.negOfNat 45808731777427710709155), (Int.ofNat 3253613638594513799513), (Int.ofNat 328101706833968610151), (Int.negOfNat 16094184302697863330), (Int.negOfNat 1732473473660639278), (Int.ofNat 5016671947393152), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1166592585077164669919256822715489/5629499534213120000000000000000000), (129062724670117033275277480569/2199023255552000000000000000000), (2286869897198925832224164849687/5629499534213120000000000000000000), (-150934926521603397651672205203/5629499534213120000000000000000000), (28763754102413021525370081519/1407374883553280000000000000000000), (4053130501711923030307189679/2814749767106560000000000000000000), (-3392071609290595954681186571/5629499534213120000000000000000000), (-28826600029555708136251753/703687441776640000000000000000000), (25442393915748596781683393/2814749767106560000000000000000000), (2041334738993156322640271/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial136.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial136.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial136.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 495983214576971539599144878415101), (Int.ofNat 341371154956185324200495145781399), (Int.ofNat 3925492682519286362043150180463), (Int.ofNat 526203081547741428408899664455), (Int.negOfNat 6358481303103133092763832448), (Int.negOfNat 25726326251198867465937055434), (Int.negOfNat 209357974354958864510657229), (Int.ofNat 580745007508127161323002026), (Int.ofNat 13076983069887222203184364), (Int.negOfNat 7517000771082350660040958), (Int.negOfNat 252851314764243134084308), (Int.ofNat 63465043271026577451345), (Int.ofNat 2581073704777918886887), (Int.negOfNat 377714032769202971249), (Int.negOfNat 16381247222138439770), (Int.ofNat 1842850562403571322), (Int.ofNat 13836264139310848), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-495983214576971539599144878415101/5629499534213120000000000000000000), (341371154956185324200495145781399/5629499534213120000000000000000000), (3925492682519286362043150180463/5629499534213120000000000000000000), (105240616309548285681779932891/1125899906842624000000000000000000), (-49675635180493227287217441/43980465111040000000000000000000), (-12863163125599433732968527717/2814749767106560000000000000000000), (-209357974354958864510657229/5629499534213120000000000000000000), (290372503754063580661501013/2814749767106560000000000000000000), (3269245767471805550796091/1407374883553280000000000000000000), (-3758500385541175330020479/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial136.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial136.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial136.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 205806026355141994734117468316684), (Int.ofNat 361341496011737954465734819896196), (Int.ofNat 5199795755383689939992014021648), (Int.negOfNat 280007049689957475517335297126), (Int.negOfNat 129777349134190796320495179871), (Int.ofNat 11211818222352530742927788032), (Int.ofNat 4484783400598271104614242456), (Int.negOfNat 180313068092542448931084341), (Int.negOfNat 80692929885919747581521271), (Int.ofNat 1160852205316158459070588), (Int.ofNat 879061067524265879171327), (Int.ofNat 1067259688296571988630), (Int.negOfNat 6359294559581310401613), (Int.negOfNat 66402896240182515496), (Int.ofNat 32432716574793493810), (Int.ofNat 847025074613273368), (Int.negOfNat 77923275626646592), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(51451506588785498683529367079171/1407374883553280000000000000000000), (90335374002934488616433704974049/1407374883553280000000000000000000), (324987234711480621249500876353/351843720888320000000000000000000), (-140003524844978737758667648563/2814749767106560000000000000000000), (-129777349134190796320495179871/5629499534213120000000000000000000), (5474520616383071651820209/2748779069440000000000000000000), (560597925074783888076780307/703687441776640000000000000000000), (-180313068092542448931084341/5629499534213120000000000000000000), (-80692929885919747581521271/5629499534213120000000000000000000), (290213051329039614767647/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial136.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial136.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial136.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 945575244915019563520602486283771), (Int.ofNat 376229364648064034146296734366740), (Int.ofNat 2127696243712843956926350805184), (Int.negOfNat 378688032080679576734051457446), (Int.ofNat 126307655838405601190270528856), (Int.ofNat 22560013815385798223645242006), (Int.negOfNat 3693243361343462478137522491), (Int.negOfNat 608864672603221427149256966), (Int.ofNat 52964942281854480021123426), (Int.ofNat 9078493779958335956848663), (Int.negOfNat 424460031154707938031212), (Int.negOfNat 84099240997612953971490), (Int.ofNat 2008621968936659766668), (Int.ofNat 523661828410994107584), (Int.negOfNat 5682935285926556380), (Int.negOfNat 2443174222396942252), (Int.ofNat 87411509216123432), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(945575244915019563520602486283771/5629499534213120000000000000000000), (18811468232403201707314836718337/281474976710656000000000000000000), (33245253808013186826974231331/87960930222080000000000000000000), (-189344016040339788367025728723/2814749767106560000000000000000000), (15788456979800700148783816107/703687441776640000000000000000000), (11280006907692899111822621003/2814749767106560000000000000000000), (-3693243361343462478137522491/5629499534213120000000000000000000), (-304432336301610713574628483/2814749767106560000000000000000000), (26482471140927240010561713/2814749767106560000000000000000000), (9078493779958335956848663/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial136.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial136.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial136.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 1705961408293767294676201437992574), (Int.ofNat 385132773698661658301378263368238), (Int.ofNat 3525921658643913937814787602965), (Int.ofNat 736308954806139196809132013065), (Int.ofNat 46933448236935037853630806873), (Int.negOfNat 36418913411131582932819160337), (Int.negOfNat 2630193226112217575330853901), (Int.ofNat 796706650197191377082260041), (Int.ofNat 63582186670613340459057741), (Int.negOfNat 9426876675066852875975083), (Int.negOfNat 835628111206826098842732), (Int.ofNat 67461779761497141569690), (Int.ofNat 6771738456917556431283), (Int.negOfNat 315322351371545237509), (Int.negOfNat 36741049854094079125), (Int.ofNat 792099410483401372), (Int.ofNat 84007374749231002), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(852980704146883647338100718996287/2814749767106560000000000000000000), (192566386849330829150689131684119/2814749767106560000000000000000000), (705184331728782787562957520593/1125899906842624000000000000000000), (147261790961227839361826402613/1125899906842624000000000000000000), (46933448236935037853630806873/5629499534213120000000000000000000), (-36418913411131582932819160337/5629499534213120000000000000000000), (-2630193226112217575330853901/5629499534213120000000000000000000), (796706650197191377082260041/5629499534213120000000000000000000), (63582186670613340459057741/5629499534213120000000000000000000), (-9426876675066852875975083/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial136.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial136.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial136.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 2495751047545357920152690935974912), (Int.ofNat 406552468402826261099003966269576), (Int.ofNat 6123973858972427607059121337329), (Int.negOfNat 265734851246764585134625807508), (Int.negOfNat 226458855392166179552934553981), (Int.ofNat 4227885882122557913874547039), (Int.ofNat 7806358080622378619631767271), (Int.ofNat 133851935783767051403735291), (Int.negOfNat 132616313555873858554348011), (Int.negOfNat 4830211434728700530359563), (Int.ofNat 1286800768508752271305582), (Int.ofNat 63262772809282423505300), (Int.negOfNat 7869079488462430720443), (Int.negOfNat 467462303435768985059), (Int.ofNat 32422728515094081495), (Int.ofNat 2315442245431511292), (Int.negOfNat 190687315612419182), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(2437256882368513593899112242163/5497558138880000000000000000000), (50819058550353282637375495783697/703687441776640000000000000000000), (6123973858972427607059121337329/5629499534213120000000000000000000), (-66433712811691146283656451877/1407374883553280000000000000000000), (-226458855392166179552934553981/5629499534213120000000000000000000), (4227885882122557913874547039/5629499534213120000000000000000000), (7806358080622378619631767271/5629499534213120000000000000000000), (133851935783767051403735291/5629499534213120000000000000000000), (-132616313555873858554348011/5629499534213120000000000000000000), (-4830211434728700530359563/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial136.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial136.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial136.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 3328219680546697976352659146939461), (Int.ofNat 422370038605091355813563478432518), (Int.ofNat 1152364321843879473633673015345), (Int.negOfNat 826489263053200034693638127034), (Int.ofNat 172511845913555380781017691757), (Int.ofNat 51332914240555761682006022822), (Int.negOfNat 3697785938868064025242208879), (Int.negOfNat 1347597670814308253432369786), (Int.ofNat 21734950609796090541996354), (Int.ofNat 18260201652028083768155973), (Int.ofNat 206143541455442057392912), (Int.negOfNat 145500587038243180450080), (Int.negOfNat 3917512912114118496658), (Int.ofNat 751194958829343971884), (Int.ofNat 28192184166044016820), (Int.negOfNat 2540635093994836012), (Int.negOfNat 90091473871815412), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(3328219680546697976352659146939461/5629499534213120000000000000000000), (211185019302545677906781739216259/2814749767106560000000000000000000), (230472864368775894726734603069/1125899906842624000000000000000000), (-413244631526600017346819063517/2814749767106560000000000000000000), (172511845913555380781017691757/5629499534213120000000000000000000), (25666457120277880841003011411/2814749767106560000000000000000000), (-3697785938868064025242208879/5629499534213120000000000000000000), (-673798835407154126716184893/2814749767106560000000000000000000), (10867475304898045270998177/2814749767106560000000000000000000), (18260201652028083768155973/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial136.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial136.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial136.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 4174965809875438312778190131786938), (Int.ofNat 425438629132226809262554590118633), (Int.ofNat 2768524583995410955364749884611), (Int.ofNat 1394552005081537943897261441642), (Int.ofNat 181038319448061146060541112504), (Int.negOfNat 62458900244642208761343491469), (Int.negOfNat 9370327006877188735453296736), (Int.ofNat 1049763703703403301680378539), (Int.ofNat 198212745656104615247421901), (Int.negOfNat 7133984816267187029859952), (Int.negOfNat 2165246838269779512055027), (Int.ofNat 6659183879828466820090), (Int.ofNat 14085967873793805186423), (Int.ofNat 190741583997574388664), (Int.negOfNat 61281690229869943630), (Int.negOfNat 1495148826409052392), (Int.ofNat 293963122008714932), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(2087482904937719156389095065893469/2814749767106560000000000000000000), (425438629132226809262554590118633/5629499534213120000000000000000000), (2768524583995410955364749884611/5629499534213120000000000000000000), (697276002540768971948630720821/2814749767106560000000000000000000), (22629789931007643257567639063/703687441776640000000000000000000), (-62458900244642208761343491469/5629499534213120000000000000000000), (-292822718964912147982915523/175921860444160000000000000000000), (1049763703703403301680378539/5629499534213120000000000000000000), (198212745656104615247421901/5629499534213120000000000000000000), (-445874051016699189366247/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial136.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial136.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial136.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 5048551124155008009877439142412372), (Int.ofNat 452890928245334787648526601184176), (Int.ofNat 9239133497527574565825591639723), (Int.negOfNat 281418972788784675713476864640), (Int.negOfNat 545632559523518018222230874875), (Int.negOfNat 28143726527492128233916858312), (Int.ofNat 16381120244957077380955991549), (Int.ofNat 1500236189926465259388532166), (Int.negOfNat 204028781658762909492235324), (Int.negOfNat 26086713463332534158404698), (Int.ofNat 1122827139798248755418088), (Int.ofNat 223593966676323358737105), (Int.negOfNat 2367709954017089116587), (Int.negOfNat 1187208539498204301159), (Int.negOfNat 6156799030549934770), (Int.ofNat 4528495864614962202), (Int.ofNat 61750304195634572), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(1262137781038752002469359785603093/1407374883553280000000000000000000), (28305683015333424228032912574011/351843720888320000000000000000000), (9239133497527574565825591639723/5629499534213120000000000000000000), (-439717144982476055802307601/8796093022208000000000000000000), (-4365060476188144145777846999/45035996273704960000000000000000), (-3517965815936516029239607289/703687441776640000000000000000000), (16381120244957077380955991549/5629499534213120000000000000000000), (750118094963232629694266083/2814749767106560000000000000000000), (-51007195414690727373058831/1407374883553280000000000000000000), (-13043356731666267079202349/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial136.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial136.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial136.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 5980583865127936138577155190875160), (Int.ofNat 470315092573709924483576830270008), (Int.negOfNat 3323376278708615823999934838863), (Int.negOfNat 2790898282315595269402835328813), (Int.ofNat 265976478712951149508346700051), (Int.ofNat 165495717433878278769832287624), (Int.ofNat 3687133722781495519498557251), (Int.negOfNat 3447975367224804459148718104), (Int.negOfNat 241497736064293095928352866), (Int.ofNat 28839501734994420623451482), (Int.ofNat 3025526139696950345130682), (Int.negOfNat 126680421781879203094015), (Int.negOfNat 20136135462158729522493), (Int.ofNat 288916989758559134801), (Int.ofNat 87846338752103478910), (Int.ofNat 212874925561116702), (Int.negOfNat 366869725687968372), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(149514596628198403464428879771879/140737488355328000000000000000000), (58789386571713740560447103783751/703687441776640000000000000000000), (-3323376278708615823999934838863/5629499534213120000000000000000000), (-2790898282315595269402835328813/5629499534213120000000000000000000), (265976478712951149508346700051/5629499534213120000000000000000000), (20686964679234784846229035953/703687441776640000000000000000000), (3687133722781495519498557251/5629499534213120000000000000000000), (-430996920903100557393589763/703687441776640000000000000000000), (-120748868032146547964176433/2814749767106560000000000000000000), (14419750867497210311725741/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial136.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial136.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial136.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 6894895183646918637551332107316940), (Int.ofNat 444277696269565611812309813008330), (Int.negOfNat 2147667652541888683118437812571), (Int.ofNat 4377096632836700634310897262441), (Int.ofNat 1055486398522405736282635169195), (Int.negOfNat 111145359684880843701503836888), (Int.negOfNat 45021113214278532354227308194), (Int.negOfNat 1364988134437339458812873481), (Int.ofNat 523402280954977356349299619), (Int.ofNat 34573503527989255231062978), (Int.negOfNat 3149999025080913253819133), (Int.negOfNat 302184417168669862727710), (Int.ofNat 11521627017291576592177), (Int.ofNat 1588562335703319008904), (Int.negOfNat 25729880145858375110), (Int.negOfNat 6135701938303688912), (Int.ofNat 3044167320172988), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(344744759182345931877566605365847/281474976710656000000000000000000), (44427769626956561181230981300833/562949953421312000000000000000000), (-2147667652541888683118437812571/5629499534213120000000000000000000), (4377096632836700634310897262441/5629499534213120000000000000000000), (211097279704481147256527033839/1125899906842624000000000000000000), (-13893169960610105462687979611/703687441776640000000000000000000), (-22510556607139266177113654097/2814749767106560000000000000000000), (-1364988134437339458812873481/5629499534213120000000000000000000), (523402280954977356349299619/5629499534213120000000000000000000), (17286751763994627615531489/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial136.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial136.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial136.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 7820299647510035789898059737643760), (Int.ofNat 504437005617712333985552689546476), (Int.ofNat 29886089560346763412342629589358), (Int.ofNat 1471790596602748871913003568877), (Int.negOfNat 2466921189182252749507394672333), (Int.negOfNat 494562718849413165824060952694), (Int.ofNat 3667771600377445332094627299), (Int.ofNat 7814306915855257858279822364), (Int.ofNat 326960552931015025804585576), (Int.negOfNat 59864147866475685802053517), (Int.negOfNat 4048298942472127086780542), (Int.ofNat 282587486089154337950920), (Int.ofNat 25917300226753457380458), (Int.negOfNat 900153852485297089356), (Int.negOfNat 110627635305632833700), (Int.ofNat 2039091493420749308), (Int.ofNat 407379093609318032), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(97753745593875447373725746720547/70368744177664000000000000000000), (126109251404428083496388172386619/1407374883553280000000000000000000), (14943044780173381706171314794679/2814749767106560000000000000000000), (1471790596602748871913003568877/5629499534213120000000000000000000), (-2466921189182252749507394672333/5629499534213120000000000000000000), (-247281359424706582912030476347/2814749767106560000000000000000000), (3667771600377445332094627299/5629499534213120000000000000000000), (1953576728963814464569955591/1407374883553280000000000000000000), (40870069116376878225573197/703687441776640000000000000000000), (-59864147866475685802053517/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial136.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial136.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial136.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 8906480146194524185272992862106205), (Int.ofNat 527521290477953989174706834615674), (Int.negOfNat 53649863961649760200388823221774), (Int.negOfNat 32866815595798372936619988796917), (Int.negOfNat 4919275861336729710505289157113), (Int.ofNat 209581085324489481265665149013), (Int.ofNat 101292110172705281038539374879), (Int.ofNat 2545520117145642028616734631), (Int.negOfNat 956631215691202781172732619), (Int.negOfNat 49323226294586854611957823), (Int.ofNat 5532733810049613253927078), (Int.ofNat 388153885742893442624560), (Int.negOfNat 21897203379927004198317), (Int.negOfNat 1927905766487220303719), (Int.ofNat 62862968478314304885), (Int.ofNat 7158798661412294812), (Int.negOfNat 106319973716468738), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(1781296029238904837054598572421241/1125899906842624000000000000000000), (263760645238976994587353417307837/2814749767106560000000000000000000), (-26824931980824880100194411610887/2814749767106560000000000000000000), (-32866815595798372936619988796917/5629499534213120000000000000000000), (-4919275861336729710505289157113/5629499534213120000000000000000000), (209581085324489481265665149013/5629499534213120000000000000000000), (101292110172705281038539374879/5629499534213120000000000000000000), (2545520117145642028616734631/5629499534213120000000000000000000), (-956631215691202781172732619/5629499534213120000000000000000000), (-49323226294586854611957823/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial136.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial136.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial136.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 9418531654244840086113317406737788), (Int.negOfNat 202602978417600393221299153583370), (Int.negOfNat 327994851405537048498422368069520), (Int.negOfNat 48086588921973489984280628295416), (Int.ofNat 2783866198887333952743475210083), (Int.ofNat 1164225373310201660956068701629), (Int.ofNat 19315898588421834889211713021), (Int.negOfNat 13231166499311623348206871149), (Int.negOfNat 571945528433389650395067651), (Int.ofNat 92052777410062660900994007), (Int.ofNat 5435560750150986750431132), (Int.negOfNat 437878507648608424401650), (Int.negOfNat 31278485236888391150623), (Int.ofNat 1522136802581759254571), (Int.ofNat 126294096844312218545), (Int.negOfNat 3870783764980900668), (Int.negOfNat 413463192731902442), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(2354632913561210021528329351684447/1407374883553280000000000000000000), (-20260297841760039322129915358337/562949953421312000000000000000000), (-4099935642569213106230279600869/70368744177664000000000000000000), (-6010823615246686248035078536927/703687441776640000000000000000000), (2783866198887333952743475210083/5629499534213120000000000000000000), (1164225373310201660956068701629/5629499534213120000000000000000000), (19315898588421834889211713021/5629499534213120000000000000000000), (-13231166499311623348206871149/5629499534213120000000000000000000), (-571945528433389650395067651/5629499534213120000000000000000000), (92052777410062660900994007/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial136.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial136.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial136.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 7397898548208564021694759945630312), (Int.negOfNat 1911969972101974439532726198362573), (Int.negOfNat 461371382605734252239890928933224), (Int.ofNat 15966397227157040980288674048003), (Int.ofNat 11662192063356193998562593151278), (Int.ofNat 242274580306834984497820535200), (Int.negOfNat 157760500398873910975161510409), (Int.negOfNat 6799337918212568827497556126), (Int.ofNat 1320177095731944463042421114), (Int.ofNat 73096753284012287874303943), (Int.negOfNat 7505989342374019331853598), (Int.negOfNat 478037279975250749576550), (Int.ofNat 30969731123831962229052), (Int.ofNat 2171946367688103676604), (Int.negOfNat 97161051839798367820), (Int.negOfNat 7497446074627318652), (Int.ofNat 209595780112764488), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(924737318526070502711844993203789/703687441776640000000000000000000), (-1911969972101974439532726198362573/5629499534213120000000000000000000), (-57671422825716781529986366116653/703687441776640000000000000000000), (15966397227157040980288674048003/5629499534213120000000000000000000), (5831096031678096999281296575639/2814749767106560000000000000000000), (302843225383543730622275669/7036874417766400000000000000000), (-157760500398873910975161510409/5629499534213120000000000000000000), (-3399668959106284413748778063/2814749767106560000000000000000000), (660088547865972231521210557/2814749767106560000000000000000000), (73096753284012287874303943/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial136.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial136.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial136.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 2039951992253882814642295736909289), (Int.negOfNat 3205145417863198803983695498314071), (Int.negOfNat 106125043781707241999210946041613), (Int.ofNat 92532888533514935116485383848495), (Int.ofNat 4372346449434747800268191966430), (Int.negOfNat 1554120778380931865164590209929), (Int.negOfNat 86040474840131907724507848156), (Int.ofNat 16090000678479342725427726819), (Int.ofNat 964821615914654605210368431), (Int.negOfNat 110966004718596407179847402), (Int.negOfNat 6977390847177300233555097), (Int.ofNat 545359635120075900568790), (Int.ofNat 35315072359119183785173), (Int.negOfNat 2014116562877379070156), (Int.negOfNat 132642244685306439750), (Int.ofNat 5674186159760750928), (Int.ofNat 419547291854486852), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(2039951992253882814642295736909289/5629499534213120000000000000000000), (-3205145417863198803983695498314071/5629499534213120000000000000000000), (-106125043781707241999210946041613/5629499534213120000000000000000000), (18506577706702987023297076769699/1125899906842624000000000000000000), (437234644943474780026819196643/562949953421312000000000000000000), (-1554120778380931865164590209929/5629499534213120000000000000000000), (-21510118710032976931126962039/1407374883553280000000000000000000), (16090000678479342725427726819/5629499534213120000000000000000000), (964821615914654605210368431/5629499534213120000000000000000000), (-55483002359298203589923701/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial136.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial136.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial136.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 4037613024367301185480533069918762), (Int.negOfNat 2512273479907178642775811489847473), (Int.ofNat 420996334514293131693127592561182), (Int.ofNat 61642325459821043000404195575673), (Int.negOfNat 11260023698472407722879105749721), (Int.negOfNat 1063852693693621425688233437700), (Int.ofNat 158890725651643197932387546099), (Int.ofNat 12356359988254923377511015176), (Int.negOfNat 1391496217210539442398366044), (Int.negOfNat 97590404719187434959550538), (Int.ofNat 8326428820824547544612168), (Int.ofNat 545633089051267420687365), (Int.negOfNat 36443661783574389876187), (Int.negOfNat 2259185408683469221609), (Int.ofNat 122256881916849696530), (Int.ofNat 7187138372850534382), (Int.negOfNat 314899619549921708), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-2018806512183650592740266534959381/2814749767106560000000000000000000), (-2512273479907178642775811489847473/5629499534213120000000000000000000), (210498167257146565846563796280591/2814749767106560000000000000000000), (61642325459821043000404195575673/5629499534213120000000000000000000), (-11260023698472407722879105749721/5629499534213120000000000000000000), (-10638526936936214256882334377/56294995342131200000000000000000), (158890725651643197932387546099/5629499534213120000000000000000000), (1544544998531865422188876897/703687441776640000000000000000000), (-347874054302634860599591511/1407374883553280000000000000000000), (-48795202359593717479775269/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial136.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial136.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial136.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial136.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial136.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial136.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial136.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial136.reflect := by
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

end Bin136
end
end ErdosOverlap.OuterNumerics
