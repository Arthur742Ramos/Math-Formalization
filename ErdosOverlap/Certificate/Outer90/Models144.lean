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

/-! # Exact integer weighted outer models for source bin 144

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin144

def weightDenominator : ℤ := (Int.ofNat 500000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 127182301678211180000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 125476408502246920000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 110931249189359385000)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 75925748589648350000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 49031349531915165000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 27744100711658417000)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 16533965292505325000)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 25304593784329720000)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 8622867149362582500)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial144.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial144.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 492519891982512150000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 114711253591922010000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 75371321354247385000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 47441436365814165000)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 15028046417827564000)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 2519121671337873500)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 5742065685359410000)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 5646826089939877500)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 28488430611510773)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial144.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial144.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 492519891982512150000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 114711253591922010000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 75371321354247385000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 47441436365814165000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 15028046417827564000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 2519121671337873500)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 5742065685359410000)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 5646826089939877500)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 28488430611510773)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial144.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial144.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial144.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 443496165145289108657473096813391279), (Int.ofNat 249016215157197822495854316417832241), (Int.ofNat 47764844188696525266533602808564840), (Int.negOfNat 8183588944025870826606410220804107), (Int.negOfNat 1400672526363141419472815351047381), (Int.ofNat 165930508854268470889881430424007), (Int.ofNat 22045621663424382770800224168737), (Int.negOfNat 2054083616858997851006882306237), (Int.negOfNat 216270722380734650197456433592), (Int.ofNat 16769866463550097058064494576), (Int.ofNat 1439375926816234709712675677), (Int.negOfNat 96516139300744242091932722), (Int.negOfNat 6909740492109135480612711), (Int.ofNat 412139260087228933223031), (Int.ofNat 25031019996878089810655), (Int.negOfNat 1346832177209981429705), (Int.negOfNat 73894825037413445362), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-443496165145289108657473096813391279/562949953421312000000000000000000000), (249016215157197822495854316417832241/562949953421312000000000000000000000), (1194121104717413131663340070214121/14073748835532800000000000000000000), (-8183588944025870826606410220804107/562949953421312000000000000000000000), (-1400672526363141419472815351047381/562949953421312000000000000000000000), (165930508854268470889881430424007/562949953421312000000000000000000000), (22045621663424382770800224168737/562949953421312000000000000000000000), (-2054083616858997851006882306237/562949953421312000000000000000000000), (-27033840297591831274682054199/70368744177664000000000000000000000), (1048116653971881066129030911/35184372088832000000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial144.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial144.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial144.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial144 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 164128415875256885877232454393482633), (Int.ofNat 313461287986905017680105202447265582), (Int.negOfNat 18064595363045333019075526589114167), (Int.negOfNat 10654748259131263277988263579648183), (Int.ofNat 846184429953318314276728121717875), (Int.ofNat 203063337695127741931958762590060), (Int.negOfNat 16557893472795077659792646382353), (Int.negOfNat 2348779948756255127277794575331), (Int.ofNat 183035933992862232834145137931), (Int.ofNat 17969413856919397524359340381), (Int.negOfNat 1320457325653849694025946152), (Int.negOfNat 97069173100820457345819205), (Int.ofNat 6755253623472978781876375), (Int.ofNat 389463340387123588252027), (Int.negOfNat 25906145769733050965248), (Int.negOfNat 1195233288067528941513), (Int.ofNat 80131791462373963092), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(164128415875256885877232454393482633/562949953421312000000000000000000000), (156730643993452508840052601223632791/281474976710656000000000000000000000), (-18064595363045333019075526589114167/562949953421312000000000000000000000), (-10654748259131263277988263579648183/562949953421312000000000000000000000), (6769475439626546514213824973743/4503599627370496000000000000000000), (10153166884756387096597938129503/28147497671065600000000000000000000), (-16557893472795077659792646382353/562949953421312000000000000000000000), (-2348779948756255127277794575331/562949953421312000000000000000000000), (183035933992862232834145137931/562949953421312000000000000000000000), (17969413856919397524359340381/562949953421312000000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial144.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial144.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial144.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial144 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 652285789988971257104987356744096772), (Int.ofNat 152658686969644866561396161458858045), (Int.negOfNat 50598499576725718079541020118039552), (Int.ofNat 673756325514435161516133908211761), (Int.ofNat 1482260929782549658492198595731940), (Int.negOfNat 87437103798527149115429486676348), (Int.negOfNat 22274409913041085490947158072564), (Int.ofNat 1588350351161277727211602522577), (Int.ofNat 204529224636838465052110507228), (Int.negOfNat 15367810546035524463722837203), (Int.negOfNat 1267197070638853118875149202), (Int.ofNat 97168406303240974003215493), (Int.ofNat 5659511480340882164942560), (Int.negOfNat 440129983844537421530500), (Int.negOfNat 19104602418611492130495), (Int.ofNat 1506023422524606839647), (Int.ofNat 47997735158714187089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(163071447497242814276246839186024193/140737488355328000000000000000000000), (30531737393928973312279232291771609/112589990684262400000000000000000000), (-49412597242896209062051777459023/549755813888000000000000000000000), (673756325514435161516133908211761/562949953421312000000000000000000000), (74113046489127482924609929786597/28147497671065600000000000000000000), (-21859275949631787278857371669087/140737488355328000000000000000000000), (-5568602478260271372736789518141/140737488355328000000000000000000000), (1588350351161277727211602522577/562949953421312000000000000000000000), (51132306159209616263027626807/140737488355328000000000000000000000), (-15367810546035524463722837203/562949953421312000000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial144.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial144.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial144.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial144 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 780338562259538239511476350246648209), (Int.negOfNat 4609208928406053535688519434831154), (Int.negOfNat 21971008465785642893237197641624524), (Int.ofNat 6628966825206815501929178555515982), (Int.negOfNat 129112654803218974212812223510461), (Int.negOfNat 167592495289607219697338658327800), (Int.ofNat 9948834428359721962575030079443), (Int.ofNat 2033786465540285538147225760718), (Int.negOfNat 147547348422564283639135534728), (Int.negOfNat 15103880651314185155797480424), (Int.ofNat 1211361442689659745976643059), (Int.ofNat 76539392092939363816916163), (Int.negOfNat 6650326362284892193336772), (Int.negOfNat 282929261076187284648546), (Int.ofNat 26578108187897543571652), (Int.ofNat 769404669825586564918), (Int.negOfNat 80046326170539430773), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(780338562259538239511476350246648209/562949953421312000000000000000000000), (-2304604464203026767844259717415577/281474976710656000000000000000000000), (-5492752116446410723309299410406131/140737488355328000000000000000000000), (3314483412603407750964589277757991/281474976710656000000000000000000000), (-129112654803218974212812223510461/562949953421312000000000000000000000), (-837962476448036098486693291639/2814749767106560000000000000000000), (9948834428359721962575030079443/562949953421312000000000000000000000), (1016893232770142769073612880359/281474976710656000000000000000000000), (-18443418552820535454891941841/70368744177664000000000000000000000), (-1887985081414273144474685053/70368744177664000000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial144.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial144.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial144.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial144 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 729691995663986624900004265815564209), (Int.negOfNat 27842331734400352315113583829543128), (Int.ofNat 4732736405039492433853788499894117), (Int.ofNat 1298524913413366726399813953367686), (Int.negOfNat 846202917143324193567780702942874), (Int.ofNat 37374047534241452572596507100955), (Int.ofNat 16514849106545379938050307704994), (Int.negOfNat 1122011043425716330795961712952), (Int.negOfNat 159174273282023302128639632694), (Int.ofNat 12855220758622846486709010458), (Int.ofNat 951016127784941147416037971), (Int.negOfNat 88419773901369713683240785), (Int.negOfNat 3901302556317303368559191), (Int.ofNat 420253704118570871715215), (Int.ofNat 11644468682871105116244), (Int.negOfNat 1503378293875457449951), (Int.negOfNat 22129133710626439589), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(729691995663986624900004265815564209/562949953421312000000000000000000000), (-3480291466800044039389197978692891/70368744177664000000000000000000000), (4732736405039492433853788499894117/562949953421312000000000000000000000), (649262456706683363199906976683843/281474976710656000000000000000000000), (-423101458571662096783890351471437/281474976710656000000000000000000000), (7474809506848290514519301420191/112589990684262400000000000000000000), (8257424553272689969025153852497/281474976710656000000000000000000000), (-140251380428214541349495214119/70368744177664000000000000000000000), (-79587136641011651064319816347/281474976710656000000000000000000000), (6427610379311423243354505229/281474976710656000000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial144.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial144.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial144.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial144 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 691863146518411480210669070006028203), (Int.negOfNat 14879041942908756311324852402336730), (Int.negOfNat 1803219097392999070395537291795046), (Int.negOfNat 2167655249277199462415054076246327), (Int.ofNat 86536429825059741609818230632897), (Int.ofNat 100714168235936883526906503477325), (Int.negOfNat 6627255596361532340409938875787), (Int.negOfNat 1421646424100954784979558880066), (Int.ofNat 114080320769049788456536689735), (Int.ofNat 10623169416189381331662670948), (Int.negOfNat 1021753951610958497496732035), (Int.negOfNat 49824185327940537609101461), (Int.ofNat 5905857715863509730029776), (Int.ofNat 157874349751037670282378), (Int.negOfNat 24363658544817715357001), (Int.negOfNat 343434051189654563783), (Int.ofNat 79960860878704898454), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(691863146518411480210669070006028203/562949953421312000000000000000000000), (-1487904194290875631132485240233673/56294995342131200000000000000000000), (-901609548696499535197768645897523/281474976710656000000000000000000000), (-2167655249277199462415054076246327/562949953421312000000000000000000000), (86536429825059741609818230632897/562949953421312000000000000000000000), (4028566729437475341076260139093/22517998136852480000000000000000000), (-6627255596361532340409938875787/562949953421312000000000000000000000), (-710823212050477392489779440033/281474976710656000000000000000000000), (22816064153809957691307337947/112589990684262400000000000000000000), (2655792354047345332915667737/140737488355328000000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial144.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial144.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial144.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial144 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 641585785796529816598437543178623944), (Int.negOfNat 39051160640197065850450128640256065), (Int.negOfNat 6980405574552334486651781321245324), (Int.ofNat 941156432379414814075379629281408), (Int.ofNat 453528238990014488250702488482106), (Int.negOfNat 34794143080081541087070312805720), (Int.negOfNat 10419289820314286227685548072771), (Int.ofNat 845613693999980871440647220678), (Int.ofNat 104174066927251625601876054623), (Int.negOfNat 10133639814822878046077025610), (Int.negOfNat 582577823659077923248961960), (Int.ofNat 72995839671339553279543992), (Int.ofNat 1987705230945889358225585), (Int.negOfNat 358026595265240854533077), (Int.negOfNat 3871884541767313416951), (Int.ofNat 1311798833807774106801), (Int.negOfNat 3739467737461307911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(80198223224566227074804692897327993/70368744177664000000000000000000000), (-7810232128039413170090025728051213/112589990684262400000000000000000000), (-1745101393638083621662945330311331/140737488355328000000000000000000000), (7352784627964178234963903353761/4398046511104000000000000000000000), (226764119495007244125351244241053/281474976710656000000000000000000000), (-869853577002038527176757820143/14073748835532800000000000000000000), (-10419289820314286227685548072771/562949953421312000000000000000000000), (422806846999990435720323610339/281474976710656000000000000000000000), (104174066927251625601876054623/562949953421312000000000000000000000), (-1013363981482287804607702561/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial144.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial144.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial144.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial144 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 548696575186210892902961235143209694), (Int.negOfNat 45490006844383538796277671560565477), (Int.ofNat 4970707316338491329244501135208929), (Int.ofNat 2110528838820982754101473047524241), (Int.negOfNat 211608783228623158506525222853284), (Int.negOfNat 65009654601147449215868197458934), (Int.ofNat 5437820642775706800940028342511), (Int.ofNat 890696418301175451303143533389), (Int.negOfNat 85472506759612424711571338125), (Int.negOfNat 6180699449668486359117475045), (Int.ofNat 782440691404069804801276731), (Int.ofNat 23335681991575138341815667), (Int.negOfNat 4648789353461178139853194), (Int.negOfNat 37856549854646017336147), (Int.ofNat 19480197472210963464196), (Int.negOfNat 91041627234540793892), (Int.negOfNat 71252528437507783635), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(274348287593105446451480617571604847/281474976710656000000000000000000000), (-45490006844383538796277671560565477/562949953421312000000000000000000000), (4970707316338491329244501135208929/562949953421312000000000000000000000), (2110528838820982754101473047524241/562949953421312000000000000000000000), (-52902195807155789626631305713321/140737488355328000000000000000000000), (-32504827300573724607934098729467/281474976710656000000000000000000000), (5437820642775706800940028342511/562949953421312000000000000000000000), (890696418301175451303143533389/562949953421312000000000000000000000), (-136756010815379879538514141/900719925474099200000000000000000), (-1236139889933697271823495009/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial144.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial144.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial144.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial144 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 489455386149805920467176977527514227), (Int.negOfNat 10907600690678776471746801331250499), (Int.ofNat 9085832448222624856332285315534098), (Int.negOfNat 987797083431901677697398523494017), (Int.negOfNat 395772769446708676950661494271465), (Int.ofNat 30845820575062558359826716710207), (Int.ofNat 6886330640519888355464977693511), (Int.negOfNat 606389211378530586622132535389), (Int.negOfNat 59957350469660220606445412125), (Int.ofNat 7131364991311197011650113045), (Int.ofNat 259072802232193528231398731), (Int.negOfNat 52363927357526824402974667), (Int.negOfNat 305535388871739963295194), (Int.ofNat 261566659076391798082147), (Int.negOfNat 2753124579044661685804), (Int.negOfNat 967433193384851208108), (Int.ofNat 20928225174963451365), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(489455386149805920467176977527514227/562949953421312000000000000000000000), (-10907600690678776471746801331250499/562949953421312000000000000000000000), (4542916224111312428166142657767049/281474976710656000000000000000000000), (-987797083431901677697398523494017/562949953421312000000000000000000000), (-79154553889341735390132298854293/112589990684262400000000000000000000), (30845820575062558359826716710207/562949953421312000000000000000000000), (6886330640519888355464977693511/562949953421312000000000000000000000), (-606389211378530586622132535389/562949953421312000000000000000000000), (-479658803757281764851563297/4503599627370496000000000000000000), (1426272998262239402330022609/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial144.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial144.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial144.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial144 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 491087408226389048575801479380798646), (Int.ofNat 4391391089415329102513686666757259), (Int.negOfNat 2699658014031775906095230150500241), (Int.negOfNat 2225210824791558024627244891574040), (Int.ofNat 118999582333167407154821730323652), (Int.ofNat 50651613732696719359425872346720), (Int.negOfNat 3394662361801987772349127091771), (Int.negOfNat 548186384698440268356693838678), (Int.ofNat 53056136427404431308626327623), (Int.ofNat 2809871783898752887436506610), (Int.negOfNat 494959858358863219660716960), (Int.negOfNat 2446533710115473504889992), (Int.ofNat 3000579509535746804811585), (Int.negOfNat 55875980108142602229923), (Int.negOfNat 12766470114405799740951), (Int.ofNat 405053119684095664199), (Int.ofNat 53949817277559597089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(245543704113194524287900739690399323/281474976710656000000000000000000000), (4391391089415329102513686666757259/562949953421312000000000000000000000), (-2699658014031775906095230150500241/562949953421312000000000000000000000), (-55630270619788950615681122289351/14073748835532800000000000000000000), (29749895583291851788705432580913/140737488355328000000000000000000000), (316572585829354495996411702167/3518437208883200000000000000000000), (-3394662361801987772349127091771/562949953421312000000000000000000000), (-274093192349220134178346919339/281474976710656000000000000000000000), (53056136427404431308626327623/562949953421312000000000000000000000), (280987178389875288743650661/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial144.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial144.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial144.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial144 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 474521811274379851919618588336982753), (Int.negOfNat 26088706706248403118665544468925190), (Int.negOfNat 10223460923751679304824577021906939), (Int.ofNat 5509596400796903951216843927192), (Int.ofNat 332688550999171773778240536375805), (Int.negOfNat 10487590741530769246625597295825), (Int.negOfNat 4781315615308340528529126880787), (Int.ofNat 282417223513755969537549317066), (Int.ofNat 30761651340476597062275815735), (Int.negOfNat 3627822995911623918408063948), (Int.negOfNat 34495160634853399853366035), (Int.ofNat 27812119408076828541373461), (Int.negOfNat 858712685041258959456224), (Int.negOfNat 141854602798368814997378), (Int.ofNat 7246028269320087006999), (Int.ofNat 503514996766856166783), (Int.negOfNat 29465627032491501546), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(474521811274379851919618588336982753/562949953421312000000000000000000000), (-2608870670624840311866554446892519/56294995342131200000000000000000000), (-10223460923751679304824577021906939/562949953421312000000000000000000000), (688699550099612993902105490899/70368744177664000000000000000000000), (66537710199834354755648107275161/112589990684262400000000000000000000), (-419503629661230769865023891833/22517998136852480000000000000000000), (-4781315615308340528529126880787/562949953421312000000000000000000000), (141208611756877984768774658533/281474976710656000000000000000000000), (6152330268095319412455163147/112589990684262400000000000000000000), (-906955748977905979602015987/140737488355328000000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial144.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial144.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial144.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial144 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 386218224682839394676505677986429114), (Int.negOfNat 57877648186385380462162842800346198), (Int.negOfNat 3963900706456931135009741454531245), (Int.ofNat 1676792076311690478192585234353900), (Int.ofNat 40395197617934129835426732145853), (Int.negOfNat 37253746298509095342057254948682), (Int.ofNat 399841870452363346652391350494), (Int.ofNat 332396751645540187635170265952), (Int.negOfNat 14986861725383515657257996694), (Int.negOfNat 759002379087140280865100458), (Int.ofNat 172453791450247719179759971), (Int.negOfNat 9945260799939402854132215), (Int.negOfNat 1128518825842291943158191), (Int.ofNat 108936185507021062740785), (Int.ofNat 4897108836883278944244), (Int.negOfNat 577249771398122605049), (Int.negOfNat 28081215829471849589), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(193109112341419697338252838993214557/281474976710656000000000000000000000), (-28938824093192690231081421400173099/281474976710656000000000000000000000), (-792780141291386227001948290906249/112589990684262400000000000000000000), (16767920763116904781925852343539/5629499534213120000000000000000000), (40395197617934129835426732145853/562949953421312000000000000000000000), (-18626873149254547671028627474341/281474976710656000000000000000000000), (199920935226181673326195675247/281474976710656000000000000000000000), (10387398488923130863599070811/17592186044416000000000000000000000), (-7493430862691757828628998347/281474976710656000000000000000000000), (-379501189543570140432550229/281474976710656000000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial144.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial144.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial144.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial144 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 267539929349587592083355522823010797), (Int.negOfNat 55090061953911774096073489435044668), (Int.ofNat 4376664585090069014894457488929823), (Int.ofNat 731119983290870299915062546243564), (Int.negOfNat 233128307047415693416367312482369), (Int.negOfNat 11757289129759798160159946182200), (Int.ofNat 3256662151324402767272200943670), (Int.ofNat 80883504555544026375683035282), (Int.negOfNat 14739732255181941955564166728), (Int.negOfNat 116751619843999968359744576), (Int.negOfNat 74309317708006561415954941), (Int.negOfNat 1805740421975718122430163), (Int.ofNat 1359052927831081793874228), (Int.ofNat 13842626034907968969546), (Int.negOfNat 8862448655158293550348), (Int.negOfNat 32707431869079587918), (Int.ofNat 29380161740656969227), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(267539929349587592083355522823010797/562949953421312000000000000000000000), (-13772515488477943524018372358761167/140737488355328000000000000000000000), (4376664585090069014894457488929823/562949953421312000000000000000000000), (182779995822717574978765636560891/140737488355328000000000000000000000), (-233128307047415693416367312482369/562949953421312000000000000000000000), (-58786445648798990800799730911/2814749767106560000000000000000000), (325666215132440276727220094367/56294995342131200000000000000000000), (40441752277772013187841517641/281474976710656000000000000000000000), (-1842466531897742744445520841/70368744177664000000000000000000000), (-1824244060062499505621009/8796093022208000000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial144.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial144.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial144.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial144 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 176824009545031946799675434566127214), (Int.negOfNat 36564867992195914069005284109901854), (Int.ofNat 3035906895716183104841386701366862), (Int.negOfNat 1065945691444238531279835672440120), (Int.negOfNat 150540041964413891696926553364106), (Int.ofNat 26758850826036093187984243363075), (Int.ofNat 2460079384788583744884920384436), (Int.negOfNat 220454426951437187635841278577), (Int.negOfNat 22900712354877111391105370772), (Int.ofNat 15922958349351102915962203), (Int.ofNat 147073074436918867106680798), (Int.ofNat 12933574976245053679832507), (Int.negOfNat 732162478817112895923440), (Int.negOfNat 115411808196400844323500), (Int.ofNat 2968895783710596243505), (Int.ofNat 593466068556180199353), (Int.ofNat 2212614381384102089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(88412004772515973399837717283063607/281474976710656000000000000000000000), (-18282433996097957034502642054950927/281474976710656000000000000000000000), (1517953447858091552420693350683431/281474976710656000000000000000000000), (-26648642286105963281995891811003/14073748835532800000000000000000000), (-75270020982206945848463276682053/281474976710656000000000000000000000), (1070354033041443727519369734523/22517998136852480000000000000000000), (615019846197145936221230096109/140737488355328000000000000000000000), (-220454426951437187635841278577/562949953421312000000000000000000000), (-5725178088719277847776342693/140737488355328000000000000000000000), (15922958349351102915962203/562949953421312000000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial144.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial144.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial144.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial144 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 105881523864233032016980793434830186), (Int.negOfNat 39538128933142568171067272102696837), (Int.negOfNat 4428719069215957012756173849319925), (Int.negOfNat 968013930465621447114930564412274), (Int.ofNat 179733897609953479653444490359783), (Int.ofNat 28995075458566274675630197778940), (Int.negOfNat 2560091785963972034784586509353), (Int.negOfNat 404159119670027793546020026669), (Int.ofNat 11372243279968450697980220931), (Int.ofNat 3543833010049627441785874619), (Int.ofNat 67910170627965389690623848), (Int.negOfNat 22138159973426098673658795), (Int.negOfNat 1171464085960407933594625), (Int.ofNat 104928530095234139599973), (Int.ofNat 7587364618315675893752), (Int.negOfNat 403750664825236285487), (Int.negOfNat 29294696448822436908), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(52940761932116516008490396717415093/281474976710656000000000000000000000), (-39538128933142568171067272102696837/562949953421312000000000000000000000), (-177148762768638280510246953972797/22517998136852480000000000000000000), (-484006965232810723557465282206137/281474976710656000000000000000000000), (179733897609953479653444490359783/562949953421312000000000000000000000), (1449753772928313733781509888947/28147497671065600000000000000000000), (-2560091785963972034784586509353/562949953421312000000000000000000000), (-404159119670027793546020026669/562949953421312000000000000000000000), (11372243279968450697980220931/562949953421312000000000000000000000), (3543833010049627441785874619/562949953421312000000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial144.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial144.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial144.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial144 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.ofNat 4939030921617055672437922933935248), (Int.negOfNat 61450796458346171646096524465111030), (Int.negOfNat 4452792031659515614082512082759034), (Int.ofNat 1033158771716273863753423619765785), (Int.ofNat 229814318240772874915110104547438), (Int.negOfNat 23621030023622345218220585972734), (Int.negOfNat 4703873132408519383882439737263), (Int.ofNat 220798242510039283888058905237), (Int.ofNat 54264602349374423698230048408), (Int.negOfNat 503104646035492148685158576), (Int.negOfNat 416050232641060049142814323), (Int.negOfNat 7000858370410061833863278), (Int.ofNat 2312788312604653954087289), (Int.ofNat 76911668296671712121969), (Int.negOfNat 9696531829044037164345), (Int.negOfNat 426604053703509293295), (Int.ofNat 23627498636092134638), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(308689432601065979527370183370953/35184372088832000000000000000000000), (-6145079645834617164609652446511103/56294995342131200000000000000000000), (-2226396015829757807041256041379517/281474976710656000000000000000000000), (206631754343254772750684723953157/112589990684262400000000000000000000), (114907159120386437457555052273719/281474976710656000000000000000000000), (-11810515011811172609110292986367/281474976710656000000000000000000000), (-4703873132408519383882439737263/562949953421312000000000000000000000), (220798242510039283888058905237/562949953421312000000000000000000000), (6783075293671802962278756051/70368744177664000000000000000000000), (-31444040377218259292822411/35184372088832000000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial144.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial144.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial144.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial144 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 124846885815320681254097249421210694), (Int.negOfNat 62151651077608414017939200704987952), (Int.ofNat 4481567181210829268900733345061013), (Int.ofNat 1385985799865903615165716565272929), (Int.negOfNat 173634134063381775322453321253073), (Int.negOfNat 41537367929891971297692883228507), (Int.ofNat 2770811719654310968876650556263), (Int.ofNat 642516564912624952015819900237), (Int.negOfNat 19532312136048277880463281408), (Int.negOfNat 6117227667787287759669682576), (Int.ofNat 39714881642570163851207323), (Int.ofNat 40371798520220926122459722), (Int.ofNat 374903186217109784370711), (Int.negOfNat 196595964771271238073031), (Int.negOfNat 3729654696433988488655), (Int.ofNat 750851541574517119705), (Int.ofNat 11991985288874250362), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-62423442907660340627048624710605347/281474976710656000000000000000000000), (-3884478192350525876121200044061747/35184372088832000000000000000000000), (4481567181210829268900733345061013/562949953421312000000000000000000000), (1385985799865903615165716565272929/562949953421312000000000000000000000), (-173634134063381775322453321253073/562949953421312000000000000000000000), (-41537367929891971297692883228507/562949953421312000000000000000000000), (2770811719654310968876650556263/562949953421312000000000000000000000), (642516564912624952015819900237/562949953421312000000000000000000000), (-76298094281438585470559693/2199023255552000000000000000000000), (-382326729236705484979355161/35184372088832000000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial144.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial144.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial144.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial144 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 223991809749213897546183916743332807), (Int.negOfNat 35686429794402973575731999241318327), (Int.ofNat 6342436770256605075223963882848409), (Int.negOfNat 927032329678088186723033838113133), (Int.negOfNat 287182386594051543887358213179194), (Int.ofNat 26086710567380298596475440577440), (Int.ofNat 6176044544625232148082815854353), (Int.negOfNat 312047243867730038082620497669), (Int.negOfNat 74410632117996481963784449931), (Int.ofNat 1978064694260291099047420619), (Int.ofNat 591316394253159347488264152), (Int.negOfNat 6141343455090404210576795), (Int.negOfNat 3365113011468530856700375), (Int.negOfNat 1583347753231378124027), (Int.ofNat 14358198614845064204248), (Int.ofNat 138651990920880521513), (Int.negOfNat 40816256073594278092), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-223991809749213897546183916743332807/562949953421312000000000000000000000), (-35686429794402973575731999241318327/562949953421312000000000000000000000), (6342436770256605075223963882848409/562949953421312000000000000000000000), (-927032329678088186723033838113133/562949953421312000000000000000000000), (-143591193297025771943679106589597/281474976710656000000000000000000000), (163041941046126866227971503609/3518437208883200000000000000000000), (6176044544625232148082815854353/562949953421312000000000000000000000), (-312047243867730038082620497669/562949953421312000000000000000000000), (-74410632117996481963784449931/562949953421312000000000000000000000), (1978064694260291099047420619/562949953421312000000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial144.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial144.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial144.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial144 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 280833456521049745687489601832644557), (Int.negOfNat 27566728607179690252285017955518509), (Int.negOfNat 2870454934394742510126062779025307), (Int.negOfNat 1481857723816586136500005335202402), (Int.ofNat 188785344998823662644814475891287), (Int.ofNat 48898831410891000491534894124848), (Int.negOfNat 3489749331446818948252194463436), (Int.negOfNat 761796527340655522695947964577), (Int.ofNat 35497235607172516920989641772), (Int.ofNat 7396588551521366366479637203), (Int.negOfNat 219933733166039734839981798), (Int.negOfNat 49822305134226059080578493), (Int.ofNat 866616064966361144312440), (Int.ofNat 246228471970084889956500), (Int.negOfNat 2152971310154562478505), (Int.negOfNat 926576752181647854647), (Int.ofNat 13905104589825007911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-280833456521049745687489601832644557/562949953421312000000000000000000000), (-27566728607179690252285017955518509/562949953421312000000000000000000000), (-2870454934394742510126062779025307/562949953421312000000000000000000000), (-740928861908293068250002667601201/281474976710656000000000000000000000), (188785344998823662644814475891287/562949953421312000000000000000000000), (3056176963180687530720930882803/35184372088832000000000000000000000), (-872437332861704737063048615859/140737488355328000000000000000000000), (-761796527340655522695947964577/562949953421312000000000000000000000), (8874308901793129230247410443/140737488355328000000000000000000000), (7396588551521366366479637203/562949953421312000000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial144.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial144.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial144.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial144 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 355026568451911919322950073043116121), (Int.negOfNat 47837382603351353107197709208020797), (Int.negOfNat 4574459370785454638696983983804629), (Int.ofNat 1097471224843994476065024985042472), (Int.ofNat 319800469860296377340006891074553), (Int.negOfNat 29237437926264535386465434205200), (Int.negOfNat 6582842177268977594264752449943), (Int.ofNat 443683333417287573558380791282), (Int.ofNat 79156833110342863638216754728), (Int.negOfNat 4033410850750451602160278576), (Int.negOfNat 639022655974699591748329059), (Int.ofNat 23802543570706527592221837), (Int.ofNat 3702422303157525834364772), (Int.negOfNat 97082742951716602937454), (Int.negOfNat 15970788741877826362652), (Int.ofNat 270642662028556530082), (Int.ofNat 40730790781759745773), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-355026568451911919322950073043116121/562949953421312000000000000000000000), (-47837382603351353107197709208020797/562949953421312000000000000000000000), (-4574459370785454638696983983804629/562949953421312000000000000000000000), (137183903105499309508128123130309/70368744177664000000000000000000000), (319800469860296377340006891074553/562949953421312000000000000000000000), (-73093594815661338466163585513/1407374883553280000000000000000000), (-6582842177268977594264752449943/562949953421312000000000000000000000), (221841666708643786779190395641/281474976710656000000000000000000000), (9894604138792857954777094341/70368744177664000000000000000000000), (-252088178171903225135017411/35184372088832000000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial144.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial144.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial144.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial144 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 456385094719412525506025646437528304), (Int.negOfNat 46067236931677525739530806155721546), (Int.ofNat 6181658228938289875860932199439521), (Int.ofNat 1793318300696216919150964110484728), (Int.negOfNat 178084795271925259220617782179626), (Int.negOfNat 47752238355611280440131623418228), (Int.ofNat 4175085651064768573947846292006), (Int.ofNat 718502283582435006211121675952), (Int.negOfNat 54402743162577564515146077306), (Int.negOfNat 7034646867592633666023691458), (Int.ofNat 435311704657064971656081029), (Int.ofNat 48415179013921719322422785), (Int.negOfNat 2333466592740677764512809), (Int.negOfNat 244469653972662556259215), (Int.ofNat 8898832195210395082756), (Int.ofNat 940465588825003789951), (Int.negOfNat 39773706037912755411), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-28524068419963282844126602902345519/35184372088832000000000000000000000), (-23033618465838762869765403077860773/281474976710656000000000000000000000), (6181658228938289875860932199439521/562949953421312000000000000000000000), (224164787587027114893870513810591/70368744177664000000000000000000000), (-89042397635962629610308891089813/281474976710656000000000000000000000), (-11938059588902820110032905854557/140737488355328000000000000000000000), (2087542825532384286973923146003/281474976710656000000000000000000000), (44906392723902187888195104747/35184372088832000000000000000000000), (-27201371581288782257573038653/281474976710656000000000000000000000), (-3517323433796316833011845729/281474976710656000000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial144.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial144.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial144.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial144 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 513481639152867769129199829578173153), (Int.negOfNat 8285382675450696438220699998974350), (Int.ofNat 10208488072716238019268196170979880), (Int.negOfNat 597977337502097887353167028165538), (Int.negOfNat 285694199826544828185317014797216), (Int.ofNat 28785217672470894377336224526948), (Int.ofNat 5409434035971940528165759984787), (Int.negOfNat 572129114142616996358396532934), (Int.negOfNat 64942524778227750785110100735), (Int.ofNat 6237449503934827327692029052), (Int.ofNat 538659345654762132477651035), (Int.negOfNat 42900800282526330667505539), (Int.negOfNat 3230250461212550424434776), (Int.ofNat 202960378871971500771622), (Int.ofNat 14438324556446783403001), (Int.negOfNat 680079315371983206217), (Int.negOfNat 40645325489925213454), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-513481639152867769129199829578173153/562949953421312000000000000000000000), (-165707653509013928764413999979487/11258999068426240000000000000000000), (255212201817905950481704904274497/14073748835532800000000000000000000), (-298988668751048943676583514082769/281474976710656000000000000000000000), (-8927943744579525880791156712413/17592186044416000000000000000000000), (7196304418117723594334056131737/140737488355328000000000000000000000), (5409434035971940528165759984787/562949953421312000000000000000000000), (-286064557071308498179198266467/281474976710656000000000000000000000), (-12988504955645550157022020147/112589990684262400000000000000000000), (1559362375983706831923007263/140737488355328000000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial144.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial144.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial144.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial144 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 497392259237754878115234750775569742), (Int.ofNat 19265819589172944071547409315908371), (Int.ofNat 2897755277695532132970328335579680), (Int.negOfNat 1263683091942861975390798606050776), (Int.ofNat 124046504443200540836677395273940), (Int.ofNat 31946886126338357878843262975493), (Int.negOfNat 4644251143431700259250648785229), (Int.negOfNat 477076722023146875795623952678), (Int.ofNat 72490164863182548248552658377), (Int.ofNat 4848704589568233597348314610), (Int.negOfNat 649783937877041464297505040), (Int.negOfNat 35459714278295448262932992), (Int.ofNat 3795701700611604539275415), (Int.ofNat 189393811614958114420077), (Int.negOfNat 15658195287668742099049), (Int.negOfNat 765420094049825771801), (Int.ofNat 65642307486000502911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-248696129618877439057617375387784871/281474976710656000000000000000000000), (19265819589172944071547409315908371/562949953421312000000000000000000000), (18110970485597075831064552097373/3518437208883200000000000000000000), (-157960386492857746923849825756347/70368744177664000000000000000000000), (6202325222160027041833869763697/28147497671065600000000000000000000), (31946886126338357878843262975493/562949953421312000000000000000000000), (-4644251143431700259250648785229/562949953421312000000000000000000000), (-238538361011573437897811976339/281474976710656000000000000000000000), (72490164863182548248552658377/562949953421312000000000000000000000), (484870458956823359734831461/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial144.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial144.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial144.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial144 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 454709998310814460318784674937370661), (Int.ofNat 21194232485697546680063729184431226), (Int.negOfNat 442650554756188596319354067784260), (Int.ofNat 141281935574974421546735976278762), (Int.ofNat 122319427940919921476083908921103), (Int.negOfNat 27467015902127875787866147424566), (Int.negOfNat 2401072286320958524536882200011), (Int.ofNat 679155694873470483162988912611), (Int.ofNat 30411462320015053386486253125), (Int.negOfNat 8264240204640434289056886955), (Int.negOfNat 288846990441156035680198731), (Int.ofNat 60666396841321503690037333), (Int.ofNat 1971473535975671690316194), (Int.negOfNat 300489693412848485468853), (Int.negOfNat 9635835932464803587196), (Int.ofNat 1081487063211167913892), (Int.ofNat 31936993048728098635), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-454709998310814460318784674937370661/562949953421312000000000000000000000), (10597116242848773340031864592215613/281474976710656000000000000000000000), (-22132527737809429815967703389213/28147497671065600000000000000000000), (70640967787487210773367988139381/281474976710656000000000000000000000), (122319427940919921476083908921103/562949953421312000000000000000000000), (-13733507951063937893933073712283/281474976710656000000000000000000000), (-2401072286320958524536882200011/562949953421312000000000000000000000), (679155694873470483162988912611/562949953421312000000000000000000000), (9731667942404817083675601/180143985094819840000000000000000), (-1652848040928086857811377391/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial144.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial144.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial144.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial144 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 411947062431925045949707548780245260), (Int.ofNat 22690466387126449112349930863325475), (Int.ofNat 1038360524825454551617709507522733), (Int.ofNat 25635989899896620852346658160020), (Int.negOfNat 106698466995174226649517412742354), (Int.negOfNat 2708141689993526563046421680207), (Int.ofNat 4932124952795979709608459016489), (Int.ofNat 33359701948279405191862411389), (Int.negOfNat 87908118245655560384214102875), (Int.negOfNat 903206004252999907005965045), (Int.ofNat 837920206970203633810293269), (Int.ofNat 12025372544028283985117667), (Int.negOfNat 5057250257138939006262806), (Int.negOfNat 87282726093223159432147), (Int.ofNat 21309786911600713463804), (Int.ofNat 421054453626902873108), (Int.negOfNat 82831064923502646365), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-20597353121596252297485377439012263/28147497671065600000000000000000000), (907618655485057964493997234533019/22517998136852480000000000000000000), (1038360524825454551617709507522733/562949953421312000000000000000000000), (1281799494994831042617332908001/28147497671065600000000000000000000), (-53349233497587113324758706371177/281474976710656000000000000000000000), (-2708141689993526563046421680207/562949953421312000000000000000000000), (4932124952795979709608459016489/562949953421312000000000000000000000), (33359701948279405191862411389/562949953421312000000000000000000000), (-703264945965244483073712823/4503599627370496000000000000000000), (-180641200850599981401193009/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial144.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial144.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial144.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial144 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 363703614938190806820096023354550848), (Int.ofNat 24394651510325965028292070384785547), (Int.negOfNat 531159766562916145111640381542342), (Int.negOfNat 278043401670951386202133945602828), (Int.ofNat 80508829928777628377107158431802), (Int.ofNat 24669520761009913580435910843053), (Int.negOfNat 2361645283954600487287936555229), (Int.negOfNat 763442384058893250210248688322), (Int.ofNat 23096976238610878343177164377), (Int.ofNat 9998363350343002926032517390), (Int.negOfNat 86839615318259639267296040), (Int.negOfNat 75219939315018177918134008), (Int.negOfNat 84644842134586445872585), (Int.ofNat 376989789972873854421923), (Int.ofNat 2468482018003696526951), (Int.negOfNat 1395498555660722784199), (Int.negOfNat 14634281888779912089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-5682868983409231356564000364914857/8796093022208000000000000000000000), (24394651510325965028292070384785547/562949953421312000000000000000000000), (-265579883281458072555820190771171/281474976710656000000000000000000000), (-69510850417737846550533486400707/140737488355328000000000000000000000), (40254414964388814188553579215901/281474976710656000000000000000000000), (24669520761009913580435910843053/562949953421312000000000000000000000), (-2361645283954600487287936555229/562949953421312000000000000000000000), (-381721192029446625105124344161/281474976710656000000000000000000000), (23096976238610878343177164377/562949953421312000000000000000000000), (999836335034300292603251739/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial144.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial144.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial144.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial144 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 317423806427884672702691291608500303), (Int.ofNat 22733291326387715681981958999413110), (Int.ofNat 710923115732790603011568784585605), (Int.ofNat 638147017347537577075087685730943), (Int.ofNat 33704947464305116898530121754287), (Int.negOfNat 40105754314346936503390523433175), (Int.negOfNat 5071780013791245159681324758213), (Int.ofNat 603404911029537611910249939934), (Int.ofNat 102341273150927859053749730265), (Int.negOfNat 4402540799848503221445051052), (Int.negOfNat 991600924857303116293082965), (Int.ofNat 18687419471315934547119539), (Int.ofNat 5981721243582432738431224), (Int.negOfNat 46724832975327131078622), (Int.negOfNat 25227981379858610197999), (Int.ofNat 42863742991092168217), (Int.ofNat 91368466781030696546), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-317423806427884672702691291608500303/562949953421312000000000000000000000), (2273329132638771568198195899941311/56294995342131200000000000000000000), (142184623146558120602313756917121/112589990684262400000000000000000000), (638147017347537577075087685730943/562949953421312000000000000000000000), (33704947464305116898530121754287/562949953421312000000000000000000000), (-1604230172573877460135620937327/22517998136852480000000000000000000), (-5071780013791245159681324758213/562949953421312000000000000000000000), (301702455514768805955124969967/281474976710656000000000000000000000), (20468254630185571810749946053/112589990684262400000000000000000000), (-1100635199962125805361262763/140737488355328000000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial144.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial144.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial144.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial144 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 264976826395287953399797038029866246), (Int.ofNat 30491318792733127896546434016899024), (Int.ofNat 1481123747080960789205769357970107), (Int.negOfNat 1024094038798183805678216250100986), (Int.negOfNat 417656869370560082568248582354353), (Int.negOfNat 20185484470037268458390695714091), (Int.ofNat 9148920605940260246345859691733), (Int.ofNat 889542763533816890627635947048), (Int.negOfNat 89832790229501154630398493306), (Int.negOfNat 11619709276006411504596310542), (Int.ofNat 530993170937089032168356029), (Int.ofNat 85650992101630649106474215), (Int.negOfNat 2129304280315144761319809), (Int.negOfNat 423193106827178167719785), (Int.ofNat 6126565419584524596756), (Int.ofNat 1534627276789739075049), (Int.negOfNat 11234319559307835411), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-132488413197643976699898519014933123/281474976710656000000000000000000000), (1905707424545820493534152126056189/35184372088832000000000000000000000), (1481123747080960789205769357970107/562949953421312000000000000000000000), (-512047019399091902839108125050493/281474976710656000000000000000000000), (-417656869370560082568248582354353/562949953421312000000000000000000000), (-20185484470037268458390695714091/562949953421312000000000000000000000), (9148920605940260246345859691733/562949953421312000000000000000000000), (111192845441727111328454493381/70368744177664000000000000000000000), (-44916395114750577315199246653/281474976710656000000000000000000000), (-5809854638003205752298155271/281474976710656000000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial144.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial144.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial144.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial144 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 212919738526254249717323139070818885), (Int.ofNat 11186783730352785166455276426836217), (Int.negOfNat 13714733373441873623025249704846943), (Int.negOfNat 3422827537247985858813326698165110), (Int.ofNat 41372212496351074205435904043277), (Int.ofNat 107122690293514152942653236854200), (Int.ofNat 6572770059018539106212778904330), (Int.negOfNat 1354407921446412620797957993282), (Int.negOfNat 122295000022584115091965278272), (Int.ofNat 10093587865670675270488660576), (Int.ofNat 1113524870690604718853040941), (Int.negOfNat 51179344898299222180396837), (Int.negOfNat 6479471357196521864997228), (Int.ofNat 190486074314990905704454), (Int.ofNat 26765044282341115551348), (Int.negOfNat 530205273181374072082), (Int.negOfNat 91283001489196164227), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-42583947705250849943464627814163777/112589990684262400000000000000000000), (11186783730352785166455276426836217/562949953421312000000000000000000000), (-13714733373441873623025249704846943/562949953421312000000000000000000000), (-342282753724798585881332669816511/56294995342131200000000000000000000), (41372212496351074205435904043277/562949953421312000000000000000000000), (535613451467570764713266184271/2814749767106560000000000000000000), (657277005901853910621277890433/56294995342131200000000000000000000), (-677203960723206310398978996641/281474976710656000000000000000000000), (-1910859375352876798311957473/8796093022208000000000000000000000), (315424620802208602202770643/17592186044416000000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial144.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial144.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial144.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial144 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 268475679031083196220334267158374929), (Int.negOfNat 74294152977574777250885689993573610), (Int.negOfNat 24183300501347655628677156495610776), (Int.ofNat 1335629477613996779179738173520206), (Int.ofNat 1043535988808752773181923327627379), (Int.ofNat 44683332909284439759500363689698), (Int.negOfNat 16641065341627741498502043930436), (Int.negOfNat 1191778531236244281090861708423), (Int.ofNat 153240543015469742288729416772), (Int.ofNat 13310777020785324330718147797), (Int.negOfNat 948320748882630358598679798), (Int.negOfNat 91122481453705072424830507), (Int.ofNat 4265636594359404303698440), (Int.ofNat 432862250309914151759500), (Int.negOfNat 14641487567242174389505), (Int.negOfNat 1534309608655291344353), (Int.ofNat 37102921007395582911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-268475679031083196220334267158374929/562949953421312000000000000000000000), (-7429415297757477725088568999357361/56294995342131200000000000000000000), (-3022912562668456953584644561951347/70368744177664000000000000000000000), (667814738806998389589869086760103/281474976710656000000000000000000000), (1043535988808752773181923327627379/562949953421312000000000000000000000), (22341666454642219879750181844849/281474976710656000000000000000000000), (-4160266335406935374625510982609/140737488355328000000000000000000000), (-1191778531236244281090861708423/562949953421312000000000000000000000), (38310135753867435572182354193/140737488355328000000000000000000000), (13310777020785324330718147797/562949953421312000000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial144.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial144.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial144.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial144 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 486158376802146261420210068952026512), (Int.negOfNat 121579153914891199696884598405549408), (Int.ofNat 7978079075119009194527037314999683), (Int.ofNat 8469628543308193886619403027148458), (Int.ofNat 367591506220569326706493068633536), (Int.negOfNat 169418342233279348355827677350713), (Int.negOfNat 11419119291649708208119824502647), (Int.ofNat 1932311379962324763743880918669), (Int.ofNat 149570698873664932875551366069), (Int.negOfNat 14589247332505666497196698619), (Int.negOfNat 1188350322756573611047246848), (Int.ofNat 78676921764989836547767795), (Int.ofNat 6463281250687078330958625), (Int.negOfNat 318583344723508408541973), (Int.negOfNat 25726084925396192302752), (Int.ofNat 983197335168195270487), (Int.ofNat 91197536197361631908), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-30384898550134141338763129309501657/35184372088832000000000000000000000), (-3799348559840349990527643700173419/17592186044416000000000000000000000), (7978079075119009194527037314999683/562949953421312000000000000000000000), (4234814271654096943309701513574229/281474976710656000000000000000000000), (5743617284696395729788954197399/8796093022208000000000000000000000), (-169418342233279348355827677350713/562949953421312000000000000000000000), (-11419119291649708208119824502647/562949953421312000000000000000000000), (1932311379962324763743880918669/562949953421312000000000000000000000), (149570698873664932875551366069/562949953421312000000000000000000000), (-14589247332505666497196698619/562949953421312000000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial144.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial144.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial144.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial144 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 629640962471194081733932238274872548), (Int.ofNat 8965858164862549151576109761794819), (Int.ofNat 52812210249910684067229396642686681), (Int.ofNat 4063949087587848624737900565480537), (Int.negOfNat 1373965294526765477382071915889984), (Int.negOfNat 113266797882359691247798983901766), (Int.ofNat 20047089511198116403560657763036), (Int.ofNat 1618759263184432561466481083763), (Int.negOfNat 188913578749110802974809408408), (Int.negOfNat 14547789665419196486706744424), (Int.ofNat 1236520631070142210673191323), (Int.ofNat 89733169356453590346005278), (Int.negOfNat 5927629857831549800485289), (Int.negOfNat 402039066825974768836969), (Int.ofNat 21648503644710451287345), (Int.ofNat 1350913628510115113295), (Int.negOfNat 62943034024871819638), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-157410240617798520433483059568718137/140737488355328000000000000000000000), (8965858164862549151576109761794819/562949953421312000000000000000000000), (52812210249910684067229396642686681/562949953421312000000000000000000000), (4063949087587848624737900565480537/562949953421312000000000000000000000), (-21468207726980710584094873685781/8796093022208000000000000000000000), (-56633398941179845623899491950883/281474976710656000000000000000000000), (5011772377799529100890164440759/140737488355328000000000000000000000), (1618759263184432561466481083763/562949953421312000000000000000000000), (-23614197343638850371851176051/70368744177664000000000000000000000), (-1818473708177399560838343053/70368744177664000000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial144.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial144.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial144.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial144.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial144 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial144 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial144 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 711109512487476428876418710681173721), (Int.negOfNat 12948574627997267618805712816885241), (Int.ofNat 56201034258304172856225052038245160), (Int.negOfNat 5433829772392772182536552560412893), (Int.negOfNat 1449511744627428602349411009468619), (Int.ofNat 154116434968804662877272740107993), (Int.ofNat 21097262841089229520658275202263), (Int.negOfNat 2137316904772760331431336098763), (Int.negOfNat 197674295267070401355160583408), (Int.ofNat 18293646668747854045920894424), (Int.ofNat 1284151093723310274379071323), (Int.negOfNat 107272932677264968321080278), (Int.negOfNat 6108247766635736422535289), (Int.ofNat 459739559887271604311969), (Int.ofNat 22144522603485611037345), (Int.negOfNat 1499719316142663038295), (Int.negOfNat 62943034024871819638), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-711109512487476428876418710681173721/562949953421312000000000000000000000), (-12948574627997267618805712816885241/562949953421312000000000000000000000), (1405025856457604321405626300956129/14073748835532800000000000000000000), (-5433829772392772182536552560412893/562949953421312000000000000000000000), (-1449511744627428602349411009468619/562949953421312000000000000000000000), (154116434968804662877272740107993/562949953421312000000000000000000000), (21097262841089229520658275202263/562949953421312000000000000000000000), (-2137316904772760331431336098763/562949953421312000000000000000000000), (-12354643454191900084697536463/35184372088832000000000000000000000), (2286705833593481755740111803/70368744177664000000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial144.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial144.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial144.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 572897140565522293214036442605881633), (Int.ofNat 115532673723835238649200074466270418), (Int.ofNat 4507659564662389781367692883839167), (Int.negOfNat 8927833986047644633041433837087817), (Int.ofNat 623544599803780978724806349567125), (Int.ofNat 182804312204892531636861063527940), (Int.negOfNat 16189996270488395534679850952647), (Int.negOfNat 2096777683702822503814250088669), (Int.ofNat 194581445397232202722052711069), (Int.ofNat 15758016959325573716145443619), (Int.negOfNat 1447692828428919839947901848), (Int.negOfNat 84108038712764793747542795), (Int.ofNat 7473956642384648545558625), (Int.ofNat 336390425343536643566973), (Int.negOfNat 28586460920999613527752), (Int.negOfNat 1032799231045711245487), (Int.ofNat 91197536197361631908), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-572897140565522293214036442605881633/562949953421312000000000000000000000), (57766336861917619324600037233135209/281474976710656000000000000000000000), (4507659564662389781367692883839167/562949953421312000000000000000000000), (-8927833986047644633041433837087817/562949953421312000000000000000000000), (4988356798430247829798450796537/4503599627370496000000000000000000), (9140215610244626581843053176397/28147497671065600000000000000000000), (-16189996270488395534679850952647/562949953421312000000000000000000000), (-2096777683702822503814250088669/562949953421312000000000000000000000), (194581445397232202722052711069/562949953421312000000000000000000000), (15758016959325573716145443619/562949953421312000000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial144.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial144.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial144.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 380645663328079734150043253245976772), (Int.ofNat 57186637032030596135915528842679955), (Int.negOfNat 24361758211651180428199616554017448), (Int.ofNat 16633711344223981773250325643239), (Int.ofNat 1152586733428195276695191876277060), (Int.negOfNat 81988602605019416982301891052652), (Int.negOfNat 18778111255198647049203566858436), (Int.ofNat 1664425106809843434021677873423), (Int.ofNat 173613508550368300842655951772), (Int.negOfNat 16728465209827091101791592797), (Int.negOfNat 1066173484164979130180549798), (Int.ofNat 107134951929608726478105507), (Int.ofNat 4725673726899667265973440), (Int.negOfNat 485552951887581873759500), (Int.negOfNat 15947670825350095064505), (Int.ofNat 1650047365702828619353), (Int.ofNat 37102921007395582911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-95161415832019933537510813311494193/140737488355328000000000000000000000), (11437327406406119227183105768535991/112589990684262400000000000000000000), (-3045219776456397553524952069252181/70368744177664000000000000000000000), (16633711344223981773250325643239/562949953421312000000000000000000000), (57629336671409763834759593813853/28147497671065600000000000000000000), (-20497150651254854245575472763163/140737488355328000000000000000000000), (-4694527813799661762300891714609/140737488355328000000000000000000000), (1664425106809843434021677873423/562949953421312000000000000000000000), (43403377137592075210663987943/140737488355328000000000000000000000), (-16728465209827091101791592797/562949953421312000000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial144.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial144.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial144.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 348722329765758485317445476685451209), (Int.negOfNat 12461764238923784917965168480305846), (Int.negOfNat 6322212967849356411733784157489476), (Int.ofNat 4095077326084738568673854771841018), (Int.negOfNat 210343355428887651404046734244539), (Int.negOfNat 128581701071437067183267880149200), (Int.ofNat 10893595097360866160289491588557), (Int.ofNat 1637812637485742804368096473282), (Int.negOfNat 162179625901663886711169823272), (Int.negOfNat 12177684973424884708041955576), (Int.ofNat 1341286847219688946437995941), (Int.ofNat 61017109216258588199996837), (Int.negOfNat 7363440448269829966872228), (Int.negOfNat 222929412487212482854454), (Int.ofNat 29261673041509419626348), (Int.ofNat 596341134351395372082), (Int.negOfNat 91283001489196164227), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-348722329765758485317445476685451209/562949953421312000000000000000000000), (-6230882119461892458982584240152923/281474976710656000000000000000000000), (-1580553241962339102933446039372369/140737488355328000000000000000000000), (2047538663042369284336927385920509/281474976710656000000000000000000000), (-210343355428887651404046734244539/562949953421312000000000000000000000), (-321454252678592667958169700373/1407374883553280000000000000000000), (10893595097360866160289491588557/562949953421312000000000000000000000), (818906318742871402184048236641/281474976710656000000000000000000000), (-20272453237707985838896227909/70368744177664000000000000000000000), (-1522210621678110588505244447/70368744177664000000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial144.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial144.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial144.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 372793655534380212208969259071301209), (Int.negOfNat 2988665344233273552896592412505872), (Int.ofNat 6298454503692858873618706506377883), (Int.negOfNat 404572993357722304480485000592686), (Int.negOfNat 595078094967469812119881406698126), (Int.ofNat 54342500301457560910093724647045), (Int.ofNat 12423201512112245256599936545006), (Int.negOfNat 1298587931621553716243803787048), (Int.negOfNat 121062467229651260684130523306), (Int.ofNat 14504074504807201984159515542), (Int.ofNat 711972213021391445062351029), (Int.negOfNat 99009320467823645861874215), (Int.negOfNat 2836485250913033978994809), (Int.ofNat 466902166982689368744785), (Int.ofNat 8127175219977668921756), (Int.negOfNat 1650365033837276350049), (Int.negOfNat 11234319559307835411), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-372793655534380212208969259071301209/562949953421312000000000000000000000), (-186791584014579597056037025781617/35184372088832000000000000000000000), (6298454503692858873618706506377883/562949953421312000000000000000000000), (-202286496678861152240242500296343/281474976710656000000000000000000000), (-297539047483734906059940703349063/281474976710656000000000000000000000), (10868500060291512182018744929409/112589990684262400000000000000000000), (6211600756056122628299968272503/281474976710656000000000000000000000), (-162323491452694214530475473381/70368744177664000000000000000000000), (-60531233614825630342065261653/281474976710656000000000000000000000), (7252037252403600992079757771/281474976710656000000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial144.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial144.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial144.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 363990223354502344670936499513723203), (Int.ofNat 4370600189547198683384534045802730), (Int.negOfNat 4099351290771524409169930624615954), (Int.negOfNat 1863390809354710337093739436419673), (Int.ofNat 258226814296566973688653020968103), (Int.ofNat 72027157653572692439523219505675), (Int.negOfNat 8703953034636220130355485298213), (Int.negOfNat 1006012267896552180373004804934), (Int.ofNat 134456414497261873574012400265), (Int.ofNat 7311721641041259929121736052), (Int.negOfNat 1171127627761694088170447965), (Int.negOfNat 32314129050381450808069539), (Int.ofNat 6671540468201440590606224), (Int.ofNat 91528833108469813053622), (Int.negOfNat 27145921353789227897999), (Int.negOfNat 158601500038629443217), (Int.ofNat 91368466781030696546), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-363990223354502344670936499513723203/562949953421312000000000000000000000), (437060018954719868338453404580273/56294995342131200000000000000000000), (-2049675645385762204584965312307977/281474976710656000000000000000000000), (-1863390809354710337093739436419673/562949953421312000000000000000000000), (258226814296566973688653020968103/562949953421312000000000000000000000), (2881086306142907697580928780227/22517998136852480000000000000000000), (-8703953034636220130355485298213/562949953421312000000000000000000000), (-503006133948276090186502402467/281474976710656000000000000000000000), (26891282899452374714802480053/112589990684262400000000000000000000), (1827930410260314982280434013/140737488355328000000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial144.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial144.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial144.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 380765952442362238120606758330567944), (Int.negOfNat 22335581352656017819307121912297935), (Int.negOfNat 5824376587431362142861895941128676), (Int.ofNat 1389169041654512918989365327484592), (Int.ofNat 338396198126622503822420356546894), (Int.negOfNat 51668918729910996217570163140280), (Int.negOfNat 6834214558982337760633581030229), (Int.ofNat 1070707677070807037086360138322), (Int.ofNat 64138684818293473397968804377), (Int.negOfNat 12102492260583767050709247390), (Int.negOfNat 320410094716328219420026040), (Int.ofNat 84825958719532621304159008), (Int.ofNat 820439211050459562627415), (Int.negOfNat 408202218176797778521923), (Int.negOfNat 77748637042123523049), (Int.ofNat 1461634416830744084199), (Int.negOfNat 14634281888779912089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-47595744055295279765075844791320993/70368744177664000000000000000000000), (-4467116270531203563861424382459587/112589990684262400000000000000000000), (-1456094146857840535715473985282169/140737488355328000000000000000000000), (86823065103407057436835332967787/35184372088832000000000000000000000), (169198099063311251911210178273447/281474976710656000000000000000000000), (-1291722968247774905439254078507/14073748835532800000000000000000000), (-6834214558982337760633581030229/562949953421312000000000000000000000), (535353838535403518543180069161/281474976710656000000000000000000000), (64138684818293473397968804377/562949953421312000000000000000000000), (-1210249226058376705070924739/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial144.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial144.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial144.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 434150605831302975419938113628746694), (Int.negOfNat 23063278909027372967371264543264523), (Int.ofNat 5635794193938802293400247688596071), (Int.ofNat 1584214294526709475194383248861759), (Int.negOfNat 266274606013138517694954022968716), (Int.negOfNat 39527380230401093165029888150066), (Int.ofNat 7346133259234271541062512436489), (Int.ofNat 472617932205345538251807203611), (Int.negOfNat 108630958061437136209203487875), (Int.negOfNat 2654838747002076296043324955), (Int.ofNat 952112442519178189720468269), (Int.ofNat 4428413492217607274332333), (Int.negOfNat 5492970499956840132887806), (Int.ofNat 33521015039868720807147), (Int.ofNat 22516766377953602188804), (Int.negOfNat 288782731286860273108), (Int.negOfNat 82831064923502646365), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-217075302915651487709969056814373347/281474976710656000000000000000000000), (-23063278909027372967371264543264523/562949953421312000000000000000000000), (5635794193938802293400247688596071/562949953421312000000000000000000000), (1584214294526709475194383248861759/562949953421312000000000000000000000), (-66568651503284629423738505742179/140737488355328000000000000000000000), (-19763690115200546582514944075033/281474976710656000000000000000000000), (7346133259234271541062512436489/562949953421312000000000000000000000), (472617932205345538251807203611/562949953421312000000000000000000000), (-869047664491497089673627903/4503599627370496000000000000000000), (-530967749400415259208664991/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial144.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial144.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial144.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 450083101396383698029709458257387227), (Int.ofNat 8317121127482606992634503064971499), (Int.ofNat 7472805244474868712775760614043902), (Int.negOfNat 881750914690314159357833332827983), (Int.negOfNat 208496882307160728660408090372535), (Int.ofNat 41591938705162515275819370090793), (Int.ofNat 2975257276803009181698580247489), (Int.negOfNat 836822244395365762710514727611), (Int.negOfNat 17418758687295457552356761875), (Int.ofNat 9342262110858140728290116955), (Int.negOfNat 20601262551235148476893731), (Int.negOfNat 65586941065185696079737333), (Int.ofNat 939154525239974792216194), (Int.ofNat 316514151590832894168853), (Int.negOfNat 6758925971568877037196), (Int.negOfNat 1131088959088683888892), (Int.ofNat 31936993048728098635), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-450083101396383698029709458257387227/562949953421312000000000000000000000), (8317121127482606992634503064971499/562949953421312000000000000000000000), (3736402622237434356387880307021951/281474976710656000000000000000000000), (-881750914690314159357833332827983/562949953421312000000000000000000000), (-41699376461432145732081618074507/112589990684262400000000000000000000), (41591938705162515275819370090793/562949953421312000000000000000000000), (2975257276803009181698580247489/562949953421312000000000000000000000), (-836822244395365762710514727611/562949953421312000000000000000000000), (-27870013899672732083770819/900719925474099200000000000000000), (1868452422171628145658023391/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial144.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial144.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial144.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 412533175428390072429216071343752646), (Int.ofNat 24482021438176233764584121215673741), (Int.ofNat 667307967501906817866095128640241), (Int.negOfNat 862513440658509057381028308490960), (Int.ofNat 166964521604754557432950941260348), (Int.ofNat 16116400357445943152977463941280), (Int.negOfNat 5334709545404863280379963775229), (Int.negOfNat 82338937381649650114087892322), (Int.ofNat 78840303967063402650771683377), (Int.negOfNat 957895797569304862362249610), (Int.negOfNat 686049415250382710610315040), (Int.ofNat 17557466252761017979882992), (Int.ofNat 3936531925354071400075415), (Int.negOfNat 131016078435447941345077), (Int.negOfNat 16055010454688869899049), (Int.ofNat 616614406417277846801), (Int.ofNat 65642307486000502911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-206266587714195036214608035671876323/281474976710656000000000000000000000), (24482021438176233764584121215673741/562949953421312000000000000000000000), (667307967501906817866095128640241/562949953421312000000000000000000000), (-10781418008231363217262853856137/7036874417766400000000000000000000), (41741130401188639358237735315087/140737488355328000000000000000000000), (100727502234037144706109149633/3518437208883200000000000000000000), (-5334709545404863280379963775229/562949953421312000000000000000000000), (-41169468690824825057043946161/281474976710656000000000000000000000), (78840303967063402650771683377/562949953421312000000000000000000000), (-95789579756930486236224961/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial144.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial144.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial144.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 364945770916602975351372025323379753), (Int.ofNat 22447415434460428455987231106216190), (Int.negOfNat 417275478608336904632073440514061), (Int.ofNat 344925897646604375748742770003808), (Int.ofNat 61387510385018267825737478428195), (Int.negOfNat 26098715788274875755913234206175), (Int.negOfNat 153030275386838479436899155213), (Int.ofNat 554834978875987605932135967934), (Int.negOfNat 15384365110485435916046825735), (Int.negOfNat 6162811694012280615378789052), (Int.ofNat 260370904010204441833126035), (Int.ofNat 42657317146784558308405539), (Int.negOfNat 2158655886370501120459776), (Int.negOfNat 202295974450724538996622), (Int.ofNat 11445676838503319578001), (Int.ofNat 680079315371983206217), (Int.negOfNat 40645325489925213454), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-364945770916602975351372025323379753/562949953421312000000000000000000000), (2244741543446042845598723110621619/56294995342131200000000000000000000), (-417275478608336904632073440514061/562949953421312000000000000000000000), (10778934301456386742148211562619/17592186044416000000000000000000000), (12277502077003653565147495685639/112589990684262400000000000000000000), (-1043948631530995030236529368247/22517998136852480000000000000000000), (-153030275386838479436899155213/562949953421312000000000000000000000), (277417489437993802966067983967/281474976710656000000000000000000000), (-3076873022097087183209365147/112589990684262400000000000000000000), (-1540702923503070153844697263/140737488355328000000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial144.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial144.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial144.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 318759118647301931779288338039362114), (Int.ofNat 24984910136644625862173642979717198), (Int.ofNat 1321864978380337494400205765082245), (Int.ofNat 23108381936480270036397865279100), (Int.negOfNat 90539680997064404755722759204853), (Int.ofNat 2443498312819293129838115492682), (Int.ofNat 3093781043363425319421704074506), (Int.negOfNat 174613747591687610961879855952), (Int.negOfNat 45957810873211616170464777306), (Int.ofNat 3199790054082615151601066458), (Int.ofNat 391010086016522289372081029), (Int.negOfNat 30657023025606955605422785), (Int.negOfNat 2168533541864335353187809), (Int.ofNat 186392577977964227809215), (Int.ofNat 8452415132312751307756), (Int.negOfNat 791659901192455864951), (Int.negOfNat 39773706037912755411), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-159379559323650965889644169019681057/281474976710656000000000000000000000), (12492455068322312931086821489858599/281474976710656000000000000000000000), (264372995676067498880041153016449/112589990684262400000000000000000000), (231083819364802700363978652791/5629499534213120000000000000000000), (-90539680997064404755722759204853/562949953421312000000000000000000000), (1221749156409646564919057746341/281474976710656000000000000000000000), (1546890521681712659710852037253/281474976710656000000000000000000000), (-10913359224480475685117490997/35184372088832000000000000000000000), (-22978905436605808085232388653/281474976710656000000000000000000000), (1599895027041307575800533229/281474976710656000000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial144.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial144.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial144.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 264521559469656639604495589796731797), (Int.ofNat 28325585277405669133394804730911668), (Int.ofNat 44124837535058544317828549320177), (Int.negOfNat 266876134251979547363850275464564), (Int.ofNat 35819137522130987725432432602369), (Int.ofNat 12857317099172243588168819855200), (Int.negOfNat 1570205567539027478859725781670), (Int.negOfNat 267826840535822802070646781282), (Int.ofNat 32984018167036835358195254728), (Int.ofNat 2861060264975790172882558576), (Int.negOfNat 375860265313049713062234059), (Int.negOfNat 18520347973177942950346837), (Int.ofNat 2682029071104988927864772), (Int.ofNat 80023389038177237037454), (Int.negOfNat 13110412746274405137652), (Int.negOfNat 221040766151040555082), (Int.ofNat 40730790781759745773), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-264521559469656639604495589796731797/562949953421312000000000000000000000), (7081396319351417283348701182727917/140737488355328000000000000000000000), (44124837535058544317828549320177/562949953421312000000000000000000000), (-66719033562994886840962568866141/140737488355328000000000000000000000), (35819137522130987725432432602369/562949953421312000000000000000000000), (16071646373965304485211024819/703687441776640000000000000000000), (-157020556753902747885972578167/56294995342131200000000000000000000), (-133913420267911401035323390641/281474976710656000000000000000000000), (4123002270879604419774406841/70368744177664000000000000000000000), (178816266560986885805159911/35184372088832000000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial144.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial144.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial144.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 208969635901788433961052472441575214), (Int.ofNat 27091206019945040217535232271563854), (Int.negOfNat 158087570675005569225854110859862), (Int.ofNat 201002119520105845491737418036120), (Int.ofNat 38187827126399199874281906017106), (Int.negOfNat 11231977744751737875793203922075), (Int.negOfNat 1073810353970514175642497593436), (Int.ofNat 284151561510510697176527144577), (Int.ofNat 14344094820505165022004841772), (Int.negOfNat 3946932643664219602402642203), (Int.negOfNat 102298398442929124063551798), (Int.ofNat 33670626280574783688478493), (Int.ofNat 415748100105407617087440), (Int.negOfNat 193107887294812029506500), (Int.negOfNat 896389947924157778505), (Int.ofNat 810838995134110579647), (Int.ofNat 13905104589825007911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-104484817950894216980526236220787607/281474976710656000000000000000000000), (13545603009972520108767616135781927/281474976710656000000000000000000000), (-79043785337502784612927055429931/281474976710656000000000000000000000), (5025052988002646137293435450903/14073748835532800000000000000000000), (19093913563199599937140953008553/281474976710656000000000000000000000), (-449279109790069515031728156883/22517998136852480000000000000000000), (-268452588492628543910624398359/140737488355328000000000000000000000), (284151561510510697176527144577/562949953421312000000000000000000000), (3586023705126291255501210443/140737488355328000000000000000000000), (-3946932643664219602402642203/562949953421312000000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial144.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial144.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial144.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 153590712109295805268791798872445186), (Int.ofNat 29120911881216867793344266678604837), (Int.ofNat 1006394589795417297394531322299925), (Int.ofNat 48868792580704241310026799374274), (Int.negOfNat 58816133435390833218314817054783), (Int.negOfNat 1629165616092460532891886130940), (Int.ofNat 1996060727962280137239639174353), (Int.ofNat 15085567104871848512718242669), (Int.negOfNat 34870131101912570738359199931), (Int.ofNat 121736010314893877483809381), (Int.ofNat 363074848558833942188534152), (Int.negOfNat 3593709122301402872923205), (Int.negOfNat 2474904090892154440050375), (Int.ofNat 33411230941304128749027), (Int.ofNat 11828501925091749479248), (Int.negOfNat 204787852090901821513), (Int.negOfNat 40816256073594278092), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-76795356054647902634395899436222593/281474976710656000000000000000000000), (29120911881216867793344266678604837/562949953421312000000000000000000000), (40255783591816691895781252891997/22517998136852480000000000000000000), (24434396290352120655013399687137/281474976710656000000000000000000000), (-58816133435390833218314817054783/562949953421312000000000000000000000), (-81458280804623026644594306547/28147497671065600000000000000000000), (1996060727962280137239639174353/562949953421312000000000000000000000), (15085567104871848512718242669/562949953421312000000000000000000000), (-34870131101912570738359199931/562949953421312000000000000000000000), (121736010314893877483809381/562949953421312000000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial144.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial144.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial144.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 91804381916541540223298621897510248), (Int.ofNat 32076802404088005146931686469531030), (Int.ofNat 188876331804985783832252905184034), (Int.negOfNat 215677734052727177450028510318785), (Int.ofNat 14753984324841314675578261905562), (Int.ofNat 10807272131729038668520978620734), (Int.negOfNat 580284158775824399537548063737), (Int.negOfNat 250106427777655282311603600237), (Int.ofNat 11706786772851995847093578592), (Int.ofNat 3264764248101615134675747576), (Int.negOfNat 139405176407694865334102677), (Int.negOfNat 26974138764082665445709722), (Int.ofNat 1071338603782508373270711), (Int.ofNat 152512715033125912123031), (Int.negOfNat 5621270817652473813655), (Int.negOfNat 635113784526979844705), (Int.ofNat 11991985288874250362), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-11475547739567692527912327737188781/70368744177664000000000000000000000), (3207680240408800514693168646953103/56294995342131200000000000000000000), (94438165902492891916126452592017/281474976710656000000000000000000000), (-43135546810545435490005702063757/112589990684262400000000000000000000), (7376992162420657337789130952781/281474976710656000000000000000000000), (5403636065864519334260489310367/281474976710656000000000000000000000), (-580284158775824399537548063737/562949953421312000000000000000000000), (-250106427777655282311603600237/562949953421312000000000000000000000), (365837086651624870221674331/17592186044416000000000000000000000), (408095531012701891834468447/70368744177664000000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial144.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial144.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial144.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 28103472977001426507922637525115306), (Int.ofNat 31375947784835500153395030288482952), (Int.negOfNat 160101182248778826596907345271013), (Int.ofNat 137149294096729816401642671283071), (Int.ofNat 41426199852624536600165515882073), (Int.negOfNat 7109065774540720913280934678493), (Int.negOfNat 1352777253978384015468241117263), (Int.ofNat 171611894624930385816157394763), (Int.ofNat 23025503440474149970673188408), (Int.negOfNat 2349358773650180476308776424), (Int.negOfNat 236930174590795019957504323), (Int.ofNat 20398518126548322510613278), (Int.ofNat 1616352895039255365187289), (Int.negOfNat 120994918034817038071969), (Int.negOfNat 7804915707825551839345), (Int.ofNat 542341810751046568295), (Int.ofNat 23627498636092134638), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-14051736488500713253961318762557653/281474976710656000000000000000000000), (3921993473104437519174378786060369/70368744177664000000000000000000000), (-160101182248778826596907345271013/562949953421312000000000000000000000), (137149294096729816401642671283071/562949953421312000000000000000000000), (41426199852624536600165515882073/562949953421312000000000000000000000), (-7109065774540720913280934678493/562949953421312000000000000000000000), (-1352777253978384015468241117263/562949953421312000000000000000000000), (171611894624930385816157394763/562949953421312000000000000000000000), (2878187930059268746334148551/70368744177664000000000000000000000), (-293669846706272559538597053/70368744177664000000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial144.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial144.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial144.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 35480426224510536880800671044001807), (Int.ofNat 32972611019980340023686722543884327), (Int.ofNat 907323111248269913291527207267591), (Int.ofNat 89850393368092695200735075937133), (Int.negOfNat 48632355548646087590091626351806), (Int.negOfNat 4537530507273588847894806650440), (Int.ofNat 1619892030698979976058590170647), (Int.ofNat 107197442907169603976117771669), (Int.negOfNat 28168257736115460527445029069), (Int.negOfNat 1444032305474442465254644619), (Int.ofNat 296151716322290794990353848), (Int.ofNat 12403107396034291590158795), (Int.negOfNat 2061673006536784350244625), (Int.negOfNat 73100646907161388974973), (Int.ofNat 10117061308068990618752), (Int.ofNat 337614803655214985487), (Int.negOfNat 29294696448822436908), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(35480426224510536880800671044001807/562949953421312000000000000000000000), (32972611019980340023686722543884327/562949953421312000000000000000000000), (907323111248269913291527207267591/562949953421312000000000000000000000), (89850393368092695200735075937133/562949953421312000000000000000000000), (-24316177774323043795045813175903/281474976710656000000000000000000000), (-113438262681839721197370166261/14073748835532800000000000000000000), (1619892030698979976058590170647/562949953421312000000000000000000000), (107197442907169603976117771669/562949953421312000000000000000000000), (-28168257736115460527445029069/562949953421312000000000000000000000), (-1444032305474442465254644619/562949953421312000000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial144.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial144.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial144.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 104960188926026134340551125888758557), (Int.ofNat 36089345404996890939020071702044509), (Int.ofNat 323539531998878904731558195847307), (Int.negOfNat 214909912852213825502742641016598), (Int.ofNat 57475908019104178157485483713), (Int.ofNat 10908002840080525146536464308152), (Int.ofNat 44140407312278972275223514436), (Int.negOfNat 257190538878707637883579541423), (Int.negOfNat 1747571568209759492120570772), (Int.ofNat 3433732949507795661161032797), (Int.ofNat 29437739713808256330250798), (Int.negOfNat 29085253829896329071932507), (Int.negOfNat 281294513956159368698440), (Int.ofNat 168532392871673704773500), (Int.ofNat 1712314421480191543505), (Int.negOfNat 709203825603717474353), (Int.ofNat 2212614381384102089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(104960188926026134340551125888758557/562949953421312000000000000000000000), (36089345404996890939020071702044509/562949953421312000000000000000000000), (323539531998878904731558195847307/562949953421312000000000000000000000), (-107454956426106912751371320508299/281474976710656000000000000000000000), (57475908019104178157485483713/562949953421312000000000000000000000), (1363500355010065643317058038519/70368744177664000000000000000000000), (11035101828069743068805878609/140737488355328000000000000000000000), (-257190538878707637883579541423/562949953421312000000000000000000000), (-436892892052439873030142693/140737488355328000000000000000000000), (3433732949507795661161032797/562949953421312000000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial144.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial144.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial144.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 177034920367666065406733515226962121), (Int.ofNat 35578264628008798039172210017571797), (Int.negOfNat 241919623229995725784646718033371), (Int.ofNat 99475107300575076683720518702528), (Int.ofNat 50853025290669158131754514336447), (Int.negOfNat 4622831697332303158945829102800), (Int.negOfNat 1755974458405490371271602703057), (Int.ofNat 94972988325920745112050974718), (Int.ofNat 31433082688124086324457333272), (Int.negOfNat 1055598965930661460917975424), (Int.negOfNat 337471708369656440102049941), (Int.ofNat 7087936019504302764305163), (Int.ofNat 2379446159883618700374228), (Int.negOfNat 30901979948447334869546), (Int.negOfNat 11722824650761714775348), (Int.ofNat 82309327746595562918), (Int.ofNat 29380161740656969227), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(177034920367666065406733515226962121/562949953421312000000000000000000000), (35578264628008798039172210017571797/562949953421312000000000000000000000), (-241919623229995725784646718033371/562949953421312000000000000000000000), (1554298551571485573183133104727/8796093022208000000000000000000000), (50853025290669158131754514336447/562949953421312000000000000000000000), (-11557079243330757897364572757/1407374883553280000000000000000000), (-1755974458405490371271602703057/562949953421312000000000000000000000), (47486494162960372556025487359/281474976710656000000000000000000000), (3929135336015510790557166659/70368744177664000000000000000000000), (-8246866921333292663421683/4398046511104000000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial144.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial144.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial144.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 248592248611143629906560902119931304), (Int.ofNat 36795321391386956007023318353419546), (Int.ofNat 895892544096501127453808966025479), (Int.ofNat 139634606319979438264669388388272), (Int.negOfNat 47149916657024874455963820299374), (Int.negOfNat 8054993744260190710154047423772), (Int.ofNat 1481146478153706601178533567994), (Int.ofNat 211491784345207207614071554048), (Int.negOfNat 23431794014749464001939296694), (Int.negOfNat 3075854434422878233557524542), (Int.ofNat 216755410090790401463759971), (Int.ofNat 27703416788254166571132215), (Int.negOfNat 1293451876718634354483191), (Int.negOfNat 167013261501719391190785), (Int.ofNat 5343525899780922719244), (Int.ofNat 726055459030670530049), (Int.negOfNat 28081215829471849589), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(31074031076392953738320112764991413/70368744177664000000000000000000000), (18397660695693478003511659176709773/281474976710656000000000000000000000), (895892544096501127453808966025479/562949953421312000000000000000000000), (8727162894998714891541836774267/35184372088832000000000000000000000), (-23574958328512437227981910149687/281474976710656000000000000000000000), (-2013748436065047677538511855943/140737488355328000000000000000000000), (740573239076853300589266783997/281474976710656000000000000000000000), (12908434103101025855351047/34359738368000000000000000000000), (-11715897007374732000969648347/281474976710656000000000000000000000), (-1537927217211439116778762271/281474976710656000000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial144.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial144.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial144.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 325985943038572894902527305104845153), (Int.ofNat 40250739465261822039721258024814350), (Int.ofNat 402302627562887493801676441507120), (Int.negOfNat 258561036256885066217655777045462), (Int.negOfNat 14393159212130684349744572734784), (Int.ofNat 13174092625715056280625806710052), (Int.ofNat 781148696050438479073532259213), (Int.negOfNat 299711358780385359963809882066), (Int.negOfNat 18796508327265717806787459265), (Int.ofNat 3702460805834170630721303948), (Int.ofNat 243793281009704290791158965), (Int.negOfNat 28055602543818600900473461), (Int.negOfNat 1930307259883308263431224), (Int.ofNat 142519007219615776772378), (Int.ofNat 10238675987263550831999), (Int.negOfNat 503514996766856166783), (Int.negOfNat 29465627032491501546), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(325985943038572894902527305104845153/562949953421312000000000000000000000), (805014789305236440794425160496287/11258999068426240000000000000000000), (5028782844536093672520955518839/7036874417766400000000000000000000), (-129280518128442533108827888522731/281474976710656000000000000000000000), (-224893112689541942964758948981/8796093022208000000000000000000000), (3293523156428764070156451677513/140737488355328000000000000000000000), (781148696050438479073532259213/562949953421312000000000000000000000), (-149855679390192679981904941033/281474976710656000000000000000000000), (-3759301665453143561357491853/112589990684262400000000000000000000), (925615201458542657680325987/140737488355328000000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial144.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial144.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial144.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 406228324417446346424668684427050742), (Int.ofNat 39356449937896145920902142949879629), (Int.negOfNat 469210703847616140664985972561680), (Int.ofNat 99014292190856938385868359918776), (Int.ofNat 76081565171606410095043064919060), (Int.negOfNat 2588327248930024365483452214493), (Int.negOfNat 2704203959828824751219812101771), (Int.negOfNat 11229274706356257553018006322), (Int.ofNat 46705997323523576906407302623), (Int.ofNat 1080937008100175847549558390), (Int.negOfNat 458694380985521973347906960), (Int.negOfNat 15455714315418956778160008), (Int.ofNat 2859749284793279944011585), (Int.ofNat 114253713287652775304923), (Int.negOfNat 12369654947385671940951), (Int.negOfNat 553858807316643589199), (Int.ofNat 53949817277559597089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(203114162208723173212334342213525371/281474976710656000000000000000000000), (39356449937896145920902142949879629/562949953421312000000000000000000000), (-5865133798095201758312324657021/7036874417766400000000000000000000), (12376786523857117298233544989847/70368744177664000000000000000000000), (3804078258580320504752153245953/28147497671065600000000000000000000), (-2588327248930024365483452214493/562949953421312000000000000000000000), (-2704203959828824751219812101771/562949953421312000000000000000000000), (-5614637353178128776509003161/281474976710656000000000000000000000), (46705997323523576906407302623/562949953421312000000000000000000000), (108093700810017584754955839/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial144.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial144.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial144.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 484828489235690144104440773453898661), (Int.ofNat 40418954303792971119491966882973774), (Int.ofNat 1170376648986644352688573804096260), (Int.ofNat 247328104316968095081617176307238), (Int.negOfNat 64956459198788839846494712328103), (Int.negOfNat 16720897772027671415821431957434), (Int.ofNat 1510001077395920649229515246011), (Int.ofNat 448722661856635307074606720389), (Int.negOfNat 12127129462349709667602397125), (Int.negOfNat 6053343085093490572416883045), (Int.negOfNat 9172925657727358971906269), (Int.ofNat 47443383133662632013274667), (Int.ofNat 726783621863956934804806), (Int.negOfNat 245542200898407389382147), (Int.negOfNat 5630034539940588235804), (Int.ofNat 917831297507335233108), (Int.ofNat 20928225174963451365), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(484828489235690144104440773453898661/562949953421312000000000000000000000), (20209477151896485559745983441486887/281474976710656000000000000000000000), (58518832449332217634428690204813/28147497671065600000000000000000000), (123664052158484047540808588153619/281474976710656000000000000000000000), (-64956459198788839846494712328103/562949953421312000000000000000000000), (-8360448886013835707910715978717/281474976710656000000000000000000000), (1510001077395920649229515246011/562949953421312000000000000000000000), (448722661856635307074606720389/562949953421312000000000000000000000), (-97017035698797677340819177/4503599627370496000000000000000000), (-1210668617018698114483376609/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial144.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial144.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial144.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 570900118585753280987671741557809260), (Int.ofNat 45117194322397340994782156692158525), (Int.ofNat 373273647220152556072405419776267), (Int.negOfNat 500678554394729673408916644420020), (Int.negOfNat 52032644210569972426376344046646), (Int.ofNat 22774132680786957900383588980207), (Int.ofNat 3023812336337414969485974922511), (Int.negOfNat 384718784147550507859473918389), (Int.negOfNat 64749666943830848886581953125), (Int.ofNat 2622654698413410156068185045), (Int.ofNat 668248455855095248891101731), (Int.negOfNat 6881895955329247082365667), (Int.negOfNat 4213069110643277013228194), (Int.negOfNat 15905161198708421288853), (Int.ofNat 18273218005858074739196), (Int.ofNat 223313349574583393892), (Int.negOfNat 71252528437507783635), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(28545005929287664049383587077890463/28147497671065600000000000000000000), (1804687772895893639791286267686341/22517998136852480000000000000000000), (373273647220152556072405419776267/562949953421312000000000000000000000), (-25033927719736483670445832221001/28147497671065600000000000000000000), (-26016322105284986213188172023323/281474976710656000000000000000000000), (22774132680786957900383588980207/562949953421312000000000000000000000), (3023812336337414969485974922511/562949953421312000000000000000000000), (-384718784147550507859473918389/562949953421312000000000000000000000), (-828795736881034865748249/7205759403792793600000000000000), (524530939682682031213637009/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial144.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial144.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial144.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 658648123300674104007979174378846848), (Int.ofNat 41110230797762426071370453372988453), (Int.negOfNat 1687188753687080506216901299743658), (Int.ofNat 169969207604645602936379843673828), (Int.ofNat 195640870792358508869267014126198), (Int.ofNat 7794745111175172750541322674947), (Int.negOfNat 5946720545286548954339903597771), (Int.negOfNat 538348400988067084564535770678), (Int.ofNat 63132358347569030547084414623), (Int.ofNat 8029510904582113921400295610), (Int.negOfNat 349007344261009343096231960), (Int.negOfNat 63389820266825109893518992), (Int.ofNat 1082621177760843349725585), (Int.ofNat 326814167061316930433077), (Int.negOfNat 1325653886721493366951), (Int.negOfNat 1245662972637752806801), (Int.negOfNat 3739467737461307911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(5145688463286516437562337299834741/4398046511104000000000000000000000), (41110230797762426071370453372988453/562949953421312000000000000000000000), (-843594376843540253108450649871829/281474976710656000000000000000000000), (42492301901161400734094960918457/140737488355328000000000000000000000), (97820435396179254434633507063099/281474976710656000000000000000000000), (7794745111175172750541322674947/562949953421312000000000000000000000), (-5946720545286548954339903597771/562949953421312000000000000000000000), (-269174200494033542282267885339/281474976710656000000000000000000000), (63132358347569030547084414623/562949953421312000000000000000000000), (802951090458211392140029561/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial144.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial144.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial144.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 738429563444787582569067973377904303), (Int.ofNat 41982933458739238196964855240029890), (Int.ofNat 3007055309116385412060180672636395), (Int.ofNat 942411457271620497454777744756057), (Int.negOfNat 137985437007301237892424213429287), (Int.negOfNat 68792764896733905374324405979825), (Int.negOfNat 2995082575516557369735778335787), (Int.ofNat 1019039067233940216516804015066), (Int.ofNat 81965179422715773936274019735), (Int.negOfNat 7713988574996624623985985948), (Int.negOfNat 842227248706567525619367035), (Int.ofNat 36197475748875021348151461), (Int.ofNat 5216038491244501877854776), (Int.negOfNat 113070349617894988307378), (Int.negOfNat 22445718570887097657001), (Int.ofNat 227696294142117288783), (Int.ofNat 79960860878704898454), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(738429563444787582569067973377904303/562949953421312000000000000000000000), (4198293345873923819696485524002989/56294995342131200000000000000000000), (601411061823277082412036134527279/112589990684262400000000000000000000), (942411457271620497454777744756057/562949953421312000000000000000000000), (-137985437007301237892424213429287/562949953421312000000000000000000000), (-2751710595869356214972976239193/22517998136852480000000000000000000), (-2995082575516557369735778335787/562949953421312000000000000000000000), (509519533616970108258402007533/281474976710656000000000000000000000), (16393035884543154787254803947/112589990684262400000000000000000000), (-1928497143749156155996496487/140737488355328000000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial144.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial144.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial144.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 837508824802662756980046406745445246), (Int.ofNat 55344985182835098149003613623350976), (Int.negOfNat 84594351558749719431741459190107), (Int.negOfNat 2727191945568791255376225382590014), (Int.negOfNat 668781691546636043419677883362647), (Int.negOfNat 3217031702832339819350911879909), (Int.ofNat 13240568200373451904657453873267), (Int.ofNat 712965875337979505179793872952), (Int.negOfNat 127944596281873196074907602694), (Int.negOfNat 9970855529822056007145805458), (Int.ofNat 770037085700638734522042971), (Int.ofNat 75061445535176716927840785), (Int.negOfNat 3194121585719414150884191), (Int.negOfNat 376544643963059670690215), (Int.ofNat 9643858882477960791244), (Int.ofNat 1387640536827920174951), (Int.negOfNat 22129133710626439589), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(418754412401331378490023203372722623/281474976710656000000000000000000000), (864765393481798408578181462864859/8796093022208000000000000000000000), (-84594351558749719431741459190107/562949953421312000000000000000000000), (-1363595972784395627688112691295007/281474976710656000000000000000000000), (-668781691546636043419677883362647/562949953421312000000000000000000000), (-3217031702832339819350911879909/562949953421312000000000000000000000), (13240568200373451904657453873267/562949953421312000000000000000000000), (89120734417247438147474234119/70368744177664000000000000000000000), (-63972298140936598037453801347/281474976710656000000000000000000000), (-4985427764911028003572902729/281474976710656000000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial144.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial144.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial144.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 916141153498547567425315944809258885), (Int.ofNat 3334228419818939595218067086412783), (Int.negOfNat 29363528871368246094592830475775057), (Int.negOfNat 5956717036371630442648224334041890), (Int.ofNat 122602913121828529233361489506723), (Int.ofNat 146133484511707083240274613607800), (Int.ofNat 5628009390017337931637094373670), (Int.negOfNat 1750381749500955354577087280718), (Int.negOfNat 107662722543484512019930989728), (Int.ofNat 13019783543559975718244185424), (Int.ofNat 983599466160575518391688059), (Int.negOfNat 66701627774979997797316163), (Int.negOfNat 5766357271211584091461772), (Int.ofNat 250485922903965707498546), (Int.ofNat 24081479428729239496652), (Int.negOfNat 703268808655565264918), (Int.negOfNat 80046326170539430773), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(183228230699709513485063188961851777/112589990684262400000000000000000000), (3334228419818939595218067086412783/562949953421312000000000000000000000), (-29363528871368246094592830475775057/562949953421312000000000000000000000), (-595671703637163044264822433404189/56294995342131200000000000000000000), (122602913121828529233361489506723/562949953421312000000000000000000000), (730667422558535416201373068039/2814749767106560000000000000000000), (562800939001733793163709437367/56294995342131200000000000000000000), (-875190874750477677288543640359/281474976710656000000000000000000000), (-3364460079483891000622843429/17592186044416000000000000000000000), (813736471472498482390261589/35184372088832000000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial144.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial144.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial144.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 764455774285464353301854187568526929), (Int.negOfNat 169766202915187146316057932304322390), (Int.negOfNat 50420041866422698397043052813437224), (Int.ofNat 678506863442404246819971735166794), (Int.ofNat 1373210185163315805178149912678621), (Int.ofNat 50131834102814645243265272780302), (Int.negOfNat 20137363999470179940245635144564), (Int.negOfNat 1115703775587678574280786357577), (Int.ofNat 184156259101939906498183972228), (Int.ofNat 11950122356993757692649392203), (Int.negOfNat 1149344335356504347293279202), (Int.negOfNat 81155935827337319949940493), (Int.ofNat 5199474347800619202667560), (Int.ofNat 387439282266869699530500), (Int.negOfNat 17798419160503571455495), (Int.negOfNat 1390285665477069564647), (Int.ofNat 47997735158714187089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(764455774285464353301854187568526929/562949953421312000000000000000000000), (-16976620291518714631605793230432239/56294995342131200000000000000000000), (-6302505233302837299630381601679653/70368744177664000000000000000000000), (339253431721202123409985867583397/281474976710656000000000000000000000), (1373210185163315805178149912678621/562949953421312000000000000000000000), (25065917051407322621632636390151/281474976710656000000000000000000000), (-5034340999867544985061408786141/140737488355328000000000000000000000), (-1115703775587678574280786357577/562949953421312000000000000000000000), (46039064775484976624545993057/140737488355328000000000000000000000), (11950122356993757692649392203/562949953421312000000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial144.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial144.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial144.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 250867179638124816356673054319935512), (Int.negOfNat 319507768177968748434310588163890592), (Int.negOfNat 14594175852590088563709293204274683), (Int.ofNat 10196542816392389423174616735641542), (Int.ofNat 590231336370353763931562376785464), (Int.negOfNat 189677367723537279457614751966287), (Int.negOfNat 11787016493956390333232619932353), (Int.ofNat 2184313645015757387207425405331), (Int.ofNat 138025187469294962987643792931), (Int.negOfNat 16800644230099490305410595381), (Int.negOfNat 1061114819981503465125291152), (Int.ofNat 91638056153045500146044205), (Int.ofNat 5744578231775408567276375), (Int.negOfNat 371656259767095353227027), (Int.negOfNat 23045769774129629740248), (Int.ofNat 1145631392190012966513), (Int.ofNat 80131791462373963092), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(31358397454765602044584131789991939/70368744177664000000000000000000000), (-9984617755561523388572205880121581/17592186044416000000000000000000000), (-14594175852590088563709293204274683/562949953421312000000000000000000000), (5098271408196194711587308367820771/281474976710656000000000000000000000), (73778917046294220491445297098183/70368744177664000000000000000000000), (-189677367723537279457614751966287/562949953421312000000000000000000000), (-11787016493956390333232619932353/562949953421312000000000000000000000), (2184313645015757387207425405331/562949953421312000000000000000000000), (138025187469294962987643792931/562949953421312000000000000000000000), (-16800644230099490305410595381/562949953421312000000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial144.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial144.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial144.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 362027615129534595243499974104163452), (Int.negOfNat 252998931620340250956349662789996819), (Int.ofNat 44376020180305865494851795341637319), (Int.ofNat 6813708259221684390003698814433463), (Int.negOfNat 1325126076262670117897069443390016), (Int.negOfNat 125080871767857513719276929526234), (Int.ofNat 20995448333533212676841383707964), (Int.ofNat 1535525975270670081042027291237), (Int.negOfNat 207510005862775051817105258592), (Int.negOfNat 13024009460221439498850344576), (Int.ofNat 1391745464163066646006795677), (Int.ofNat 78976375979932864116857722), (Int.negOfNat 6729122583304948858562711), (Int.negOfNat 354438767025932097748031), (Int.ofNat 24535001038102930060655), (Int.ofNat 1198026489577433504705), (Int.negOfNat 73894825037413445362), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-90506903782383648810874993526040863/140737488355328000000000000000000000), (-252998931620340250956349662789996819/562949953421312000000000000000000000), (44376020180305865494851795341637319/562949953421312000000000000000000000), (6813708259221684390003698814433463/562949953421312000000000000000000000), (-20705094941604220592141710052969/8796093022208000000000000000000000), (-62540435883928756859638464763117/281474976710656000000000000000000000), (5248862083383303169210345926991/140737488355328000000000000000000000), (1535525975270670081042027291237/562949953421312000000000000000000000), (-6484687683211720369284539331/17592186044416000000000000000000000), (-101750073907979996084768317/4398046511104000000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial144.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial144.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial144.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial144.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial144.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial144.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial144.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial144.reflect := by
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

end Bin144
end
end ErdosOverlap.OuterNumerics
