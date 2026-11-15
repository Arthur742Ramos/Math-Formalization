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

/-! # Exact integer weighted outer models for source bin 155

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin155

def weightDenominator : ℤ := (Int.ofNat 1000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 160025055411857080)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 110292368595176810)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 62010517156863120)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 94625246886442930)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 72074738860639400)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 50209733699131974)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 35750491341991646)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 21901184562726930)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 9538375748875385)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial155.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial155.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 929877398456134500)⟩, ⟨(314159265359/50000000000), (Int.ofNat 353178366978619540)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 127217015526930540)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 106147707487629870)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 60817565485848890)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 25627969972289832)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 7257646165658454)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 2019174453202457)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 2267482160928351)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial155.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial155.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 929877398456134500)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 353178366978619540)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 127217015526930540)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 106147707487629870)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 60817565485848890)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 25627969972289832)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 7257646165658454)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 2019174453202457)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 2267482160928351)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial155.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial155.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial155.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 311595594142094995318649672928871), (Int.ofNat 425865610924309713186542801326161), (Int.ofNat 33346286638986642274593187592554), (Int.negOfNat 11219723784870394194097041556059), (Int.negOfNat 953129698280425423407881000803), (Int.ofNat 204913917675833877240475150614), (Int.ofNat 15064551300676442397319734045), (Int.negOfNat 2437272383837865349880215537), (Int.negOfNat 148688897192852789136111027), (Int.ofNat 19796463856121052814250206), (Int.ofNat 997312473457796176921036), (Int.negOfNat 115271594551903454023783), (Int.negOfNat 4839188535639650937173), (Int.ofNat 500819141291459477182), (Int.ofNat 17840862963811260555), (Int.negOfNat 1653469080832120267), (Int.negOfNat 53968995888331292), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-311595594142094995318649672928871/1125899906842624000000000000000000), (425865610924309713186542801326161/1125899906842624000000000000000000), (16673143319493321137296593796277/562949953421312000000000000000000), (-11219723784870394194097041556059/1125899906842624000000000000000000), (-953129698280425423407881000803/1125899906842624000000000000000000), (102456958837916938620237575307/562949953421312000000000000000000), (3012910260135288479463946809/225179981368524800000000000000000), (-2437272383837865349880215537/1125899906842624000000000000000000), (-148688897192852789136111027/1125899906842624000000000000000000), (9898231928060526407125103/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial155.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial155.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial155.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial155 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 575695155713262752942510797042371), (Int.ofNat 412204601740806025321111854773694), (Int.negOfNat 38643637492347488259139636311696), (Int.negOfNat 9752712517847283635723967515403), (Int.ofNat 1238852249616053690302628805933), (Int.ofNat 158575843704165669230855582383), (Int.negOfNat 20927488481284040884773870275), (Int.negOfNat 1679614753266203343954001840), (Int.ofNat 219231858102020945746408794), (Int.ofNat 12152129088613826496057804), (Int.negOfNat 1561040034402642298529960), (Int.negOfNat 63362280911969513731301), (Int.ofNat 8012363536777619431992), (Int.ofNat 248703399421100691282), (Int.negOfNat 31001607768128837057), (Int.negOfNat 749193284641383538), (Int.ofNat 99758917901770486), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(575695155713262752942510797042371/1125899906842624000000000000000000), (206102300870403012660555927386847/562949953421312000000000000000000), (-2415227343271718016196227269481/70368744177664000000000000000000), (-9752712517847283635723967515403/1125899906842624000000000000000000), (1238852249616053690302628805933/1125899906842624000000000000000000), (158575843704165669230855582383/1125899906842624000000000000000000), (-837099539251361635390954811/45035996273704960000000000000000), (-20995184415827541799425023/14073748835532800000000000000000), (109615929051010472873204397/562949953421312000000000000000000), (3038032272153456624014451/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial155.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial155.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial155.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial155 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 1190910473429079602597287272097885), (Int.ofNat 188400288003345501867083566485821), (Int.negOfNat 60463027185990007929347408595634), (Int.ofNat 2644647454501584217866904340340), (Int.ofNat 1370622761798599786881570647659), (Int.negOfNat 124527803210120286149183053622), (Int.negOfNat 17400235186685634051326290592), (Int.ofNat 1960950546159856999297348038), (Int.ofNat 140791094511159498721962211), (Int.negOfNat 18145466001624196653226248), (Int.negOfNat 789720154376849434686913), (Int.ofNat 113331738437835231018170), (Int.ofNat 3246861000028738874864), (Int.negOfNat 512930279865492347600), (Int.negOfNat 10164480557282443316), (Int.ofNat 1759131449974967554), (Int.ofNat 23086386480776786), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(238182094685815920519457454419577/225179981368524800000000000000000), (188400288003345501867083566485821/1125899906842624000000000000000000), (-30231513592995003964673704297817/562949953421312000000000000000000), (132232372725079210893345217017/56294995342131200000000000000000), (1370622761798599786881570647659/1125899906842624000000000000000000), (-62263901605060143074591526811/562949953421312000000000000000000), (-543757349583926064103946581/35184372088832000000000000000000), (980475273079928499648674019/562949953421312000000000000000000), (140791094511159498721962211/1125899906842624000000000000000000), (-2268183250203024581653281/140737488355328000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial155.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial155.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial155.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial155 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 1364124765891579457466586499408392), (Int.ofNat 9818961400816396206859563822854), (Int.negOfNat 24357805702728576620324202868875), (Int.ofNat 7090227972188989422560873845224), (Int.negOfNat 290688219627034746176377316281), (Int.negOfNat 144979736006749564232741973246), (Int.ofNat 12726046658657080417173234566), (Int.ofNat 1465345724708878081627067585), (Int.negOfNat 174275854111137263544934580), (Int.negOfNat 9242612679105980075778903), (Int.ofNat 1394132052034753727639690), (Int.ofNat 39768508039609749133022), (Int.negOfNat 7585401544613799085253), (Int.negOfNat 122168500660964058851), (Int.ofNat 30237414849072854782), (Int.ofNat 245519910949347477), (Int.negOfNat 92956471418985433), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(170515595736447432183323312426049/140737488355328000000000000000000), (4909480700408198103429781911427/562949953421312000000000000000000), (-194862445621828612962593622951/9007199254740992000000000000000), (886278496523623677820109230653/140737488355328000000000000000000), (-290688219627034746176377316281/1125899906842624000000000000000000), (-72489868003374782116370986623/562949953421312000000000000000000), (6363023329328540208586617283/562949953421312000000000000000000), (293069144941775616325413517/225179981368524800000000000000000), (-8713792705556863177246729/56294995342131200000000000000000), (-9242612679105980075778903/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial155.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial155.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial155.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial155 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 1334717088461659441747549940870166), (Int.negOfNat 20522408787650013455151207819992), (Int.ofNat 3309396667813333401137721942797), (Int.ofNat 1482529375885469794103101749462), (Int.negOfNat 779639032110450576461782621558), (Int.ofNat 45753143989641416812528477770), (Int.ofNat 12330985191504957726512535667), (Int.negOfNat 1298114325872724549660609509), (Int.negOfNat 96572905635094126365954444), (Int.ofNat 14534008848896773838635859), (Int.ofNat 451612290230277984701138), (Int.negOfNat 98756682814062092873710), (Int.negOfNat 1285887790932594177497), (Int.ofNat 466004492319993653103), (Int.ofNat 1762246229736741988), (Int.negOfNat 1653163765009078581), (Int.ofNat 5528740765849369), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(667358544230829720873774970435083/562949953421312000000000000000000), (-2565301098456251681893900977499/140737488355328000000000000000000), (3309396667813333401137721942797/1125899906842624000000000000000000), (741264687942734897051550874731/562949953421312000000000000000000), (-389819516055225288230891310779/562949953421312000000000000000000), (4575314398964141681252847777/112589990684262400000000000000000), (12330985191504957726512535667/1125899906842624000000000000000000), (-1298114325872724549660609509/1125899906842624000000000000000000), (-24143226408773531591488611/281474976710656000000000000000000), (14534008848896773838635859/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial155.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial155.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial155.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial155 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 1308365970549469548958193073352796), (Int.negOfNat 9060884597820848993905626627656), (Int.negOfNat 863086251857066676153632645611), (Int.negOfNat 1770612095170816607513759812668), (Int.ofNat 6622137518107726212932580538), (Int.ofNat 71461101217671417971918590211), (Int.negOfNat 6810929942927917553673173562), (Int.negOfNat 821508176906056084486661724), (Int.ofNat 124028299322974764583854893), (Int.ofNat 4525639324076134949249364), (Int.negOfNat 1111829077932556503212673), (Int.negOfNat 11256236011013708678222), (Int.ofNat 6382056561151373912908), (Int.negOfNat 12485099092930653556), (Int.negOfNat 26159636877814819944), (Int.ofNat 231880571021872334), (Int.ofNat 86154024936200380), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(327091492637367387239548268338199/281474976710656000000000000000000), (-1132610574727606124238203328457/140737488355328000000000000000000), (-863086251857066676153632645611/1125899906842624000000000000000000), (-442653023792704151878439953167/281474976710656000000000000000000), (3311068759053863106466290269/562949953421312000000000000000000), (71461101217671417971918590211/1125899906842624000000000000000000), (-3405464971463958776836586781/562949953421312000000000000000000), (-205377044226514021121665431/281474976710656000000000000000000), (124028299322974764583854893/1125899906842624000000000000000000), (1131409831019033737312341/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial155.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial155.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial155.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial155 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 1274511548890575260356673767765298), (Int.negOfNat 29375746485536995031415421054143), (Int.negOfNat 7567208559898821512464843026462), (Int.negOfNat 179252419208535832520880486311), (Int.ofNat 225074259799381376047596773692), (Int.negOfNat 23269540808137944085282899825), (Int.negOfNat 4926037176107938024862903329), (Int.ofNat 837548540779737582200451994), (Int.ofNat 35938979777552179081176230), (Int.negOfNat 10593550635184050170294210), (Int.negOfNat 63550078746019233303418), (Int.ofNat 76538722858352095514135), (Int.negOfNat 696771067208118895510), (Int.negOfNat 372391589583813102812), (Int.ofNat 6254507050446113597), (Int.ofNat 1360963529387538610), (Int.negOfNat 34143868012475524), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(637255774445287630178336883882649/562949953421312000000000000000000), (-29375746485536995031415421054143/1125899906842624000000000000000000), (-3783604279949410756232421513231/562949953421312000000000000000000), (-179252419208535832520880486311/1125899906842624000000000000000000), (56268564949845344011899193423/281474976710656000000000000000000), (-930781632325517763411315993/45035996273704960000000000000000), (-4926037176107938024862903329/1125899906842624000000000000000000), (418774270389868791100225997/562949953421312000000000000000000), (3593897977755217908117623/112589990684262400000000000000000), (-1059355063518405017029421/112589990684262400000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial155.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial155.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial155.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial155 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 1186709567406999156865924119758052), (Int.negOfNat 57012479296467313108871947179162), (Int.negOfNat 5705012781088685280681301155010), (Int.ofNat 380949271203501250991006567873), (Int.negOfNat 68967226835405364353224320678), (Int.negOfNat 15716399578844283034609695561), (Int.ofNat 4508847173156914938807755481), (Int.ofNat 176357724306706316530191307), (Int.negOfNat 83848967595212854868940147), (Int.ofNat 251078139240305242702450), (Int.ofNat 789551083552955493712956), (Int.negOfNat 15549867605779743668259), (Int.negOfNat 4668935800698111650051), (Int.ofNat 130703509459347136736), (Int.ofNat 19292559214318579041), (Int.negOfNat 642451646623264461), (Int.negOfNat 69813202704539942), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(296677391851749789216481029939513/281474976710656000000000000000000), (-28506239648233656554435973589581/562949953421312000000000000000000), (-570501278108868528068130115501/112589990684262400000000000000000), (380949271203501250991006567873/1125899906842624000000000000000000), (-34483613417702682176612160339/562949953421312000000000000000000), (-15716399578844283034609695561/1125899906842624000000000000000000), (4508847173156914938807755481/1125899906842624000000000000000000), (176357724306706316530191307/1125899906842624000000000000000000), (-83848967595212854868940147/1125899906842624000000000000000000), (5021562784806104854049/22517998136852480000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial155.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial155.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial155.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial155 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 1051596313561684302168827981635039), (Int.negOfNat 77862216730206436972080510372685), (Int.negOfNat 5271937583255016120409697955075), (Int.negOfNat 117180138622613242819484574303), (Int.ofNat 10309912697435728224794740683), (Int.ofNat 21640004790884501298451681505), (Int.negOfNat 56045771121957815046484863), (Int.negOfNat 550009159788192964666242711), (Int.ofNat 13706677114615372922817293), (Int.ofNat 6866330054553877789103502), (Int.negOfNat 260652517221419796828714), (Int.negOfNat 50451283604963794515511), (Int.ofNat 2282834042504466430847), (Int.ofNat 247600672658030171250), (Int.negOfNat 12350229325007453137), (Int.negOfNat 900683847820063029), (Int.ofNat 48685655188369592), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(1051596313561684302168827981635039/1125899906842624000000000000000000), (-15572443346041287394416102074537/225179981368524800000000000000000), (-210877503330200644816387918203/45035996273704960000000000000000), (-117180138622613242819484574303/1125899906842624000000000000000000), (10309912697435728224794740683/1125899906842624000000000000000000), (4328000958176900259690336301/225179981368524800000000000000000), (-56045771121957815046484863/1125899906842624000000000000000000), (-550009159788192964666242711/1125899906842624000000000000000000), (13706677114615372922817293/1125899906842624000000000000000000), (3433165027276938894551751/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial155.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial155.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial155.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial155 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 874636804703910049453875669536453), (Int.negOfNat 98524155502539215982770854593687), (Int.negOfNat 4327469678973543237913034489690), (Int.ofNat 569587058574248892613224783286), (Int.ofNat 107112187267470208136633499361), (Int.negOfNat 8545686226815820841987872078), (Int.negOfNat 3050411388947047683964748181), (Int.ofNat 219946573628048250374205556), (Int.ofNat 49152025970649993147330554), (Int.negOfNat 3586509283675043661208622), (Int.negOfNat 454972031827776360260274), (Int.ofNat 34295668053607795415791), (Int.ofNat 2680061100758451899500), (Int.negOfNat 209906854558129629902), (Int.negOfNat 10968008719244882231), (Int.ofNat 902282498663298352), (Int.ofNat 46201486884932470), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(874636804703910049453875669536453/1125899906842624000000000000000000), (-98524155502539215982770854593687/1125899906842624000000000000000000), (-432746967897354323791303448969/112589990684262400000000000000000), (284793529287124446306612391643/562949953421312000000000000000000), (107112187267470208136633499361/1125899906842624000000000000000000), (-4272843113407910420993936039/562949953421312000000000000000000), (-3050411388947047683964748181/1125899906842624000000000000000000), (54986643407012062593551389/281474976710656000000000000000000), (24576012985324996573665277/562949953421312000000000000000000), (-1793254641837521830604311/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial155.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial155.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial155.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial155 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 666118931402387878069640449983399), (Int.negOfNat 106702018473183409505011580005187), (Int.ofNat 460218242758304149473730819035), (Int.ofNat 783255007028345113987129751792), (Int.negOfNat 63606827030456287050406155768), (Int.negOfNat 14346003221835905278773226972), (Int.ofNat 2208475770907774688333120194), (Int.ofNat 275879703656901206040559760), (Int.negOfNat 40752506527868697565302307), (Int.negOfNat 3213160929184610756911284), (Int.ofNat 446216291108657544515283), (Int.ofNat 22902214417697471183870), (Int.negOfNat 3154665439449841789836), (Int.negOfNat 108396503763973579096), (Int.ofNat 15447445531965629334), (Int.ofNat 362223371840936444), (Int.negOfNat 51421584454459924), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(666118931402387878069640449983399/1125899906842624000000000000000000), (-106702018473183409505011580005187/1125899906842624000000000000000000), (92043648551660829894746163807/225179981368524800000000000000000), (48953437939271569624195609487/70368744177664000000000000000000), (-7950853378807035881300769471/140737488355328000000000000000000), (-3586500805458976319693306743/281474976710656000000000000000000), (1104237885453887344166560097/562949953421312000000000000000000), (3448496295711265075506997/14073748835532800000000000000000), (-40752506527868697565302307/1125899906842624000000000000000000), (-803290232296152689227821/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial155.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial155.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial155.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial155 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 459510093699519546182891143591781), (Int.negOfNat 98144235250309652324039120658513), (Int.ofNat 3118655550840502377356281132657), (Int.ofNat 125552666656817329052875036995), (Int.negOfNat 49368780152921854781494720208), (Int.ofNat 14531096060946997827777796966), (Int.ofNat 987094066672195784990900790), (Int.negOfNat 374380768011216084077084317), (Int.negOfNat 14412092483055160241661808), (Int.ofNat 4979220748979486228032623), (Int.ofNat 122404483774067794109232), (Int.negOfNat 41563270975569985034886), (Int.negOfNat 636953823700155296777), (Int.ofNat 236024446861987511237), (Int.ofNat 2137969306779499596), (Int.negOfNat 967734518192003223), (Int.negOfNat 17586359638306315), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(459510093699519546182891143591781/1125899906842624000000000000000000), (-98144235250309652324039120658513/1125899906842624000000000000000000), (3118655550840502377356281132657/1125899906842624000000000000000000), (25110533331363465810575007399/225179981368524800000000000000000), (-3085548759557615923843420013/70368744177664000000000000000000), (7265548030473498913888898483/562949953421312000000000000000000), (98709406667219578499090079/112589990684262400000000000000000), (-374380768011216084077084317/1125899906842624000000000000000000), (-900755780190947515103863/70368744177664000000000000000000), (4979220748979486228032623/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial155.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial155.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial155.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial155 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 276389914024168774812848024826910), (Int.negOfNat 84561625236377432765782625005792), (Int.ofNat 3832279314306097951374196063683), (Int.ofNat 261191624258556248238151415253), (Int.ofNat 54170608886622632012396801660), (Int.negOfNat 1719662843330731941807289868), (Int.negOfNat 2712146454366801762152930385), (Int.ofNat 19254757295990013144557019), (Int.ofNat 46698643865492010954537526), (Int.negOfNat 297838560520206440631187), (Int.negOfNat 473764438502800347501814), (Int.ofNat 3537256882596564835288), (Int.ofNat 3179660168374650767029), (Int.negOfNat 27430190108628872307), (Int.negOfNat 15072001695481079890), (Int.ofNat 152367224070883785), (Int.ofNat 44619137971674871), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(27638991402416877481284802482691/112589990684262400000000000000000), (-2642550788636794773930707031431/35184372088832000000000000000000), (3832279314306097951374196063683/1125899906842624000000000000000000), (261191624258556248238151415253/1125899906842624000000000000000000), (2708530444331131600619840083/56294995342131200000000000000000), (-429915710832682985451822467/281474976710656000000000000000000), (-542429290873360352430586077/225179981368524800000000000000000), (19254757295990013144557019/1125899906842624000000000000000000), (23349321932746005477268763/562949953421312000000000000000000), (-297838560520206440631187/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial155.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial155.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial155.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial155 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 125337238597461028818945028092594), (Int.negOfNat 64969605651404410862203613292555), (Int.ofNat 6001133158026941007821525526081), (Int.ofNat 277903738908143285604372357416), (Int.negOfNat 75101695910779627054751885759), (Int.negOfNat 15744613973713902797511258188), (Int.ofNat 1219139003430956154862228976), (Int.ofNat 358873541562437643345794988), (Int.negOfNat 17838748290495144132722097), (Int.negOfNat 4562368959615450031454938), (Int.ofNat 177248907248830214832597), (Int.ofNat 36960970606217486011432), (Int.negOfNat 1213572365957983036888), (Int.negOfNat 206075872516457538276), (Int.ofNat 5981593279088867162), (Int.ofNat 837884058421343692), (Int.negOfNat 11028767608319840), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(62668619298730514409472514046297/562949953421312000000000000000000), (-12993921130280882172440722658511/225179981368524800000000000000000), (6001133158026941007821525526081/1125899906842624000000000000000000), (34737967363517910700546544677/140737488355328000000000000000000), (-75101695910779627054751885759/1125899906842624000000000000000000), (-3936153493428475699377814547/281474976710656000000000000000000), (76196187714434759678889311/70368744177664000000000000000000), (89718385390609410836448747/281474976710656000000000000000000), (-17838748290495144132722097/1125899906842624000000000000000000), (-2281184479807725015727469/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial155.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial155.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial155.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial155 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 20037643776263519600658756505951), (Int.negOfNat 40925696162374995500429191332857), (Int.ofNat 5090282394206408643014766828286), (Int.negOfNat 609064698900826953326458878180), (Int.negOfNat 93567304619057023792955257438), (Int.ofNat 14180636553513456719858160701), (Int.ofNat 2210962279124883537197779723), (Int.negOfNat 267780329439227290444891756), (Int.negOfNat 35631984485097798396382286), (Int.ofNat 3224643230092567428552474), (Int.ofNat 357735520661106704289912), (Int.negOfNat 25567575592498379185667), (Int.negOfNat 2396025589714382590486), (Int.ofNat 141784666443796258508), (Int.ofNat 11349860123273088949), (Int.negOfNat 602531425266386224), (Int.negOfNat 37816691488889818), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(20037643776263519600658756505951/1125899906842624000000000000000000), (-40925696162374995500429191332857/1125899906842624000000000000000000), (2545141197103204321507383414143/562949953421312000000000000000000), (-30453234945041347666322943909/56294995342131200000000000000000), (-46783652309528511896477628719/562949953421312000000000000000000), (14180636553513456719858160701/1125899906842624000000000000000000), (2210962279124883537197779723/1125899906842624000000000000000000), (-66945082359806822611222939/281474976710656000000000000000000), (-17815992242548899198191143/562949953421312000000000000000000), (1612321615046283714276237/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial155.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial155.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial155.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial155 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 47268372662434563501711977282483), (Int.negOfNat 29456070775892844213313625676114), (Int.ofNat 629684547370391743389869787708), (Int.negOfNat 628903791489587681949205106401), (Int.ofNat 82498322825768594966042231330), (Int.ofNat 10698597754834835369019116280), (Int.negOfNat 2641328916849110089821212241), (Int.negOfNat 206406957699925856596618227), (Int.ofNat 41525618906156790726434307), (Int.ofNat 2658875945851231735091366), (Int.negOfNat 401125309396364957901352), (Int.negOfNat 22140503492994666251117), (Int.ofNat 2612666769018123867479), (Int.ofNat 126799575264022505596), (Int.negOfNat 12187561861456422393), (Int.negOfNat 538128622804405021), (Int.ofNat 37376412694017644), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-47268372662434563501711977282483/1125899906842624000000000000000000), (-14728035387946422106656812838057/562949953421312000000000000000000), (157421136842597935847467446927/281474976710656000000000000000000), (-628903791489587681949205106401/1125899906842624000000000000000000), (8249832282576859496604223133/112589990684262400000000000000000), (267464943870870884225477907/28147497671065600000000000000000), (-2641328916849110089821212241/1125899906842624000000000000000000), (-206406957699925856596618227/1125899906842624000000000000000000), (41525618906156790726434307/1125899906842624000000000000000000), (1329437972925615867545683/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial155.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial155.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial155.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial155 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 107214595872234209935002131113388), (Int.negOfNat 31541534818452224283193593734978), (Int.negOfNat 998901570316666381696597898986), (Int.ofNat 2759247799075666675546889160), (Int.ofNat 24477401552542572143441304508), (Int.negOfNat 17968174975955091561055622633), (Int.negOfNat 596500307102436741136618819), (Int.ofNat 413083882711859400564703375), (Int.ofNat 11247795457060278168080969), (Int.negOfNat 5066434801051122146765350), (Int.negOfNat 129781613129138498731928), (Int.ofNat 39858529515103151539845), (Int.ofNat 969576552801161400197), (Int.negOfNat 217664117890810445110), (Int.negOfNat 5016104183896558315), (Int.ofNat 888017592322379883), (Int.ofNat 14204975669282346), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-26803648968058552483750532778347/281474976710656000000000000000000), (-15770767409226112141596796867489/562949953421312000000000000000000), (-499450785158333190848298949493/562949953421312000000000000000000), (68981194976891666888672229/28147497671065600000000000000000), (6119350388135643035860326127/281474976710656000000000000000000), (-17968174975955091561055622633/1125899906842624000000000000000000), (-596500307102436741136618819/1125899906842624000000000000000000), (3304671061694875204517627/9007199254740992000000000000000), (11247795457060278168080969/1125899906842624000000000000000000), (-101328696021022442935307/22517998136852480000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial155.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial155.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial155.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial155 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 174439605974827362299921964324945), (Int.negOfNat 36088032710126002109504981504024), (Int.negOfNat 1701443240515263005552268760226), (Int.negOfNat 391609136767128719184776672821), (Int.negOfNat 83181295716619196331335402580), (Int.ofNat 4554137111080491667940288875), (Int.ofNat 3202973664209806307478601593), (Int.negOfNat 50699292372457981423838786), (Int.negOfNat 52198899321522003050195950), (Int.ofNat 291508724976118092140592), (Int.ofNat 511267285072889484328748), (Int.ofNat 89249877869875715851), (Int.negOfNat 3341452249483839600644), (Int.negOfNat 12108459847069865518), (Int.ofNat 15560098723899451909), (Int.ofNat 112968961136600402), (Int.negOfNat 51918199869911712), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-34887921194965472459984392864989/225179981368524800000000000000000), (-4511004088765750263688122688003/140737488355328000000000000000000), (-850721620257631502776134380113/562949953421312000000000000000000), (-391609136767128719184776672821/1125899906842624000000000000000000), (-4159064785830959816566770129/56294995342131200000000000000000), (36433096888643933343522311/9007199254740992000000000000000), (3202973664209806307478601593/1125899906842624000000000000000000), (-25349646186228990711919393/562949953421312000000000000000000), (-1043977986430440061003919/22517998136852480000000000000000), (18219295311007380758787/70368744177664000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial155.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial155.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial155.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial155 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 257553688466129651974702209104654), (Int.negOfNat 49348570472423395450590016180261), (Int.negOfNat 5035001261946700133254666671437), (Int.negOfNat 475294675070123687430008499643), (Int.ofNat 89518435754390536195088882333), (Int.ofNat 19732167161378262930244895417), (Int.negOfNat 1626531521523948602989300900), (Int.negOfNat 431965223955602360615590468), (Int.ofNat 21117981511638549566963537), (Int.ofNat 5464046218883039426021198), (Int.negOfNat 166023308028669520932363), (Int.negOfNat 43930103688671841336532), (Int.ofNat 847511589566695573464), (Int.ofNat 242751197963446498972), (Int.negOfNat 3068233329698000856), (Int.negOfNat 993679961465227170), (Int.ofNat 16677633738272160), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-128776844233064825987351104552327/562949953421312000000000000000000), (-49348570472423395450590016180261/1125899906842624000000000000000000), (-5035001261946700133254666671437/1125899906842624000000000000000000), (-475294675070123687430008499643/1125899906842624000000000000000000), (89518435754390536195088882333/1125899906842624000000000000000000), (19732167161378262930244895417/1125899906842624000000000000000000), (-16265315215239486029893009/11258999068426240000000000000000), (-107991305988900590153897617/281474976710656000000000000000000), (21117981511638549566963537/1125899906842624000000000000000000), (2732023109441519713010599/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial155.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial155.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial155.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial155 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 378280907906073254111947706730706), (Int.negOfNat 71221860490496242406886614198034), (Int.negOfNat 4780435460511773811186910505453), (Int.ofNat 590968911939015112008589187660), (Int.ofNat 110084745419415346805460217864), (Int.negOfNat 18072686406328076832520143830), (Int.negOfNat 2745522649552717519999153825), (Int.ofNat 346728662888756880584705041), (Int.ofNat 46989204149983110449276278), (Int.negOfNat 3728338270492111546467687), (Int.negOfNat 484299750533120628106576), (Int.ofNat 25337242716330622311606), (Int.ofNat 3266971803093481413125), (Int.negOfNat 118862733866812587493), (Int.negOfNat 15449678549177632986), (Int.ofNat 390704412555435659), (Int.ofNat 45115753387126659), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-189140453953036627055973853365353/562949953421312000000000000000000), (-35610930245248121203443307099017/562949953421312000000000000000000), (-4780435460511773811186910505453/1125899906842624000000000000000000), (29548445596950755600429459383/56294995342131200000000000000000), (13760593177426918350682527233/140737488355328000000000000000000), (-1807268640632807683252014383/112589990684262400000000000000000), (-109820905982108700799966153/45035996273704960000000000000000), (346728662888756880584705041/1125899906842624000000000000000000), (23494602074991555224638139/562949953421312000000000000000000), (-3728338270492111546467687/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial155.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial155.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial155.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial155 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 534057233186819438415819583792866), (Int.negOfNat 81509479406448954862569025039451), (Int.negOfNat 401971461918586478418209069003), (Int.ofNat 561738988714156497237863039794), (Int.negOfNat 105776821828764819195194239034), (Int.negOfNat 11237275751322646716435108658), (Int.ofNat 3770001310359012420268251885), (Int.ofNat 294429197454518795273729657), (Int.negOfNat 55351436049752275927202324), (Int.negOfNat 4242064936124368161851923), (Int.ofNat 478478396371626673244114), (Int.ofNat 36685100364611737992526), (Int.negOfNat 2755814214416297712383), (Int.negOfNat 211847591215165381623), (Int.ofNat 11325069487373544712), (Int.ofNat 887712276499338197), (Int.negOfNat 45292760984898315), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-267028616593409719207909791896433/562949953421312000000000000000000), (-81509479406448954862569025039451/1125899906842624000000000000000000), (-401971461918586478418209069003/1125899906842624000000000000000000), (280869494357078248618931519897/562949953421312000000000000000000), (-52888410914382409597597119517/562949953421312000000000000000000), (-5618637875661323358217554329/562949953421312000000000000000000), (754000262071802484053650377/225179981368524800000000000000000), (294429197454518795273729657/1125899906842624000000000000000000), (-13837859012438068981800581/281474976710656000000000000000000), (-4242064936124368161851923/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial155.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial155.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial155.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial155 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 695979010512583618849625882017375), (Int.negOfNat 79868261283306652116771556334775), (Int.ofNat 521086155457905860359527270147), (Int.negOfNat 79344707081573856186740092291), (Int.ofNat 18960402256099916122776668810), (Int.ofNat 29993291081767750452654161195), (Int.ofNat 793149609845313144788614770), (Int.negOfNat 635944246683103631265279948), (Int.negOfNat 24949356781735474051562455), (Int.ofNat 7066962156296885387134296), (Int.ofNat 315824866790077687104985), (Int.negOfNat 49962855621262846830788), (Int.negOfNat 2368437381778817164116), (Int.ofNat 245214090347187537944), (Int.ofNat 12029858147235552260), (Int.negOfNat 868104894526655470), (Int.negOfNat 38313306904341606), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-5567832084100668950797007056139/9007199254740992000000000000000), (-3194730451332266084670862253391/45035996273704960000000000000000), (521086155457905860359527270147/1125899906842624000000000000000000), (-79344707081573856186740092291/1125899906842624000000000000000000), (1896040225609991612277666881/112589990684262400000000000000000), (5998658216353550090530832239/225179981368524800000000000000000), (79314960984531314478861477/112589990684262400000000000000000), (-158986061670775907816319987/281474976710656000000000000000000), (-4989871356347094810312491/225179981368524800000000000000000), (883370269537110673391787/140737488355328000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial155.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial155.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial155.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial155 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 853035988849662687879653502447601), (Int.negOfNat 75870730918713753576124817637113), (Int.ofNat 2652501617089959935739534219453), (Int.ofNat 1038680829007263748788127786488), (Int.ofNat 190902027866893490456365980789), (Int.negOfNat 9919123155895487222485631362), (Int.negOfNat 5912433080536309068999795311), (Int.negOfNat 7599602985880822344339918), (Int.ofNat 85956469775277737831021508), (Int.ofNat 1465286856816480363043822), (Int.negOfNat 756210503118087747028318), (Int.negOfNat 18583335639028845402051), (Int.ofNat 4455163314063992254146), (Int.ofNat 127669043842286385624), (Int.negOfNat 18790561903111396273), (Int.negOfNat 595512040877798226), (Int.ofNat 73907888231524470), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-853035988849662687879653502447601/1125899906842624000000000000000000), (-75870730918713753576124817637113/1125899906842624000000000000000000), (2652501617089959935739534219453/1125899906842624000000000000000000), (129835103625907968598515973311/140737488355328000000000000000000), (190902027866893490456365980789/1125899906842624000000000000000000), (-4959561577947743611242815681/562949953421312000000000000000000), (-5912433080536309068999795311/1125899906842624000000000000000000), (-3799801492940411172169959/562949953421312000000000000000000), (21489117443819434457755377/281474976710656000000000000000000), (732643428408240181521911/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial155.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial155.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial155.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial155 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 983478383910964457614281944549547), (Int.negOfNat 48532382883016269706203491969069), (Int.ofNat 11400479843845701231194339409837), (Int.ofNat 1368922517161756680629128532336), (Int.negOfNat 173341316574361712108785790915), (Int.negOfNat 46218470905806088112703103092), (Int.ofNat 2053472445508358782223847438), (Int.ofNat 872726984033557097051183165), (Int.negOfNat 11648199987159015976404355), (Int.negOfNat 9739775071407639326260742), (Int.negOfNat 19949509949986117476132), (Int.ofNat 69960726082319271840653), (Int.ofNat 739755575959053441579), (Int.negOfNat 348067239445539307544), (Int.negOfNat 5369896656008525393), (Int.ofNat 1278675970128047597), (Int.ofNat 21972484672681168), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-983478383910964457614281944549547/1125899906842624000000000000000000), (-48532382883016269706203491969069/1125899906842624000000000000000000), (11400479843845701231194339409837/1125899906842624000000000000000000), (85557657322609792539320533271/70368744177664000000000000000000), (-34668263314872342421757158183/225179981368524800000000000000000), (-11554617726451522028175775773/281474976710656000000000000000000), (1026736222754179391111923719/562949953421312000000000000000000), (174545396806711419410236633/225179981368524800000000000000000), (-2329639997431803195280871/225179981368524800000000000000000), (-4869887535703819663130371/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial155.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial155.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial155.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial155 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 1028007016728475281724214989241798), (Int.ofNat 5003772335464961765536670392434), (Int.ofNat 12771630908661904569647990031400), (Int.negOfNat 1119870255917202893091672746286), (Int.negOfNat 317619439029853900885764888863), (Int.ofNat 28744998329647584569809886517), (Int.ofNat 7355679925549894020219006103), (Int.negOfNat 385627677146722838151486581), (Int.negOfNat 106643977154589511715018701), (Int.ofNat 2644845697685893832589804), (Int.ofNat 956503294202676056029778), (Int.negOfNat 8513516265020287615021), (Int.negOfNat 5701008993019393423079), (Int.negOfNat 1021400924243208306), (Int.ofNat 24179163080903097417), (Int.ofNat 135232359310322645), (Int.negOfNat 88449675407418538), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-514003508364237640862107494620899/562949953421312000000000000000000), (2501886167732480882768335196217/562949953421312000000000000000000), (63858154543309522848239950157/5629499534213120000000000000000), (-559935127958601446545836373143/562949953421312000000000000000000), (-317619439029853900885764888863/1125899906842624000000000000000000), (28744998329647584569809886517/1125899906842624000000000000000000), (7355679925549894020219006103/1125899906842624000000000000000000), (-385627677146722838151486581/1125899906842624000000000000000000), (-106643977154589511715018701/1125899906842624000000000000000000), (661211424421473458147451/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial155.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial155.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial155.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial155 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 979637586012201818873158403254696), (Int.ofNat 35928714364908783171740145971670), (Int.ofNat 2066848238720269516891402351396), (Int.negOfNat 1713248092459106409124386826308), (Int.ofNat 206215961998645973748384726709), (Int.ofNat 49083712163235654949569375481), (Int.negOfNat 5440946469855804826119389361), (Int.negOfNat 971976643317100925541891456), (Int.ofNat 61211177093859803338855186), (Int.ofNat 11337886574531433632543794), (Int.negOfNat 376686233801440697407842), (Int.negOfNat 82778458212684531253191), (Int.ofNat 1417773745904017638504), (Int.ofNat 413639535675202114402), (Int.negOfNat 3251727416278172501), (Int.negOfNat 1538506822168081488), (Int.ofNat 1639231146926304), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-122454698251525227359144800406837/140737488355328000000000000000000), (3592871436490878317174014597167/112589990684262400000000000000000), (516712059680067379222850587849/281474976710656000000000000000000), (-428312023114776602281096706577/281474976710656000000000000000000), (206215961998645973748384726709/1125899906842624000000000000000000), (49083712163235654949569375481/1125899906842624000000000000000000), (-5440946469855804826119389361/1125899906842624000000000000000000), (-7593567525914850980796027/8796093022208000000000000000000), (30605588546929901669427593/562949953421312000000000000000000), (5668943287265716816271897/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial155.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial155.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial155.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial155 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 908800319575108158088996446275964), (Int.ofNat 32768628520790392818067672623533), (Int.negOfNat 1140331375174151830185497885575), (Int.ofNat 646605807811518943288065250349), (Int.ofNat 204478077491698519931898949885), (Int.negOfNat 52786966554512483533339572942), (Int.negOfNat 6894947563147388793743852248), (Int.ofNat 918892700958504178164500224), (Int.ofNat 114670060783067780811698355), (Int.negOfNat 7844635572990291364805678), (Int.negOfNat 1063262464225808526932129), (Int.ofNat 41372253603060164726412), (Int.ofNat 6359053490447517050156), (Int.negOfNat 150355617650920276092), (Int.negOfNat 26868424180795531682), (Int.ofNat 403228116668803940), (Int.ofNat 91185604673508870), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-227200079893777039522249111568991/281474976710656000000000000000000), (32768628520790392818067672623533/1125899906842624000000000000000000), (-45613255006966073207419915423/45035996273704960000000000000000), (646605807811518943288065250349/1125899906842624000000000000000000), (40895615498339703986379789977/225179981368524800000000000000000), (-26393483277256241766669786471/562949953421312000000000000000000), (-861868445393423599217981531/140737488355328000000000000000000), (3589424613119156945955079/4398046511104000000000000000000), (22934012156613556162339671/225179981368524800000000000000000), (-3922317786495145682402839/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial155.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial155.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial155.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial155 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 841368374215125323049422408881638), (Int.ofNat 37469263413211285919015809446014), (Int.ofNat 2545181644073617235211119288211), (Int.negOfNat 268274779671308183513336109597), (Int.negOfNat 394815353526097433454706401988), (Int.negOfNat 29563315526050665501023853255), (Int.ofNat 10904107414215953036338323957), (Int.ofNat 955656155643405038363042977), (Int.negOfNat 123719114236728099328817054), (Int.negOfNat 12017203995547507198155361), (Int.ofNat 828654066746956692165542), (Int.ofNat 87955039529859300735778), (Int.negOfNat 3789519827919526982527), (Int.negOfNat 435366922867718922917), (Int.ofNat 12735539573077718488), (Int.ofNat 1603958841696786359), (Int.negOfNat 30254358393552459), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-420684187107562661524711204440819/562949953421312000000000000000000), (18734631706605642959507904723007/562949953421312000000000000000000), (2545181644073617235211119288211/1125899906842624000000000000000000), (-268274779671308183513336109597/1125899906842624000000000000000000), (-98703838381524358363676600497/281474976710656000000000000000000), (-5912663105210133100204770651/225179981368524800000000000000000), (10904107414215953036338323957/1125899906842624000000000000000000), (955656155643405038363042977/1125899906842624000000000000000000), (-61859557118364049664408527/562949953421312000000000000000000), (-12017203995547507198155361/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial155.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial155.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial155.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial155 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 764875018998577319297986611790076), (Int.ofNat 31804001602005932148885597162473), (Int.negOfNat 7911290681234617290184289286426), (Int.negOfNat 2599913464589122806540053191973), (Int.ofNat 58592827731881096221649699404), (Int.ofNat 110681123842974501170251149690), (Int.ofNat 6129576198978580159921631859), (Int.negOfNat 1630327193119694095743014871), (Int.negOfNat 119114485601958910273629964), (Int.ofNat 13507425305749199039425733), (Int.ofNat 1096826964442521207579224), (Int.negOfNat 74805570556329476411734), (Int.negOfNat 6413982219020333114117), (Int.ofNat 302158402478335556883), (Int.ofNat 26638378514181139710), (Int.negOfNat 917818712580624169), (Int.negOfNat 84383158190723817), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-191218754749644329824496652947519/281474976710656000000000000000000), (31804001602005932148885597162473/1125899906842624000000000000000000), (-3955645340617308645092144643213/562949953421312000000000000000000), (-2599913464589122806540053191973/1125899906842624000000000000000000), (14648206932970274055412424851/281474976710656000000000000000000), (11068112384297450117025114969/112589990684262400000000000000000), (6129576198978580159921631859/1125899906842624000000000000000000), (-1630327193119694095743014871/1125899906842624000000000000000000), (-29778621400489727568407491/281474976710656000000000000000000), (13507425305749199039425733/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial155.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial155.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial155.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial155 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 749071224987093197103589899009658), (Int.negOfNat 19950387994595608660060567649015), (Int.negOfNat 13015593548966401160055080353133), (Int.ofNat 2236057084799072569441205550620), (Int.ofNat 1008644252167962019977538059723), (Int.ofNat 27262267451679739355737978755), (Int.negOfNat 18674890817995263502021476134), (Int.negOfNat 1052755430209577926772842002), (Int.ofNat 188458903101593206707454953), (Int.ofNat 12457558815515162918987046), (Int.negOfNat 1249376513877182904396757), (Int.negOfNat 86506728142617005410482), (Int.ofNat 5953157076105644048888), (Int.ofNat 412917499978212420712), (Int.negOfNat 21513059728262039358), (Int.negOfNat 1474108381926126828), (Int.ofNat 58869485640178614), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-374535612493546598551794949504829/562949953421312000000000000000000), (-3990077598919121732012113529803/225179981368524800000000000000000), (-13015593548966401160055080353133/1125899906842624000000000000000000), (111802854239953628472060277531/56294995342131200000000000000000), (1008644252167962019977538059723/1125899906842624000000000000000000), (5452453490335947871147595751/225179981368524800000000000000000), (-9337445408997631751010738067/562949953421312000000000000000000), (-526377715104788963386421001/562949953421312000000000000000000), (188458903101593206707454953/1125899906842624000000000000000000), (6228779407757581459493523/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial155.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial155.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial155.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial155 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 807411969015886071062885490142292), (Int.negOfNat 14565214767554673383019152598128), (Int.ofNat 21978520047359715899302066196150), (Int.ofNat 8200794979751281257349222659853), (Int.ofNat 107739047241959343049932644699), (Int.negOfNat 187643033684004095169992608710), (Int.negOfNat 8988374990987726331673161239), (Int.ofNat 2285106811174522475781207824), (Int.ofNat 132676621518836296262661844), (Int.negOfNat 18096516987079870382354668), (Int.negOfNat 1081755762331642529227168), (Int.ofNat 101651971662955636547993), (Int.ofNat 5902683691613390289378), (Int.negOfNat 426750325994300788576), (Int.negOfNat 23467497806418152793), (Int.ofNat 1367982913776126608), (Int.ofNat 77580711707938764), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-201852992253971517765721372535573/281474976710656000000000000000000), (-910325922972167086438697037383/70368744177664000000000000000000), (439570400947194317986041323923/22517998136852480000000000000000), (8200794979751281257349222659853/1125899906842624000000000000000000), (107739047241959343049932644699/1125899906842624000000000000000000), (-18764303368400409516999260871/112589990684262400000000000000000), (-8988374990987726331673161239/1125899906842624000000000000000000), (142819175698407654736325489/70368744177664000000000000000000), (33169155379709074065665461/281474976710656000000000000000000), (-4524129246769967595588667/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial155.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial155.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial155.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial155 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 687561652563431860425406464480554), (Int.ofNat 159582464772903381899135201991225), (Int.ofNat 58281057910881429701211360513179), (Int.ofNat 1527178730336658702566017640994), (Int.negOfNat 1602204208609450225008490983905), (Int.negOfNat 85877116227336314835056724419), (Int.ofNat 23811485962930458197630943292), (Int.ofNat 1395313516255228820402198471), (Int.negOfNat 227605860884147573867950879), (Int.negOfNat 12841804262414268497138122), (Int.ofNat 1520120402042071821853936), (Int.ofNat 78751362267286162395583), (Int.negOfNat 7460533174615532837719), (Int.negOfNat 348960374151437353852), (Int.ofNat 27926144482898808625), (Int.ofNat 1174352946309188157), (Int.negOfNat 85217130725876418), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-343780826281715930212703232240277/562949953421312000000000000000000), (6383298590916135275965408079649/45035996273704960000000000000000), (58281057910881429701211360513179/1125899906842624000000000000000000), (763589365168329351283008820497/562949953421312000000000000000000), (-320440841721890045001698196781/225179981368524800000000000000000), (-85877116227336314835056724419/1125899906842624000000000000000000), (5952871490732614549407735823/281474976710656000000000000000000), (1395313516255228820402198471/1125899906842624000000000000000000), (-227605860884147573867950879/1125899906842624000000000000000000), (-6420902131207134248569061/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial155.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial155.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial155.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial155.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial155 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial155 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial155 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 960762063950066595050255995626491), (Int.negOfNat 200944357830887723350425200580423), (Int.ofNat 66306405904389708024000942801870), (Int.negOfNat 1180033927179333494966878618211), (Int.negOfNat 1644811598172015270041918891469), (Int.ofNat 84887193044572784315583026914), (Int.ofNat 23906396860256430657591116701), (Int.negOfNat 1393840362490073299604509061), (Int.negOfNat 227722042925616327914768199), (Int.ofNat 12840451560189064907353912), (Int.ofNat 1520209926964386219974846), (Int.negOfNat 78750479928337400981103), (Int.negOfNat 7460533174615532837719), (Int.ofNat 348960374151437353852), (Int.ofNat 27926144482898808625), (Int.negOfNat 1174352946309188157), (Int.negOfNat 85217130725876418), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-960762063950066595050255995626491/1125899906842624000000000000000000), (-200944357830887723350425200580423/1125899906842624000000000000000000), (6630640590438970802400094280187/112589990684262400000000000000000), (-1180033927179333494966878618211/1125899906842624000000000000000000), (-1644811598172015270041918891469/1125899906842624000000000000000000), (42443596522286392157791513457/562949953421312000000000000000000), (23906396860256430657591116701/1125899906842624000000000000000000), (-1393840362490073299604509061/1125899906842624000000000000000000), (-227722042925616327914768199/1125899906842624000000000000000000), (1605056445023633113419239/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial155.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial155.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial155.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 1129164779374835179378022683016885), (Int.ofNat 8046582246115709058121006343346), (Int.ofNat 31008520851708871604718392668046), (Int.negOfNat 8218309574452759095369875497777), (Int.ofNat 61205218642731160387617198269), (Int.ofNat 187861752232312453177687545325), (Int.negOfNat 8886450662837066688553049619), (Int.negOfNat 2285598120458626465645620144), (Int.ofNat 132552944034129241686240864), (Int.ofNat 18097054965297462015009168), (Int.negOfNat 1081660794177575112578568), (Int.negOfNat 101652302540061422078423), (Int.ofNat 5902683691613390289378), (Int.ofNat 426750325994300788576), (Int.negOfNat 23467497806418152793), (Int.negOfNat 1367982913776126608), (Int.ofNat 77580711707938764), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-225832955874967035875604536603377/225179981368524800000000000000000), (4023291123057854529060503171673/562949953421312000000000000000000), (15504260425854435802359196334023/562949953421312000000000000000000), (-8218309574452759095369875497777/1125899906842624000000000000000000), (61205218642731160387617198269/1125899906842624000000000000000000), (7514470089292498127107501813/45035996273704960000000000000000), (-8886450662837066688553049619/1125899906842624000000000000000000), (-142849882528664154102851259/70368744177664000000000000000000), (4142279501066538802695027/35184372088832000000000000000000), (1131065935331091375938073/70368744177664000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial155.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial155.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial155.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 1048612527213476631133701359128989), (Int.ofNat 47889222961889481315183789010227), (Int.negOfNat 5166081107093054017604928518896), (Int.negOfNat 2601278107153113590078779962918), (Int.ofNat 970140407327396276526396414467), (Int.negOfNat 25915299717438425762796661004), (Int.negOfNat 18593024302333525418809345138), (Int.ofNat 1050450782994619834733927042), (Int.ofNat 188361143602781781623726223), (Int.negOfNat 12455285626143965454303716), (Int.negOfNat 1249301960638300557274277), (Int.ofNat 86505294341825268111952), (Int.ofNat 5953157076105644048888), (Int.negOfNat 412917499978212420712), (Int.negOfNat 21513059728262039358), (Int.ofNat 1474108381926126828), (Int.ofNat 58869485640178614), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-1048612527213476631133701359128989/1125899906842624000000000000000000), (47889222961889481315183789010227/1125899906842624000000000000000000), (-322880069193315876100308032431/70368744177664000000000000000000), (-1300639053576556795039389981459/562949953421312000000000000000000), (970140407327396276526396414467/1125899906842624000000000000000000), (-6478824929359606440699165251/281474976710656000000000000000000), (-9296512151166762709404672569/562949953421312000000000000000000), (525225391497309917366963521/562949953421312000000000000000000), (188361143602781781623726223/1125899906842624000000000000000000), (-3113821406535991363575929/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial155.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial155.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial155.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 980630407578894563485852762286018), (Int.ofNat 22040456633299520794584611624628), (Int.negOfNat 3051503885506952198809825865841), (Int.ofNat 1992186547154470996889056899754), (Int.ofNat 37725959756315285299638844303), (Int.negOfNat 108584007943256630577882102592), (Int.ofNat 6169982731781617370126162978), (Int.ofNat 1626848623122981006616643911), (Int.negOfNat 119160126981430901201519344), (Int.negOfNat 13504044014782813979224853), (Int.ofNat 1096860709505023339282004), (Int.ofNat 74803475001326168052344), (Int.negOfNat 6413982219020333114117), (Int.negOfNat 302158402478335556883), (Int.ofNat 26638378514181139710), (Int.ofNat 917818712580624169), (Int.negOfNat 84383158190723817), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-490315203789447281742926381143009/562949953421312000000000000000000), (5510114158324880198646152906157/281474976710656000000000000000000), (-3051503885506952198809825865841/1125899906842624000000000000000000), (996093273577235498444528449877/562949953421312000000000000000000), (37725959756315285299638844303/1125899906842624000000000000000000), (-1696625124113384852779407853/17592186044416000000000000000000), (3084991365890808685063081489/562949953421312000000000000000000), (1626848623122981006616643911/1125899906842624000000000000000000), (-7447507936339431325094959/70368744177664000000000000000000), (-13504044014782813979224853/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial155.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial155.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial155.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 935122145821948907296399688782936), (Int.ofNat 28027809349418263003709594259518), (Int.ofNat 3432865463413511586512013070123), (Int.negOfNat 418048585286879779666810591864), (Int.negOfNat 393297794354537357934702079932), (Int.ofNat 31839686289128693870220278922), (Int.ofNat 10893055083333247509657771893), (Int.negOfNat 959357396149671702343371807), (Int.negOfNat 123700760216306778097890684), (Int.ofNat 12020766765763117987397521), (Int.ofNat 828637970485848765766472), (Int.negOfNat 87957355669599799448788), (Int.negOfNat 3789519827919526982527), (Int.ofNat 435366922867718922917), (Int.ofNat 12735539573077718488), (Int.negOfNat 1603958841696786359), (Int.negOfNat 30254358393552459), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-116890268227743613412049961097867/140737488355328000000000000000000), (14013904674709131501854797129759/562949953421312000000000000000000), (3432865463413511586512013070123/1125899906842624000000000000000000), (-52256073160859972458351323983/140737488355328000000000000000000), (-98324448588634339483675519983/281474976710656000000000000000000), (15919843144564346935110139461/562949953421312000000000000000000), (10893055083333247509657771893/1125899906842624000000000000000000), (-959357396149671702343371807/1125899906842624000000000000000000), (-30925190054076694524472671/281474976710656000000000000000000), (12020766765763117987397521/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial155.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial155.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial155.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 873403847094022022354903178074394), (Int.ofNat 28270217386809108372566161168360), (Int.negOfNat 4157147397366048571325650865855), (Int.negOfNat 1233523232999227569783657274548), (Int.ofNat 227094469346363666203042812884), (Int.ofNat 54635015494404285529079353399), (Int.negOfNat 6953453921348192205003413118), (Int.negOfNat 921814212158363702837280874), (Int.ofNat 114746790117454287846900275), (Int.ofNat 7847407861498547452514638), (Int.negOfNat 1063323659238676918830219), (Int.negOfNat 41374018280957687555372), (Int.ofNat 6359053490447517050156), (Int.ofNat 150355617650920276092), (Int.negOfNat 26868424180795531682), (Int.negOfNat 403228116668803940), (Int.ofNat 91185604673508870), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-436701923547011011177451589037197/562949953421312000000000000000000), (706755434670227709314154029209/28147497671065600000000000000000), (-831429479473209714265130173171/225179981368524800000000000000000), (-308380808249806892445914318637/281474976710656000000000000000000), (56773617336590916550760703221/281474976710656000000000000000000), (54635015494404285529079353399/1125899906842624000000000000000000), (-3476726960674096102501706559/562949953421312000000000000000000), (-460907106079181851418640437/562949953421312000000000000000000), (4589871604698171513876011/45035996273704960000000000000000), (3923703930749273726257319/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial155.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial155.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial155.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 838509122734723953132101975107874), (Int.ofNat 6858969374716578647595199094811), (Int.negOfNat 3796690273960279143580930305334), (Int.ofNat 1370338089846336187031969961939), (Int.ofNat 243080662187959958634644031538), (Int.negOfNat 48143723954014269587699049079), (Int.negOfNat 5530126499904297748707837781), (Int.ofNat 970614997554643750302819956), (Int.ofNat 61324784803560901790283576), (Int.negOfNat 11336655704802866919629384), (Int.negOfNat 376775592273992714256482), (Int.ofNat 82777796458472960192331), (Int.ofNat 1417773745904017638504), (Int.negOfNat 413639535675202114402), (Int.negOfNat 3251727416278172501), (Int.ofNat 1538506822168081488), (Int.ofNat 1639231146926304), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-419254561367361976566050987553937/562949953421312000000000000000000), (6858969374716578647595199094811/1125899906842624000000000000000000), (-1898345136980139571790465152667/562949953421312000000000000000000), (1370338089846336187031969961939/1125899906842624000000000000000000), (121540331093979979317322015769/562949953421312000000000000000000), (-48143723954014269587699049079/1125899906842624000000000000000000), (-5530126499904297748707837781/1125899906842624000000000000000000), (242653749388660937575704989/281474976710656000000000000000000), (7665598100445112723785447/140737488355328000000000000000000), (-1417081963100358364953673/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial155.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial155.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial155.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 826886557409331146946750934872226), (Int.ofNat 11452092907097289792327404295186), (Int.ofNat 5788474217756199306127396463832), (Int.ofNat 1094654859867486147174257621023), (Int.negOfNat 276955942587949957159229224534), (Int.negOfNat 28936908996311432950303251569), (Int.ofNat 7260679553591267650814138113), (Int.ofNat 386172472467698032128991891), (Int.negOfNat 106524906211743586962776881), (Int.negOfNat 2645481429210295869211074), (Int.ofNat 956410428028318917155758), (Int.ofNat 8514067726863263499071), (Int.negOfNat 5701008993019393423079), (Int.ofNat 1021400924243208306), (Int.ofNat 24179163080903097417), (Int.negOfNat 135232359310322645), (Int.negOfNat 88449675407418538), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-413443278704665573473375467436113/562949953421312000000000000000000), (5726046453548644896163702147593/562949953421312000000000000000000), (723559277219524913265924557979/140737488355328000000000000000000), (1094654859867486147174257621023/1125899906842624000000000000000000), (-138477971293974978579614612267/562949953421312000000000000000000), (-28936908996311432950303251569/1125899906842624000000000000000000), (7260679553591267650814138113/1125899906842624000000000000000000), (386172472467698032128991891/1125899906842624000000000000000000), (-106524906211743586962776881/1125899906842624000000000000000000), (-1322740714605147934605537/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial155.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial155.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial155.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 776942049464406284982108559451729), (Int.ofNat 38021039633201849880502965904783), (Int.ofNat 5204377241656495317368258048199), (Int.negOfNat 1091192788685258923641592530737), (Int.negOfNat 140014834726433819785773376739), (Int.ofNat 44983649129579129025158856961), (Int.ofNat 1978705008058274936669218853), (Int.negOfNat 870454282196323904840206275), (Int.negOfNat 11556342385585198932918625), (Int.ofNat 9737460718469365630011862), (Int.negOfNat 20020516581371487709232), (Int.negOfNat 69959181989158939365313), (Int.ofNat 739755575959053441579), (Int.ofNat 348067239445539307544), (Int.negOfNat 5369896656008525393), (Int.negOfNat 1278675970128047597), (Int.ofNat 21972484672681168), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-776942049464406284982108559451729/1125899906842624000000000000000000), (38021039633201849880502965904783/1125899906842624000000000000000000), (5204377241656495317368258048199/1125899906842624000000000000000000), (-1091192788685258923641592530737/1125899906842624000000000000000000), (-140014834726433819785773376739/1125899906842624000000000000000000), (44983649129579129025158856961/1125899906842624000000000000000000), (1978705008058274936669218853/1125899906842624000000000000000000), (-34818171287852956193608251/45035996273704960000000000000000), (-92450739084681591463349/9007199254740992000000000000000), (4868730359234682815005931/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial155.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial155.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial155.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 689595676020025931491919733561657), (Int.ofNat 44862146885413163405479548566161), (Int.negOfNat 1192436550432539260237469754366), (Int.negOfNat 554271050128034273602822974372), (Int.ofNat 208123264933864053677699395771), (Int.ofNat 8013961031015430775804291498), (Int.negOfNat 5946864134531688540133750741), (Int.ofNat 10949424495253080722086638), (Int.ofNat 85996145683335417542506668), (Int.negOfNat 1468632025193153405659892), (Int.negOfNat 756240078724573185644858), (Int.ofNat 18585541486400748938251), (Int.ofNat 4455163314063992254146), (Int.negOfNat 127669043842286385624), (Int.negOfNat 18790561903111396273), (Int.ofNat 595512040877798226), (Int.ofNat 73907888231524470), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-689595676020025931491919733561657/1125899906842624000000000000000000), (44862146885413163405479548566161/1125899906842624000000000000000000), (-596218275216269630118734877183/562949953421312000000000000000000), (-138567762532008568400705743593/281474976710656000000000000000000), (208123264933864053677699395771/1125899906842624000000000000000000), (4006980515507715387902145749/562949953421312000000000000000000), (-5946864134531688540133750741/1125899906842624000000000000000000), (5474712247626540361043319/562949953421312000000000000000000), (21499036420833854385626667/281474976710656000000000000000000), (-367158006298288351414973/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial155.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial155.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial155.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 605847531975404165993592025493057), (Int.ofNat 39686431293992683215684152057665), (Int.negOfNat 162453587277061172186873948289), (Int.ofNat 621737581712986955120071721462), (Int.ofNat 16032748427159372563047073756), (Int.negOfNat 32019383940041770182634657840), (Int.ofNat 807744785659779987440037610), (Int.ofNat 639430392954972026482306178), (Int.negOfNat 24972300393383352027232845), (Int.negOfNat 7070409666114688653909306), (Int.ofNat 315844442674293842481705), (Int.ofNat 49965061468634750366988), (Int.negOfNat 2368437381778817164116), (Int.negOfNat 245214090347187537944), (Int.ofNat 12029858147235552260), (Int.ofNat 868104894526655470), (Int.negOfNat 38313306904341606), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-605847531975404165993592025493057/1125899906842624000000000000000000), (7937286258798536643136830411533/225179981368524800000000000000000), (-162453587277061172186873948289/1125899906842624000000000000000000), (310868790856493477560035860731/562949953421312000000000000000000), (4008187106789843140761768439/281474976710656000000000000000000), (-400242299250522127282933223/14073748835532800000000000000000), (80774478565977998744003761/112589990684262400000000000000000), (319715196477486013241153089/562949953421312000000000000000000), (-4994460078676670405446569/225179981368524800000000000000000), (-3535204833057344326954653/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial155.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial155.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial155.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 522794735330982441577696000790819), (Int.ofNat 44850765345838921170440281294295), (Int.ofNat 1942283741936968408885639651613), (Int.negOfNat 119582843796159334147655436089), (Int.negOfNat 127152813957999901721971122998), (Int.ofNat 9662154920364916850547674398), (Int.ofNat 3828614039912070898375139500), (Int.negOfNat 291776413773377546418101767), (Int.negOfNat 55430100221967839198181584), (Int.ofNat 4239467582967486595052373), (Int.ofNat 478541868618543708991214), (Int.negOfNat 36683445979082810340376), (Int.negOfNat 2755814214416297712383), (Int.ofNat 211847591215165381623), (Int.ofNat 11325069487373544712), (Int.negOfNat 887712276499338197), (Int.negOfNat 45292760984898315), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-522794735330982441577696000790819/1125899906842624000000000000000000), (8970153069167784234088056258859/225179981368524800000000000000000), (1942283741936968408885639651613/1125899906842624000000000000000000), (-119582843796159334147655436089/1125899906842624000000000000000000), (-63576406978999950860985561499/562949953421312000000000000000000), (4831077460182458425273837199/562949953421312000000000000000000), (7657228079824141796750279/2251799813685248000000000000000), (-291776413773377546418101767/1125899906842624000000000000000000), (-3464381263872989949886349/70368744177664000000000000000000), (4239467582967486595052373/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial155.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial155.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial155.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 427809918566141524317536983892040), (Int.ofNat 48448355466422074423094129052398), (Int.negOfNat 406579300120086079104257096299), (Int.negOfNat 372115832673900551608655376803), (Int.ofNat 77119428333786558253718308560), (Int.ofNat 17383830377218586303956918074), (Int.negOfNat 2660091607854384455900452779), (Int.negOfNat 345639903129861482435102511), (Int.ofNat 46877080853663446271268938), (Int.ofNat 3727305359856158930113967), (Int.negOfNat 484210409312270542489396), (Int.negOfNat 25336580962119051250746), (Int.ofNat 3266971803093481413125), (Int.ofNat 118862733866812587493), (Int.negOfNat 15449678549177632986), (Int.negOfNat 390704412555435659), (Int.ofNat 45115753387126659), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-10695247964153538107938424597301/28147497671065600000000000000000), (24224177733211037211547064526199/562949953421312000000000000000000), (-406579300120086079104257096299/1125899906842624000000000000000000), (-372115832673900551608655376803/1125899906842624000000000000000000), (963992854172331978171478857/14073748835532800000000000000000), (8691915188609293151978459037/562949953421312000000000000000000), (-2660091607854384455900452779/1125899906842624000000000000000000), (-345639903129861482435102511/1125899906842624000000000000000000), (23438540426831723135634469/562949953421312000000000000000000), (3727305359856158930113967/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial155.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial155.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial155.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 333927370556833916877880744589846), (Int.ofNat 45603502205897769611947672209191), (Int.negOfNat 173272262094486004358391428087), (Int.ofNat 416944565122426841425955572392), (Int.ofNat 54966753007900005918314711409), (Int.negOfNat 19355973602435700490480437878), (Int.negOfNat 1538802788250117846406058190), (Int.ofNat 431199257622734405814141268), (Int.ofNat 21003822915929002618540267), (Int.negOfNat 5463235104648250303517898), (Int.negOfNat 165932764418759850186543), (Int.ofNat 43929552226828865452482), (Int.ofNat 847511589566695573464), (Int.negOfNat 242751197963446498972), (Int.negOfNat 3068233329698000856), (Int.ofNat 993679961465227170), (Int.ofNat 16677633738272160), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-166963685278416958438940372294923/562949953421312000000000000000000), (45603502205897769611947672209191/1125899906842624000000000000000000), (-173272262094486004358391428087/1125899906842624000000000000000000), (52118070640303355178244446549/140737488355328000000000000000000), (54966753007900005918314711409/1125899906842624000000000000000000), (-9677986801217850245240218939/562949953421312000000000000000000), (-153880278825011784640605819/112589990684262400000000000000000), (107799814405683601453535317/281474976710656000000000000000000), (21003822915929002618540267/1125899906842624000000000000000000), (-2731617552324125151758949/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial155.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial155.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial155.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 239858610331323733799359847951173), (Int.ofNat 50030506951770884323596640418261), (Int.ofNat 2031380556643876998572667316422), (Int.ofNat 85302116317885017912059086104), (Int.negOfNat 109045186858636472583871842628), (Int.negOfNat 3238337372170468897542598881), (Int.ofNat 3268032047237278104648071783), (Int.ofNat 48306587818348054407865416), (Int.negOfNat 52283220216664887808001160), (Int.negOfNat 289084307036143417223382), (Int.ofNat 511334044436874451747608), (Int.negOfNat 90904263398803368001), (Int.negOfNat 3341452249483839600644), (Int.ofNat 12108459847069865518), (Int.ofNat 15560098723899451909), (Int.negOfNat 112968961136600402), (Int.negOfNat 51918199869911712), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-239858610331323733799359847951173/1125899906842624000000000000000000), (50030506951770884323596640418261/1125899906842624000000000000000000), (1015690278321938499286333658211/562949953421312000000000000000000), (10662764539735627239007385763/140737488355328000000000000000000), (-27261296714659118145967960657/281474976710656000000000000000000), (-3238337372170468897542598881/1125899906842624000000000000000000), (3268032047237278104648071783/1125899906842624000000000000000000), (6038323477293506800983177/140737488355328000000000000000000), (-1307080505416622195200029/28147497671065600000000000000000), (-144542153518071708611691/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial155.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial155.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial155.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 132635692196504077968437052815479), (Int.ofNat 56028578308531528785278144639786), (Int.ofNat 394477601970209457313905325234), (Int.negOfNat 454413094569812160136502281273), (Int.ofNat 14921216582855008174082107752), (Int.ofNat 19831288885003411067600162992), (Int.negOfNat 572555225892317643325889389), (Int.negOfNat 416421591397807518290739235), (Int.ofNat 11216812180740383771783679), (Int.ofNat 5069795251406693217396320), (Int.negOfNat 129757117396315407663838), (Int.negOfNat 39860735362475055076045), (Int.ofNat 969576552801161400197), (Int.ofNat 217664117890810445110), (Int.negOfNat 5016104183896558315), (Int.negOfNat 888017592322379883), (Int.ofNat 14204975669282346), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-132635692196504077968437052815479/1125899906842624000000000000000000), (28014289154265764392639072319893/562949953421312000000000000000000), (197238800985104728656952662617/562949953421312000000000000000000), (-454413094569812160136502281273/1125899906842624000000000000000000), (1865152072856876021760263469/140737488355328000000000000000000), (1239455555312713191725010187/70368744177664000000000000000000), (-572555225892317643325889389/1125899906842624000000000000000000), (-83284318279561503658147847/225179981368524800000000000000000), (11216812180740383771783679/1125899906842624000000000000000000), (31686220321291832608727/7036874417766400000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial155.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial155.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial155.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 21847276338081139910873113489704), (Int.ofNat 53943114265995334604781050029024), (Int.negOfNat 763694624904257089086960493758), (Int.ofNat 177249944718976869186162934428), (Int.ofNat 92054507795695735127686424478), (Int.negOfNat 8835483845800534539390441041), (Int.negOfNat 2665273998059229187631941671), (Int.ofNat 203069249013977738870582367), (Int.ofNat 41556602182476685122731597), (Int.negOfNat 2655515495495660664460396), (Int.negOfNat 401149805129188048969442), (Int.ofNat 22138297645622762714917), (Int.ofNat 2612666769018123867479), (Int.negOfNat 126799575264022505596), (Int.negOfNat 12187561861456422393), (Int.ofNat 538128622804405021), (Int.ofNat 37376412694017644), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-2730909542260142488859139186213/140737488355328000000000000000000), (1685722320812354206399407813407/35184372088832000000000000000000), (-381847312452128544543480246879/562949953421312000000000000000000), (44312486179744217296540733607/281474976710656000000000000000000), (46027253897847867563843212239/562949953421312000000000000000000), (-8835483845800534539390441041/1125899906842624000000000000000000), (-2665273998059229187631941671/1125899906842624000000000000000000), (203069249013977738870582367/1125899906842624000000000000000000), (41556602182476685122731597/1125899906842624000000000000000000), (-663878873873915166115099/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial155.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial155.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial155.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 85456648132934638467099924887243), (Int.ofNat 54868170404086872927384366924456), (Int.ofNat 1357458597058227131898362161326), (Int.ofNat 302757678451574826538759912917), (Int.negOfNat 67703413477051153159704152670), (Int.negOfNat 12864836814570731650753612865), (Int.ofNat 2145903896097411740028309533), (Int.ofNat 265387624885117363428918386), (Int.negOfNat 35547663589954913638577076), (Int.negOfNat 3222218812152592753635264), (Int.ofNat 357668761297121736871052), (Int.ofNat 25565921206969451533517), (Int.negOfNat 2396025589714382590486), (Int.negOfNat 141784666443796258508), (Int.ofNat 11349860123273088949), (Int.ofNat 602531425266386224), (Int.negOfNat 37816691488889818), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(85456648132934638467099924887243/1125899906842624000000000000000000), (6858521300510859115923045865557/140737488355328000000000000000000), (678729298529113565949181080663/562949953421312000000000000000000), (302757678451574826538759912917/1125899906842624000000000000000000), (-6770341347705115315970415267/112589990684262400000000000000000), (-2572967362914146330150722573/225179981368524800000000000000000), (2145903896097411740028309533/1125899906842624000000000000000000), (132693812442558681714459193/562949953421312000000000000000000), (-8886915897488728409644269/281474976710656000000000000000000), (-50347168939884261775551/17592186044416000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial155.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial155.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial155.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 201710920688515697277840487485966), (Int.ofNat 61224537384984734207801307396165), (Int.ofNat 1139404158181504223854846479069), (Int.negOfNat 336253848856748484706744868115), (Int.negOfNat 40550013164339962776262481799), (Int.ofNat 16120807532660006970766668853), (Int.ofNat 1131410270157125398278986266), (Int.negOfNat 359639507895305598147244188), (Int.negOfNat 17724589694785597184298827), (Int.ofNat 4563180073850239153958238), (Int.ofNat 177158363638920544086777), (Int.negOfNat 36961522068060461895482), (Int.negOfNat 1213572365957983036888), (Int.ofNat 206075872516457538276), (Int.ofNat 5981593279088867162), (Int.negOfNat 837884058421343692), (Int.negOfNat 11028767608319840), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(100855460344257848638920243742983/562949953421312000000000000000000), (12244907476996946841560261479233/225179981368524800000000000000000), (1139404158181504223854846479069/1125899906842624000000000000000000), (-67250769771349696941348973623/225179981368524800000000000000000), (-40550013164339962776262481799/1125899906842624000000000000000000), (16120807532660006970766668853/1125899906842624000000000000000000), (565705135078562699139493133/562949953421312000000000000000000), (-89909876973826399536811047/281474976710656000000000000000000), (-17724589694785597184298827/1125899906842624000000000000000000), (2281590036925119576979119/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial155.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial155.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial155.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 325918924684813104073673952498762), (Int.ofNat 61788120212420029685628814799436), (Int.negOfNat 541576846087781916168750278443), (Int.negOfNat 42338544994801478788912134318), (Int.ofNat 87135925972368513161941977810), (Int.ofNat 1030806814239795054481785934), (Int.negOfNat 2797577496060599861929774729), (Int.negOfNat 18165997537094614994954489), (Int.ofNat 46810767161811675132544866), (Int.ofNat 296805649884253824277467), (Int.negOfNat 473853779723650433118994), (Int.negOfNat 3536595128384993774428), (Int.ofNat 3179660168374650767029), (Int.ofNat 27430190108628872307), (Int.negOfNat 15072001695481079890), (Int.negOfNat 152367224070883785), (Int.ofNat 44619137971674871), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(162959462342406552036836976249381/562949953421312000000000000000000), (15447030053105007421407203699859/281474976710656000000000000000000), (-541576846087781916168750278443/1125899906842624000000000000000000), (-21169272497400739394456067159/562949953421312000000000000000000), (8713592597236851316194197781/112589990684262400000000000000000), (515403407119897527240892967/562949953421312000000000000000000), (-2797577496060599861929774729/1125899906842624000000000000000000), (-18165997537094614994954489/1125899906842624000000000000000000), (23405383580905837566272433/562949953421312000000000000000000), (296805649884253824277467/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial155.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial155.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial155.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 448247595844473472790722133063248), (Int.ofNat 61485521189792930968008467159307), (Int.ofNat 774400346976913842046834917749), (Int.ofNat 316603478260478207218116301528), (Int.negOfNat 27992788023778805874176322548), (Int.negOfNat 16106216891903734462834327650), (Int.ofNat 928481337119137306884013175), (Int.ofNat 377033551692357332932712207), (Int.negOfNat 14333428310839596970682548), (Int.negOfNat 4981818102136367794832173), (Int.ofNat 122341011527150758362132), (Int.ofNat 41564925361098912687036), (Int.negOfNat 636953823700155296777), (Int.negOfNat 236024446861987511237), (Int.ofNat 2137969306779499596), (Int.ofNat 967734518192003223), (Int.negOfNat 17586359638306315), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(28015474740279592049420133316453/70368744177664000000000000000000), (61485521189792930968008467159307/1125899906842624000000000000000000), (774400346976913842046834917749/1125899906842624000000000000000000), (39575434782559775902264537691/140737488355328000000000000000000), (-6998197005944701468544080637/281474976710656000000000000000000), (-322124337838074689256686553/22517998136852480000000000000000), (37139253484765492275360527/45035996273704960000000000000000), (377033551692357332932712207/1125899906842624000000000000000000), (-3583357077709899242670637/281474976710656000000000000000000), (-4981818102136367794832173/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial155.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial155.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial155.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 575987452866149658965856980770147), (Int.ofNat 66520188483921214118412262466519), (Int.ofNat 1143757985481111477691075086019), (Int.negOfNat 240862132397902720984198267847), (Int.negOfNat 60679173201390647084698452122), (Int.ofNat 12319910363524281650901834895), (Int.ofNat 2193880595093307845681697354), (Int.negOfNat 272393557385032810823533530), (Int.negOfNat 40729562916220819589631917), (Int.ofNat 3209713419366807490136274), (Int.ofNat 446196715224441389138563), (Int.negOfNat 22900008570325567647670), (Int.negOfNat 3154665439449841789836), (Int.ofNat 108396503763973579096), (Int.ofNat 15447445531965629334), (Int.negOfNat 362223371840936444), (Int.negOfNat 51421584454459924), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(575987452866149658965856980770147/1125899906842624000000000000000000), (66520188483921214118412262466519/1125899906842624000000000000000000), (1143757985481111477691075086019/1125899906842624000000000000000000), (-240862132397902720984198267847/1125899906842624000000000000000000), (-30339586600695323542349226061/562949953421312000000000000000000), (2463982072704856330180366979/225179981368524800000000000000000), (1096940297546653922840848677/562949953421312000000000000000000), (-27239355738503281082353353/112589990684262400000000000000000), (-40729562916220819589631917/1125899906842624000000000000000000), (1604856709683403745068137/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial155.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial155.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial155.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 711196491875258969498868270741315), (Int.ofNat 67515571469229897407498369789565), (Int.negOfNat 482531511469298475241299646521), (Int.negOfNat 85177279695819912055618591200), (Int.ofNat 89890950200263266346928581509), (Int.ofNat 6640524101990562068742065004), (Int.negOfNat 3015980334951668212830792751), (Int.negOfNat 216596752118675991996458836), (Int.ofNat 49112350062592313435845394), (Int.ofNat 3583164115298370618592552), (Int.negOfNat 454942456221290921643734), (Int.negOfNat 34293462206235891879591), (Int.ofNat 2680061100758451899500), (Int.ofNat 209906854558129629902), (Int.negOfNat 10968008719244882231), (Int.negOfNat 902282498663298352), (Int.ofNat 46201486884932470), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(142239298375051793899773654148263/225179981368524800000000000000000), (13503114293845979481499673957913/225179981368524800000000000000000), (-482531511469298475241299646521/1125899906842624000000000000000000), (-106471599619774890069523239/1407374883553280000000000000000), (89890950200263266346928581509/1125899906842624000000000000000000), (1660131025497640517185516251/281474976710656000000000000000000), (-3015980334951668212830792751/1125899906842624000000000000000000), (-54149188029668997999114709/281474976710656000000000000000000), (24556175031296156717922697/562949953421312000000000000000000), (447895514412296327324069/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial155.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial155.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial155.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 845059979116013261949876926849043), (Int.ofNat 67350873480299411446070197486019), (Int.ofNat 924165018911088933703950421823), (Int.ofNat 394909867098421587023611571384), (Int.negOfNat 23016569150467608618089911599), (Int.negOfNat 22874826567088371780436349112), (Int.ofNat 18721666328126030508143722), (Int.ofNat 552281861625426156877219601), (Int.ofNat 13614819513041555879331563), (Int.negOfNat 6868644407492151485352382), (Int.negOfNat 260581510590034426595614), (Int.ofNat 50452827698124126990851), (Int.ofNat 2282834042504466430847), (Int.negOfNat 247600672658030171250), (Int.negOfNat 12350229325007453137), (Int.ofNat 900683847820063029), (Int.ofNat 48685655188369592), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(845059979116013261949876926849043/1125899906842624000000000000000000), (67350873480299411446070197486019/1125899906842624000000000000000000), (924165018911088933703950421823/1125899906842624000000000000000000), (49363733387302698377951446423/140737488355328000000000000000000), (-23016569150467608618089911599/1125899906842624000000000000000000), (-2859353320886046472554543639/140737488355328000000000000000000), (9360833164063015254071861/562949953421312000000000000000000), (552281861625426156877219601/1125899906842624000000000000000000), (13614819513041555879331563/1125899906842624000000000000000000), (-3434322203746075742676191/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial155.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial155.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial155.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 985589108088461605314738720003254), (Int.ofNat 73468344538840496874658096765254), (Int.ofNat 1278143909795050383190141906210), (Int.negOfNat 406164667252144463975303553802), (Int.negOfNat 109630723276796636513780705303), (Int.ofNat 15524488912191408212956694291), (Int.ofNat 4603847545115541308212623471), (Int.negOfNat 175812928985731122552685997), (Int.negOfNat 83968038538058779621181967), (Int.negOfNat 251713870764707279323720), (Int.ofNat 789643949727312632586976), (Int.ofNat 15550419067622719552309), (Int.negOfNat 4668935800698111650051), (Int.negOfNat 130703509459347136736), (Int.ofNat 19292559214318579041), (Int.ofNat 642451646623264461), (Int.negOfNat 69813202704539942), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(492794554044230802657369360001627/562949953421312000000000000000000), (36734172269420248437329048382627/562949953421312000000000000000000), (127814390979505038319014190621/112589990684262400000000000000000), (-203082333626072231987651776901/562949953421312000000000000000000), (-109630723276796636513780705303/1125899906842624000000000000000000), (15524488912191408212956694291/1125899906842624000000000000000000), (4603847545115541308212623471/1125899906842624000000000000000000), (-175812928985731122552685997/1125899906842624000000000000000000), (-83968038538058779621181967/1125899906842624000000000000000000), (-6292846769117681983093/28147497671065600000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial155.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial155.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial155.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 1133383085613253481420508474664264), (Int.ofNat 72163430224914411224386928523486), (Int.negOfNat 1703670047222733547252560942872), (Int.negOfNat 163657583401358704696064591566), (Int.ofNat 188209559610132605918410928867), (Int.ofNat 24209529017284984901649068039), (Int.negOfNat 4836857146059445102274454909), (Int.negOfNat 838910186542194757439523494), (Int.ofNat 35825372067851080629747840), (Int.ofNat 10594781504912616883208620), (Int.negOfNat 63460720273467216454778), (Int.negOfNat 76539384612563666574995), (Int.negOfNat 696771067208118895510), (Int.ofNat 372391589583813102812), (Int.ofNat 6254507050446113597), (Int.negOfNat 1360963529387538610), (Int.negOfNat 34143868012475524), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(141672885701656685177563559333033/140737488355328000000000000000000), (36081715112457205612193464261743/562949953421312000000000000000000), (-212958755902841693406570117859/140737488355328000000000000000000), (-81828791700679352348032295783/562949953421312000000000000000000), (188209559610132605918410928867/1125899906842624000000000000000000), (24209529017284984901649068039/1125899906842624000000000000000000), (-4836857146059445102274454909/1125899906842624000000000000000000), (-419455093271097378719761747/562949953421312000000000000000000), (55977143856017313483981/1759218604441600000000000000000), (529739075245630844160431/56294995342131200000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial155.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial155.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial155.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 1272969498068051059333176586487380), (Int.ofNat 70099730505192298155241880950689), (Int.ofNat 2153729770349797196402821200647), (Int.ofNat 1183694669985105814178478078001), (Int.negOfNat 15994254337081792640825331099), (Int.negOfNat 69613052277790092919603721748), (Int.negOfNat 6752423584727114142413612692), (Int.ofNat 818586665706196559813881074), (Int.ofNat 123951569988588257548652973), (Int.negOfNat 4522867035567878861540404), (Int.negOfNat 1111767882919688111314583), (Int.ofNat 11254471333116185849262), (Int.ofNat 6382056561151373912908), (Int.ofNat 12485099092930653556), (Int.negOfNat 26159636877814819944), (Int.negOfNat 231880571021872334), (Int.ofNat 86154024936200380), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(63648474903402552966658829324369/56294995342131200000000000000000), (70099730505192298155241880950689/1125899906842624000000000000000000), (2153729770349797196402821200647/1125899906842624000000000000000000), (1183694669985105814178478078001/1125899906842624000000000000000000), (-15994254337081792640825331099/1125899906842624000000000000000000), (-17403263069447523229900930437/281474976710656000000000000000000), (-1688105896181778535603403173/281474976710656000000000000000000), (409293332853098279906940537/562949953421312000000000000000000), (123951569988588257548652973/1125899906842624000000000000000000), (-1130716758891969715385101/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial155.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial155.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial155.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 1428470860067767826345226208039376), (Int.ofNat 86019481550127027951992378278282), (Int.ofNat 2421712848494434592260973972229), (Int.negOfNat 2168852740844474465344458130309), (Int.negOfNat 781156591282175250669208904834), (Int.negOfNat 43476773226550280165781933785), (Int.ofNat 12342037522392198217514944433), (Int.ofNat 1294413085366457885680280679), (Int.negOfNat 96591259655515447596880814), (Int.negOfNat 14530446078681163049393699), (Int.ofNat 451628386491385911100208), (Int.ofNat 98754366674321594160700), (Int.negOfNat 1285887790932594177497), (Int.negOfNat 466004492319993653103), (Int.ofNat 1762246229736741988), (Int.ofNat 1653163765009078581), (Int.ofNat 5528740765849369), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(89279428754235489146576638002461/70368744177664000000000000000000), (43009740775063513975996189139141/562949953421312000000000000000000), (2421712848494434592260973972229/1125899906842624000000000000000000), (-2168852740844474465344458130309/1125899906842624000000000000000000), (-390578295641087625334604452417/562949953421312000000000000000000), (-8695354645310056033156386757/225179981368524800000000000000000), (12342037522392198217514944433/1125899906842624000000000000000000), (1294413085366457885680280679/1125899906842624000000000000000000), (-48295629827757723798440407/562949953421312000000000000000000), (-14530446078681163049393699/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial155.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial155.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial155.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 1579880154470946180165737516471684), (Int.ofNat 44025496834400750612677363434697), (Int.negOfNat 29217592498443819599027681336058), (Int.negOfNat 7697954889625145280156077480917), (Int.negOfNat 269821351651575903515902365236), (Int.ofNat 147076851906477911768535932338), (Int.ofNat 12685640125849508242646846745), (Int.negOfNat 1468824294705591170753438545), (Int.negOfNat 174230212731665272617045200), (Int.ofNat 9245993970072365135979783), (Int.ofNat 1394098306972251595936910), (Int.negOfNat 39770603594613057492412), (Int.negOfNat 7585401544613799085253), (Int.ofNat 122168500660964058851), (Int.ofNat 30237414849072854782), (Int.negOfNat 245519910949347477), (Int.negOfNat 92956471418985433), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(394970038617736545041434379117921/281474976710656000000000000000000), (44025496834400750612677363434697/1125899906842624000000000000000000), (-14608796249221909799513840668029/562949953421312000000000000000000), (-7697954889625145280156077480917/1125899906842624000000000000000000), (-67455337912893975878975591309/281474976710656000000000000000000), (73538425953238955884267966169/562949953421312000000000000000000), (2537128025169901648529369349/225179981368524800000000000000000), (-293764858941118234150687709/225179981368524800000000000000000), (-435575531829163181542613/2814749767106560000000000000000), (9245993970072365135979783/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial155.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial155.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial155.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 1490451775654368277404448630251570), (Int.negOfNat 160461453036110171303819052440781), (Int.negOfNat 68312539627859281182437218880171), (Int.negOfNat 3009868476856336420596804528322), (Int.ofNat 1409126606639404024099311074661), (Int.ofNat 125874770944344453115667848141), (Int.negOfNat 17482101702347372134538421588), (Int.negOfNat 1963255193374815091336262998), (Int.ofNat 140888854009970923805690941), (Int.ofNat 18147739190995394117909578), (Int.negOfNat 789794707615731781809393), (Int.negOfNat 113333172238626968316700), (Int.ofNat 3246861000028738874864), (Int.ofNat 512930279865492347600), (Int.negOfNat 10164480557282443316), (Int.negOfNat 1759131449974967554), (Int.ofNat 23086386480776786), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(149045177565436827740444863025157/112589990684262400000000000000000), (-160461453036110171303819052440781/1125899906842624000000000000000000), (-68312539627859281182437218880171/1125899906842624000000000000000000), (-1504934238428168210298402264161/562949953421312000000000000000000), (1409126606639404024099311074661/1125899906842624000000000000000000), (125874770944344453115667848141/1125899906842624000000000000000000), (-4370525425586843033634605397/281474976710656000000000000000000), (-981627596687407545668131499/562949953421312000000000000000000), (140888854009970923805690941/1125899906842624000000000000000000), (9073869595497697058954789/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial155.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial155.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial155.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 897447966071015084693160655652734), (Int.negOfNat 418723234262288024024213828411080), (Int.negOfNat 47673638296689906970503122923044), (Int.ofNat 9735197923146381826671826852611), (Int.ofNat 1285386078215535395598778718259), (Int.negOfNat 158357125155863253202263701060), (Int.negOfNat 21029412809434700527893981895), (Int.ofNat 1679123443982099354089589520), (Int.ofNat 219355535586728000322829774), (Int.negOfNat 12151591110396234863403304), (Int.negOfNat 1561135002556709715178560), (Int.ofNat 63361950034863728200871), (Int.ofNat 8012363536777619431992), (Int.negOfNat 248703399421100691282), (Int.negOfNat 31001607768128837057), (Int.ofNat 749193284641383538), (Int.ofNat 99758917901770486), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(448723983035507542346580327826367/562949953421312000000000000000000), (-10468080856557200600605345710277/28147497671065600000000000000000), (-11918409574172476742625780730761/281474976710656000000000000000000), (9735197923146381826671826852611/1125899906842624000000000000000000), (1285386078215535395598778718259/1125899906842624000000000000000000), (-7917856257793162660113185053/56294995342131200000000000000000), (-4205882561886940105578796379/225179981368524800000000000000000), (20989043049776241926119869/14073748835532800000000000000000), (109677767793364000161414887/562949953421312000000000000000000), (-1518948888799529357925413/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial155.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial155.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial155.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 38395182756721990679558044119034), (Int.negOfNat 467227503982311942899315115645513), (Int.ofNat 25320938645486554566488009040453), (Int.ofNat 11566868588028141491599215820014), (Int.negOfNat 910522308718005477338894543187), (Int.negOfNat 205903840858599311390145498497), (Int.ofNat 14969640403345934973037703934), (Int.ofNat 2438745537603020870677904947), (Int.negOfNat 148572715151384035089293707), (Int.negOfNat 19797816558346256404034416), (Int.ofNat 997222948535481778800126), (Int.ofNat 115272476890852215438263), (Int.negOfNat 4839188535639650937173), (Int.negOfNat 500819141291459477182), (Int.ofNat 17840862963811260555), (Int.ofNat 1653469080832120267), (Int.negOfNat 53968995888331292), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-19197591378360995339779022059517/562949953421312000000000000000000), (-467227503982311942899315115645513/1125899906842624000000000000000000), (25320938645486554566488009040453/1125899906842624000000000000000000), (5783434294014070745799607910007/562949953421312000000000000000000), (-910522308718005477338894543187/1125899906842624000000000000000000), (-205903840858599311390145498497/1125899906842624000000000000000000), (7484820201672967486518851967/562949953421312000000000000000000), (2438745537603020870677904947/1125899906842624000000000000000000), (-148572715151384035089293707/1125899906842624000000000000000000), (-1237363534896641025252151/70368744177664000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial155.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial155.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial155.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial155.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial155.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial155.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial155.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial155.reflect := by
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

end Bin155
end
end ErdosOverlap.OuterNumerics
