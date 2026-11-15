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

/-! # Exact integer weighted outer models for source bin 131

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin131

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 4044555271938693500)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 3239701066769759000)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 2382074719591100200)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 1637457450123035200)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 1125657835211751500)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 649631471898439700)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 330893701146030560)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 90577709015687070)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial131.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial131.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9504960455340187000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1341102139455308000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1695307020362774000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 282242799071990570)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 130671730908441030)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 19248181024035802)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 92223334225013500)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 43670671631627320)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 7224695039227059)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial131.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial131.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9504960455340187000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1341102139455308000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1695307020362774000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 282242799071990570)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 130671730908441030)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 19248181024035802)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 92223334225013500)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 43670671631627320)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 7224695039227059)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial131.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial131.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial131.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 12043631809251966367526068908589551), (Int.ofNat 4255458848967269120770855895053221), (Int.ofNat 1003888874493211825578647630641456), (Int.negOfNat 121294251951382170537588258163727), (Int.negOfNat 24482778513289184426695541175441), (Int.ofNat 2233708452962395665867436198363), (Int.ofNat 333974689782807435391508847021), (Int.negOfNat 26049039172006071634633026225), (Int.negOfNat 2934236923261582061445239526), (Int.ofNat 205329217777356793096872986), (Int.ofNat 17971863718007268207041073), (Int.negOfNat 1158234789928467171053988), (Int.negOfNat 81106207580890418014981), (Int.ofNat 4885764929085486300133), (Int.ofNat 281860386402648944833), (Int.negOfNat 15744565563543059535), (Int.negOfNat 784104747620730876), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-12043631809251966367526068908589551/11258999068426240000000000000000000), (4255458848967269120770855895053221/11258999068426240000000000000000000), (62743054655825739098665476915091/703687441776640000000000000000000), (-121294251951382170537588258163727/11258999068426240000000000000000000), (-24482778513289184426695541175441/11258999068426240000000000000000000), (2233708452962395665867436198363/11258999068426240000000000000000000), (333974689782807435391508847021/11258999068426240000000000000000000), (-1041961566880242865385321049/450359962737049600000000000000000), (-1467118461630791030722619763/5629499534213120000000000000000000), (102664608888678396548436493/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial131.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial131.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial131.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial131 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.negOfNat 790348604648461163327722889756179), (Int.ofNat 6260729942643527290183054021045452), (Int.negOfNat 74259860693132787777373463193489), (Int.negOfNat 192894360009909737814862427330395), (Int.ofNat 8324966384046371454793677118781), (Int.ofNat 3256990590749509891498270413904), (Int.negOfNat 181655939514261685863923346171), (Int.negOfNat 33717210021149888897697343075), (Int.ofNat 2065551658816551026027936045), (Int.ofNat 235164420010445580330485057), (Int.negOfNat 15051354386756105028055814), (Int.negOfNat 1180355186584412215614699), (Int.ofNat 77282856073969271334159), (Int.ofNat 4471995522619766306303), (Int.negOfNat 296628648260640309808), (Int.negOfNat 12880804672683124069), (Int.ofNat 950165772781120966), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-790348604648461163327722889756179/11258999068426240000000000000000000), (1565182485660881822545763505261363/2814749767106560000000000000000000), (-74259860693132787777373463193489/11258999068426240000000000000000000), (-38578872001981947562972485466079/2251799813685248000000000000000000), (8324966384046371454793677118781/11258999068426240000000000000000000), (203561911921844368218641900869/703687441776640000000000000000000), (-181655939514261685863923346171/11258999068426240000000000000000000), (-1348688400845995555907893723/450359962737049600000000000000000), (413110331763310205205587209/2251799813685248000000000000000000), (235164420010445580330485057/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial131.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial131.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial131.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial131 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 10113030039236743497214767572933326), (Int.ofNat 4128501786795019227144715334269919), (Int.negOfNat 832938677520518773357940580879718), (Int.negOfNat 39267153973886778566269402462967), (Int.ofNat 23575246500917972965296593908372), (Int.negOfNat 502970195423708655666692179638), (Int.negOfNat 327048731180970003390390665746), (Int.ofNat 14817278351778314773346508783), (Int.ofNat 2762838030604530668685988760), (Int.negOfNat 160143913304735635648866599), (Int.negOfNat 15895215827541609985990810), (Int.ofNat 1056859499615396683671637), (Int.ofNat 66688296364958590624950), (Int.negOfNat 4875521702788005833686), (Int.negOfNat 213419296655308137191), (Int.ofNat 16934817511007338371), (Int.ofNat 505146925534442607), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(5056515019618371748607383786466663/5629499534213120000000000000000000), (4128501786795019227144715334269919/11258999068426240000000000000000000), (-416469338760259386678970290439859/5629499534213120000000000000000000), (-39267153973886778566269402462967/11258999068426240000000000000000000), (5893811625229493241324148477093/2814749767106560000000000000000000), (-251485097711854327833346089819/5629499534213120000000000000000000), (-163524365590485001695195332873/5629499534213120000000000000000000), (14817278351778314773346508783/11258999068426240000000000000000000), (69070950765113266717149719/281474976710656000000000000000000), (-160143913304735635648866599/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial131.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial131.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial131.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial131 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 15066827472438935603389057134382019), (Int.ofNat 985948340415269468081469992059450), (Int.negOfNat 607444410727494263779719165794920), (Int.ofNat 89082410114249818890580974393894), (Int.ofNat 5357643714650770437123681492873), (Int.negOfNat 2359941792130672868665672246162), (Int.ofNat 47185633176131006167114272607), (Int.ofNat 27373418155242807136602902452), (Int.negOfNat 1284531153921799691277112174), (Int.negOfNat 191765475608797621761865128), (Int.ofNat 12154561632297808871919143), (Int.ofNat 918193473284131841573601), (Int.negOfNat 70519558372704024740804), (Int.negOfNat 3220043397497030935302), (Int.ofNat 288543656573967770242), (Int.ofNat 8151325462085351184), (Int.negOfNat 928491687663439789), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(15066827472438935603389057134382019/11258999068426240000000000000000000), (19718966808305389361629399841189/225179981368524800000000000000000), (-15186110268187356594492979144873/281474976710656000000000000000000), (44541205057124909445290487196947/5629499534213120000000000000000000), (5357643714650770437123681492873/11258999068426240000000000000000000), (-1179970896065336434332836123081/5629499534213120000000000000000000), (47185633176131006167114272607/11258999068426240000000000000000000), (6843354538810701784150725613/2814749767106560000000000000000000), (-642265576960899845638556087/5629499534213120000000000000000000), (-23970684451099702720233141/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial131.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial131.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial131.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial131 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 15337920623972192013421474064642209), (Int.negOfNat 372554676142741668698843187174218), (Int.negOfNat 106467180553817293785861270057771), (Int.ofNat 57308712175041558572077304484188), (Int.negOfNat 9765612096219159233249548913996), (Int.negOfNat 339148053762921579044649667003), (Int.ofNat 207452678589792801179420243010), (Int.negOfNat 6282027761839961370632453464), (Int.negOfNat 1968025751363240084271369862), (Int.ofNat 112285804172263009062359380), (Int.ofNat 11348562641733305049275029), (Int.negOfNat 879402511543080671685377), (Int.negOfNat 44649781619315126719811), (Int.ofNat 4404460056034311099659), (Int.ofNat 126789352694643722888), (Int.negOfNat 16362390442147526953), (Int.negOfNat 233413798487381397), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(15337920623972192013421474064642209/11258999068426240000000000000000000), (-186277338071370834349421593587109/5629499534213120000000000000000000), (-106467180553817293785861270057771/11258999068426240000000000000000000), (14327178043760389643019326121047/2814749767106560000000000000000000), (-2441403024054789808312387228499/2814749767106560000000000000000000), (-339148053762921579044649667003/11258999068426240000000000000000000), (20745267858979280117942024301/1125899906842624000000000000000000), (-785253470229995171329056683/1407374883553280000000000000000000), (-984012875681620042135684931/5629499534213120000000000000000000), (5614290208613150453117969/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial131.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial131.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial131.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial131 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 14470345937875909373281546452400993), (Int.negOfNat 415042922862502895963037354823502), (Int.ofNat 18540079643038605068531611650126), (Int.negOfNat 7497174601878496242943852901943), (Int.negOfNat 4108934464135790685870288300039), (Int.ofNat 1029803874533529302824062301499), (Int.negOfNat 1945502191324643249458158835), (Int.negOfNat 15968807600423564329032670120), (Int.ofNat 773834816061158457429023911), (Int.ofNat 120531092840723480981955714), (Int.negOfNat 9226771487586644052381219), (Int.negOfNat 556492064606253323059731), (Int.ofNat 59047477191093959494658), (Int.ofNat 1705712029787571132800), (Int.negOfNat 254130555331396957129), (Int.negOfNat 3385184734240745339), (Int.ofNat 906817602545758612), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(14470345937875909373281546452400993/11258999068426240000000000000000000), (-207521461431251447981518677411751/5629499534213120000000000000000000), (9270039821519302534265805825063/5629499534213120000000000000000000), (-7497174601878496242943852901943/11258999068426240000000000000000000), (-4108934464135790685870288300039/11258999068426240000000000000000000), (1029803874533529302824062301499/11258999068426240000000000000000000), (-389100438264928649891631767/2251799813685248000000000000000000), (-399220190010589108225816753/281474976710656000000000000000000), (773834816061158457429023911/11258999068426240000000000000000000), (60265546420361740490977857/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial131.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial131.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial131.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial131 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 13619734744282344381484391058319412), (Int.negOfNat 486459741146876065777362193038133), (Int.negOfNat 52046721361807820431930509541200), (Int.negOfNat 6553891888470773130525205047508), (Int.ofNat 2814112960273977486090421888492), (Int.ofNat 170171540721664050681670641906), (Int.negOfNat 93402827713951290913622276565), (Int.ofNat 3544153970674268733509240136), (Int.ofNat 1036810595197860753058797681), (Int.negOfNat 79237121541231559051009554), (Int.negOfNat 5982218223623202987963148), (Int.ofNat 684735012750048798785130), (Int.ofNat 20243185732299948108199), (Int.negOfNat 3613553937219877187903), (Int.negOfNat 36094012596197711097), (Int.ofNat 13992858583052428253), (Int.negOfNat 38319328559679813), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(3404933686070586095371097764579853/2814749767106560000000000000000000), (-486459741146876065777362193038133/11258999068426240000000000000000000), (-130116803404519551079826273853/28147497671065600000000000000000), (-1638472972117693282631301261877/2814749767106560000000000000000000), (703528240068494371522605472123/2814749767106560000000000000000000), (85085770360832025340835320953/5629499534213120000000000000000000), (-18680565542790258182724455313/2251799813685248000000000000000000), (443019246334283591688655017/1407374883553280000000000000000000), (1036810595197860753058797681/11258999068426240000000000000000000), (-39618560770615779525504777/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial131.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial131.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial131.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial131 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 12431364592627945192906944008060094), (Int.negOfNat 685117033507111061100297635050479), (Int.negOfNat 28808650220453469707743189505845), (Int.ofNat 11176388264027330566187765135593), (Int.ofNat 695529001437822189822063642282), (Int.negOfNat 375334734814425097016094349754), (Int.ofNat 9522009269842757162239597243), (Int.ofNat 6716739824853148006332361481), (Int.negOfNat 547422714232592603766646925), (Int.negOfNat 52251011999764604772445523), (Int.ofNat 6765723938363242226732915), (Int.ofNat 200650508516618088142353), (Int.negOfNat 45081292944071332250890), (Int.negOfNat 258589751544333307251), (Int.ofNat 197784386620723734096), (Int.negOfNat 1342627310623636606), (Int.negOfNat 794565808412390365), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(6215682296313972596453472004030047/5629499534213120000000000000000000), (-685117033507111061100297635050479/11258999068426240000000000000000000), (-5761730044090693941548637901169/2251799813685248000000000000000000), (11176388264027330566187765135593/11258999068426240000000000000000000), (347764500718911094911031821141/5629499534213120000000000000000000), (-187667367407212548508047174877/5629499534213120000000000000000000), (9522009269842757162239597243/11258999068426240000000000000000000), (6716739824853148006332361481/11258999068426240000000000000000000), (-21896908569303704150665877/450359962737049600000000000000000), (-52251011999764604772445523/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial131.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial131.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial131.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial131 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 11035734197350458705433970320311141), (Int.negOfNat 669812646796294364199041620395623), (Int.ofNat 30573349095172646407224370979078), (Int.ofNat 5857630256997131079892828942079), (Int.negOfNat 1335804734185668073813088797027), (Int.ofNat 8583151116668373344965263849), (Int.ofNat 30253764221190435032771409543), (Int.negOfNat 3100680532246730178698279753), (Int.negOfNat 337657266790575477814999385), (Int.ofNat 56408010913433399190033867), (Int.ofNat 1463665699331639387791131), (Int.negOfNat 486748552120073732460449), (Int.ofNat 750249943689452952366), (Int.ofNat 2603031665309763724711), (Int.negOfNat 39164788657969156820), (Int.negOfNat 10059595842237332254), (Int.ofNat 205025356512599835), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(11035734197350458705433970320311141/11258999068426240000000000000000000), (-669812646796294364199041620395623/11258999068426240000000000000000000), (15286674547586323203612185489539/5629499534213120000000000000000000), (5857630256997131079892828942079/11258999068426240000000000000000000), (-1335804734185668073813088797027/11258999068426240000000000000000000), (8583151116668373344965263849/11258999068426240000000000000000000), (30253764221190435032771409543/11258999068426240000000000000000000), (-3100680532246730178698279753/11258999068426240000000000000000000), (-67531453358115095562999877/2251799813685248000000000000000000), (56408010913433399190033867/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial131.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial131.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial131.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial131 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 9845647447116028319922214390147134), (Int.negOfNat 515080804307034035239230396044405), (Int.ofNat 39182160276742255356998173961625), (Int.negOfNat 1680370094211924412561526998954), (Int.negOfNat 453582470672004998829451357210), (Int.ofNat 71896606621333132180154397584), (Int.negOfNat 14781619012007369971821940861), (Int.negOfNat 1271786466993684805200479012), (Int.ofNat 397326641047806190437748237), (Int.ofNat 4558440146605550717889026), (Int.negOfNat 4478576798394180989253752), (Int.ofNat 66031150292223973522578), (Int.ofNat 29460344438595240405091), (Int.negOfNat 832627868231931410701), (Int.negOfNat 129568535155165226569), (Int.ofNat 4867911726672140767), (Int.ofNat 598961000302562107), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(4922823723558014159961107195073567/5629499534213120000000000000000000), (-103016160861406807047846079208881/2251799813685248000000000000000000), (313457282213938042855985391693/90071992547409920000000000000000), (-840185047105962206280763499477/5629499534213120000000000000000000), (-45358247067200499882945135721/1125899906842624000000000000000000), (4493537913833320761259649849/703687441776640000000000000000000), (-14781619012007369971821940861/11258999068426240000000000000000000), (-317946616748421201300119753/2814749767106560000000000000000000), (397326641047806190437748237/11258999068426240000000000000000000), (2279220073302775358944513/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial131.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial131.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial131.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial131 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 8952805789058996200094407248847893), (Int.negOfNat 390291501342628642219349958753914), (Int.ofNat 20248555091955459869267015141231), (Int.negOfNat 4836923224067414867133081236944), (Int.negOfNat 568320171463362055692692672309), (Int.negOfNat 56686852798410431649592253101), (Int.ofNat 2379770078145432203788043593), (Int.ofNat 2398992319237726660545028856), (Int.negOfNat 60531148522846548703280641), (Int.negOfNat 34487798567639696369110134), (Int.ofNat 1382361516163077324127529), (Int.ofNat 279871393358975507662095), (Int.negOfNat 14392259054756450456122), (Int.negOfNat 1460524016912538952848), (Int.ofNat 88555965055512869163), (Int.ofNat 5154995713861624359), (Int.negOfNat 273928980410605728), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(8952805789058996200094407248847893/11258999068426240000000000000000000), (-195145750671314321109674979376957/5629499534213120000000000000000000), (20248555091955459869267015141231/11258999068426240000000000000000000), (-302307701504213429195817577309/703687441776640000000000000000000), (-568320171463362055692692672309/11258999068426240000000000000000000), (-56686852798410431649592253101/11258999068426240000000000000000000), (2379770078145432203788043593/11258999068426240000000000000000000), (299874039904715832568128607/1407374883553280000000000000000000), (-60531148522846548703280641/11258999068426240000000000000000000), (-17243899283819848184555067/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial131.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial131.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial131.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial131 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 8204042660860360460687168918266718), (Int.negOfNat 388661522990307176777051831572232), (Int.negOfNat 25009104310106694964762934334581), (Int.negOfNat 10189559015291665671793071179256), (Int.negOfNat 499390773265054441126193401367), (Int.ofNat 94325045106174502506162209006), (Int.ofNat 13698367405322674112740149464), (Int.negOfNat 1211274519675894722895808072), (Int.negOfNat 217308612633554807158334042), (Int.ofNat 19419364473251959130903332), (Int.ofNat 2106372318068188808156517), (Int.negOfNat 206411053835778017098967), (Int.negOfNat 12955582608448808515175), (Int.ofNat 1397996709720913251429), (Int.ofNat 53511207222008173276), (Int.negOfNat 6514974081844533567), (Int.negOfNat 327227873255500897), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(4102021330430180230343584459133359/5629499534213120000000000000000000), (-48582690373788397097131478946529/1407374883553280000000000000000000), (-25009104310106694964762934334581/11258999068426240000000000000000000), (-1273694876911458208974133897407/1407374883553280000000000000000000), (-499390773265054441126193401367/11258999068426240000000000000000000), (47162522553087251253081104503/5629499534213120000000000000000000), (1712295925665334264092518683/1407374883553280000000000000000000), (-151409314959486840361976009/1407374883553280000000000000000000), (-108654306316777403579167021/5629499534213120000000000000000000), (4854841118312989782725833/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial131.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial131.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial131.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial131 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 7240872531937678971518049345787239), (Int.negOfNat 617489275488822444582778906542398), (Int.negOfNat 88394318992965583230422045487795), (Int.negOfNat 9160663439885247776750955654774), (Int.ofNat 780016124434671603121342074389), (Int.ofNat 108818548967788534501473302958), (Int.negOfNat 10956946614014532276013763088), (Int.negOfNat 1121644692753820623561881036), (Int.ofNat 198741747449164703031237566), (Int.ofNat 10630641375734458441500736), (Int.negOfNat 2438235144353412064260949), (Int.negOfNat 69981385901372929551177), (Int.ofNat 19173257075782551148532), (Int.ofNat 299112435945743445794), (Int.negOfNat 101516087953700921610), (Int.negOfNat 501054704074774924), (Int.ofNat 252254895292924551), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(7240872531937678971518049345787239/11258999068426240000000000000000000), (-308744637744411222291389453271199/5629499534213120000000000000000000), (-17678863798593116646084409097559/2251799813685248000000000000000000), (-4580331719942623888375477827387/5629499534213120000000000000000000), (780016124434671603121342074389/11258999068426240000000000000000000), (54409274483894267250736651479/5629499534213120000000000000000000), (-684809163375908267250860193/703687441776640000000000000000000), (-280411173188455155890470259/2814749767106560000000000000000000), (99370873724582351515618783/5629499534213120000000000000000000), (166103771495850913148449/175921860444160000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial131.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial131.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial131.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial131 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 5594202793913782360571920236515562), (Int.negOfNat 1049719535604481580980351064364250), (Int.negOfNat 118939463867155990841491812397414), (Int.negOfNat 573965980044384983861723377036), (Int.ofNat 1128886189284117176820814034852), (Int.negOfNat 26208589994644277430340448589), (Int.negOfNat 5362544126612285190028350298), (Int.ofNat 1353421674815352890630048961), (Int.ofNat 3879815816950905072536688), (Int.negOfNat 22636512825860554140411101), (Int.ofNat 241082603778823151331658), (Int.ofNat 218952860487850978765759), (Int.negOfNat 2863200748252662048190), (Int.negOfNat 1388494401740949933466), (Int.ofNat 18137660533802873821), (Int.ofNat 6336032866624730849), (Int.ofNat 55494746208439687), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(2797101396956891180285960118257781/5629499534213120000000000000000000), (-4198878142417926323921404257457/45035996273704960000000000000000), (-59469731933577995420745906198707/5629499534213120000000000000000000), (-143491495011096245965430844259/2814749767106560000000000000000000), (282221547321029294205203508713/2814749767106560000000000000000000), (-26208589994644277430340448589/11258999068426240000000000000000000), (-2681272063306142595014175149/5629499534213120000000000000000000), (1353421674815352890630048961/11258999068426240000000000000000000), (242488488559431567033543/703687441776640000000000000000000), (-22636512825860554140411101/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial131.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial131.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial131.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial131 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 3031457754726080408042915366192042), (Int.negOfNat 1498805209135256664574393590274969), (Int.negOfNat 97853006115589510259514707055245), (Int.ofNat 7206195482944126682522042858680), (Int.ofNat 848734275455708066101772980155), (Int.negOfNat 13060943959796630817971241436), (Int.ofNat 2410297236406207692053515573), (Int.negOfNat 663989468260773921341450569), (Int.negOfNat 142775176429716854839012539), (Int.ofNat 12393768361664629568834211), (Int.ofNat 1935634259013901119874642), (Int.negOfNat 118497739561823537497949), (Int.negOfNat 15416198567156537714749), (Int.ofNat 737020983160437948261), (Int.ofNat 82229835130022463580), (Int.negOfNat 3827236986896159191), (Int.negOfNat 230580810175243374), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(1515728877363040204021457683096021/5629499534213120000000000000000000), (-1498805209135256664574393590274969/11258999068426240000000000000000000), (-19570601223117902051902941411049/2251799813685248000000000000000000), (180154887073603167063051071467/281474976710656000000000000000000), (169746855091141613220354596031/2251799813685248000000000000000000), (-3265235989949157704492810359/2814749767106560000000000000000000), (2410297236406207692053515573/11258999068426240000000000000000000), (-663989468260773921341450569/11258999068426240000000000000000000), (-142775176429716854839012539/11258999068426240000000000000000000), (12393768361664629568834211/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial131.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial131.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial131.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial131 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 286712578875193278231420295486922), (Int.negOfNat 1777572358637937865439779994840110), (Int.negOfNat 35339493382179135904020510360850), (Int.ofNat 13321480858523195615465541815869), (Int.ofNat 586288542496205260359452846080), (Int.negOfNat 68032460213862619361959646820), (Int.negOfNat 10492710026739480733525839679), (Int.negOfNat 211554168400738397382188563), (Int.ofNat 192892921498468545341071254), (Int.ofNat 10207767840500636211475710), (Int.negOfNat 2172250685751346638579091), (Int.negOfNat 122041022675364869589256), (Int.ofNat 15670727576089965912495), (Int.ofNat 854001348062372280647), (Int.negOfNat 78519048744265833903), (Int.negOfNat 4296662307101535585), (Int.ofNat 209013685799394464), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-143356289437596639115710147743461/5629499534213120000000000000000000), (-177757235863793786543977999484011/1125899906842624000000000000000000), (-706789867643582718080410207217/225179981368524800000000000000000), (13321480858523195615465541815869/11258999068426240000000000000000000), (57254740478145044956977817/1099511627776000000000000000000), (-3401623010693130968097982341/562949953421312000000000000000000), (-10492710026739480733525839679/11258999068426240000000000000000000), (-211554168400738397382188563/11258999068426240000000000000000000), (96446460749234272670535627/5629499534213120000000000000000000), (1020776784050063621147571/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial131.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial131.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial131.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial131 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 3870086254809680459102655137954006), (Int.negOfNat 1747654336706448104466315799882952), (Int.ofNat 50922709013416289187142032758273), (Int.ofNat 13857157683398598901862705950851), (Int.negOfNat 557777229683881873670358009739), (Int.negOfNat 124066369376499669649551763029), (Int.ofNat 6952248809485794734536069419), (Int.ofNat 2066565846969217457237946157), (Int.negOfNat 33538732853104489657421014), (Int.negOfNat 28578886483188402659714110), (Int.negOfNat 240392982957241743686409), (Int.ofNat 251168344139205598988284), (Int.ofNat 4633682253139534611505), (Int.negOfNat 1481446267003815161253), (Int.negOfNat 33717280139344251817), (Int.ofNat 6553428619082155855), (Int.ofNat 34976002065415116), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-1935043127404840229551327568977003/5629499534213120000000000000000000), (-218456792088306013058289474985369/1407374883553280000000000000000000), (50922709013416289187142032758273/11258999068426240000000000000000000), (13857157683398598901862705950851/11258999068426240000000000000000000), (-557777229683881873670358009739/11258999068426240000000000000000000), (-124066369376499669649551763029/11258999068426240000000000000000000), (6952248809485794734536069419/11258999068426240000000000000000000), (2066565846969217457237946157/11258999068426240000000000000000000), (-16769366426552244828710507/5629499534213120000000000000000000), (-2857888648318840265971411/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial131.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial131.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial131.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial131 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 7063054869413736853438170920506603), (Int.negOfNat 1403289694412406611810350675550163), (Int.ofNat 113623544259295564018431942192471), (Int.ofNat 6495172361094198145356711353897), (Int.negOfNat 948053837141539150831782213766), (Int.ofNat 65767143155990488263463095056), (Int.ofNat 15767985901088931771408899687), (Int.negOfNat 1539221316713328972746059469), (Int.negOfNat 285046615563985468914185561), (Int.ofNat 13026618644678343036168291), (Int.ofNat 3208742033460085722936438), (Int.negOfNat 56351323356112438883109), (Int.negOfNat 23081277238879826514271), (Int.ofNat 88074168282230802161), (Int.ofNat 114355709517247867840), (Int.ofNat 894744743798071909), (Int.negOfNat 375719713752314486), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-7063054869413736853438170920506603/11258999068426240000000000000000000), (-1403289694412406611810350675550163/11258999068426240000000000000000000), (113623544259295564018431942192471/11258999068426240000000000000000000), (6495172361094198145356711353897/11258999068426240000000000000000000), (-474026918570769575415891106883/5629499534213120000000000000000000), (4110446447249405516466443441/703687441776640000000000000000000), (15767985901088931771408899687/11258999068426240000000000000000000), (-1539221316713328972746059469/11258999068426240000000000000000000), (-285046615563985468914185561/11258999068426240000000000000000000), (13026618644678343036168291/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial131.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial131.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial131.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial131 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 9375494108279741544547831428880409), (Int.negOfNat 893838548200926133011300479823061), (Int.ofNat 137435714895342115731198051749635), (Int.ofNat 2805984670862063903962855306052), (Int.negOfNat 4046369534713337447507372345), (Int.ofNat 46262065048367174757600241030), (Int.negOfNat 20264235949817302768023180222), (Int.negOfNat 1968093866586799779821102699), (Int.ofNat 294407965633725455575219372), (Int.ofNat 32049416716642491307769079), (Int.negOfNat 2258915205856379814375778), (Int.negOfNat 296553539234844234923661), (Int.ofNat 10978510999244496665150), (Int.ofNat 1790503955707825726654), (Int.negOfNat 36744147106131629201), (Int.negOfNat 7743680566546434691), (Int.ofNat 243981820020873153), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-9375494108279741544547831428880409/11258999068426240000000000000000000), (-893838548200926133011300479823061/11258999068426240000000000000000000), (27487142979068423146239610349927/2251799813685248000000000000000000), (701496167715515975990713826513/2814749767106560000000000000000000), (-809273906942667489501474469/2251799813685248000000000000000000), (4626206504836717475760024103/1125899906842624000000000000000000), (-10132117974908651384011590111/5629499534213120000000000000000000), (-1968093866586799779821102699/11258999068426240000000000000000000), (73601991408431363893804843/2814749767106560000000000000000000), (32049416716642491307769079/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial131.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial131.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial131.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial131 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 10591024734607662636592249397085799), (Int.negOfNat 311264061750357518664802297239045), (Int.ofNat 152331396952713516432795360817531), (Int.ofNat 934059950833762740396193609310), (Int.negOfNat 890282714437631980773742929923), (Int.negOfNat 191062780346042831195473372092), (Int.negOfNat 4284290788279007271849466021), (Int.ofNat 4070636915141715364609258684), (Int.ofNat 221288575293443479318001054), (Int.negOfNat 43052996942044916947481684), (Int.negOfNat 2999913148937447554545251), (Int.ofNat 283008522096869712952323), (Int.ofNat 23297006117190851067008), (Int.negOfNat 1269690112137811419946), (Int.negOfNat 119740115491068274670), (Int.ofNat 3834734466799700976), (Int.ofNat 354045628634633309), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-10591024734607662636592249397085799/11258999068426240000000000000000000), (-62252812350071503732960459447809/2251799813685248000000000000000000), (152331396952713516432795360817531/11258999068426240000000000000000000), (93405995083376274039619360931/1125899906842624000000000000000000), (-890282714437631980773742929923/11258999068426240000000000000000000), (-47765695086510707798868343023/2814749767106560000000000000000000), (-4284290788279007271849466021/11258999068426240000000000000000000), (1017659228785428841152314671/2814749767106560000000000000000000), (110644287646721739659000527/5629499534213120000000000000000000), (-10763249235511229236870421/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial131.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial131.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial131.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial131 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 10616834278529504898556242960246120), (Int.ofNat 266612963727626278517758920525142), (Int.ofNat 123164089996494598610122992549623), (Int.negOfNat 12103498667414295955454207490812), (Int.negOfNat 1869921854299385266276451833784), (Int.ofNat 97814939756998121732805103028), (Int.ofNat 43681903343859665106340736966), (Int.ofNat 433302674651257196316246628), (Int.negOfNat 606280505754317430070532458), (Int.negOfNat 20135624817530253629951768), (Int.ofNat 5131436979587940546363623), (Int.ofNat 235349008973685111678893), (Int.negOfNat 28828168177139578288065), (Int.negOfNat 1580107997291691973651), (Int.ofNat 114176346574861673484), (Int.ofNat 7171253497686623273), (Int.negOfNat 515714947067934363), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-265420856963237622463906074006153/281474976710656000000000000000000), (133306481863813139258879460262571/5629499534213120000000000000000000), (123164089996494598610122992549623/11258999068426240000000000000000000), (-3025874666853573988863551872703/2814749767106560000000000000000000), (-233740231787423158284556479223/1407374883553280000000000000000000), (24453734939249530433201275757/2814749767106560000000000000000000), (21840951671929832553170368483/5629499534213120000000000000000000), (108325668662814299079061657/2814749767106560000000000000000000), (-303140252877158715035266229/5629499534213120000000000000000000), (-2516953102191281703743971/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial131.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial131.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial131.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial131 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 9711877457067908416504276239239535), (Int.ofNat 569957002878695257196182576739560), (Int.ofNat 23149354184723660556500854375406), (Int.negOfNat 17028078672592894122229190536220), (Int.ofNat 1165056072112921188429913880350), (Int.ofNat 391219599907561448150009917848), (Int.negOfNat 12914138360787516999835377573), (Int.negOfNat 6842326798877210622086706064), (Int.negOfNat 1251943740511796046213559), (Int.ofNat 74468281630693474515426586), (Int.ofNat 1384153538904289710319791), (Int.negOfNat 521646037645786809815845), (Int.negOfNat 15486410264130157459598), (Int.ofNat 2507745067427750527192), (Int.ofNat 94139795119951115537), (Int.negOfNat 8600875194644306821), (Int.negOfNat 332371543516952132), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-1942375491413581683300855247847907/2251799813685248000000000000000000), (14248925071967381429904564418489/281474976710656000000000000000000), (11574677092361830278250427187703/5629499534213120000000000000000000), (-851403933629644706111459526811/562949953421312000000000000000000), (23301121442258423768598277607/225179981368524800000000000000000), (48902449988445181018751239731/1407374883553280000000000000000000), (-12914138360787516999835377573/11258999068426240000000000000000000), (-427645424929825663880419129/703687441776640000000000000000000), (-1251943740511796046213559/11258999068426240000000000000000000), (37234140815346737257713293/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial131.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial131.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial131.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial131 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 8586094947642028732138986608143812), (Int.ofNat 521423226226774949198219610982847), (Int.negOfNat 27116097931887698994843752899840), (Int.ofNat 2439555169548881733269210558502), (Int.ofNat 2680999722097186138738894383574), (Int.negOfNat 193877946378750683066175525025), (Int.negOfNat 62183436419222051590522419839), (Int.ofNat 2343454716496481517229312128), (Int.ofNat 890210476022101522798718303), (Int.negOfNat 8386769901116979829487434), (Int.negOfNat 7915367878306289465748828), (Int.negOfNat 61435237921424727552522), (Int.ofNat 46351542420607112122289), (Int.ofNat 839307772216684508399), (Int.negOfNat 191325296288718595671), (Int.negOfNat 4801721638591524573), (Int.ofNat 787448074114995573), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-2146523736910507183034746652035953/2814749767106560000000000000000000), (521423226226774949198219610982847/11258999068426240000000000000000000), (-21184451509287264839721681953/8796093022208000000000000000000), (1219777584774440866634605279251/5629499534213120000000000000000000), (1340499861048593069369447191787/5629499534213120000000000000000000), (-7755117855150027322647021001/450359962737049600000000000000000), (-62183436419222051590522419839/11258999068426240000000000000000000), (18308239972628761853354001/87960930222080000000000000000000), (890210476022101522798718303/11258999068426240000000000000000000), (-4193384950558489914743717/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial131.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial131.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial131.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial131 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 7598968759818712965883905547868711), (Int.ofNat 502478094714822878500281831435256), (Int.ofNat 24472656214864354164758319073718), (Int.ofNat 8926733408985826116612775730486), (Int.negOfNat 1472399189371384839691055145885), (Int.negOfNat 422197693982093936923142810120), (Int.ofNat 39960247825916547718356980407), (Int.ofNat 8634841080100750513350373067), (Int.negOfNat 403501127907035716410352035), (Int.negOfNat 101867510648326553543879093), (Int.ofNat 1698481230495818081884249), (Int.ofNat 741816328252961858272111), (Int.negOfNat 34984502255435818626), (Int.negOfNat 3647173533098457588309), (Int.negOfNat 35311332566565959880), (Int.ofNat 13328687239508688766), (Int.ofNat 220119749383583885), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-7598968759818712965883905547868711/11258999068426240000000000000000000), (62809761839352859812535228929407/1407374883553280000000000000000000), (12236328107432177082379159536859/5629499534213120000000000000000000), (4463366704492913058306387865243/5629499534213120000000000000000000), (-294479837874276967938211029177/2251799813685248000000000000000000), (-10554942349552348423078570253/281474976710656000000000000000000), (39960247825916547718356980407/11258999068426240000000000000000000), (8634841080100750513350373067/11258999068426240000000000000000000), (-80700225581407143282070407/2251799813685248000000000000000000), (-101867510648326553543879093/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial131.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial131.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial131.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial131 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 6458266300122570954347703304699520), (Int.ofNat 637506675504129938581880394628051), (Int.ofNat 23160122889214309999221023253195), (Int.negOfNat 9725581994837810191115094477070), (Int.negOfNat 1688834004674389379179297310110), (Int.ofNat 430948218182382217557352979297), (Int.ofNat 63078368748579657621417001657), (Int.negOfNat 7337921551887540525929714219), (Int.negOfNat 1098562022868899267334834175), (Int.ofNat 55485223323911464699545277), (Int.ofNat 10361452632974974407427945), (Int.negOfNat 216258363898767382078087), (Int.negOfNat 61691215424315679619010), (Int.ofNat 349449840899567993409), (Int.ofNat 255481504638960235004), (Int.ofNat 868458897776428574), (Int.negOfNat 954154102067915595), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-10091041093941517116168286413593/17592186044416000000000000000000), (637506675504129938581880394628051/11258999068426240000000000000000000), (4632024577842861999844204650639/2251799813685248000000000000000000), (-972558199483781019111509447707/1125899906842624000000000000000000), (-168883400467438937917929731011/1125899906842624000000000000000000), (430948218182382217557352979297/11258999068426240000000000000000000), (63078368748579657621417001657/11258999068426240000000000000000000), (-7337921551887540525929714219/11258999068426240000000000000000000), (-43942480914755970693393367/450359962737049600000000000000000), (55485223323911464699545277/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial131.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial131.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial131.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial131 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 5178793254826124378326789324028244), (Int.ofNat 601749067212029941790258761699407), (Int.negOfNat 32645494425012660998847562085450), (Int.negOfNat 1541997297626800435578471125650), (Int.ofNat 3466752004138261886228687427760), (Int.ofNat 262485418481789030019547686483), (Int.negOfNat 97166841113395467709882614555), (Int.negOfNat 9535704520335189249835842944), (Int.ofNat 1052898535118671670555223599), (Int.ofNat 126085334054413396879680446), (Int.negOfNat 6101879969417581328470412), (Int.negOfNat 932257630173471651990170), (Int.ofNat 21436960679257428239581), (Int.ofNat 4570446917032312271677), (Int.negOfNat 44315082699302349063), (Int.negOfNat 16853971655557192927), (Int.negOfNat 24514941273755627), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-1294698313706531094581697331007061/2814749767106560000000000000000000), (601749067212029941790258761699407/11258999068426240000000000000000000), (-652909888500253219976951241709/225179981368524800000000000000000), (-30839945952536008711569422513/225179981368524800000000000000000), (43334400051728273577858592847/140737488355328000000000000000000), (262485418481789030019547686483/11258999068426240000000000000000000), (-19433368222679093541976522911/2251799813685248000000000000000000), (-74497691565118666014342523/87960930222080000000000000000000), (1052898535118671670555223599/11258999068426240000000000000000000), (63042667027206698439840223/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial131.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial131.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial131.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial131 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 4061458694938634381134737020485917), (Int.ofNat 562997677579766668904126163745712), (Int.ofNat 34948765530438999372141367634717), (Int.ofNat 18239961292292730818079646713703), (Int.negOfNat 837868455086333060714536633895), (Int.negOfNat 1051816130477953780263130226321), (Int.negOfNat 60101241421436091282892263605), (Int.ofNat 15686381265496530093088087680), (Int.ofNat 1330057785274144538790396909), (Int.negOfNat 118828269348780062947527426), (Int.negOfNat 12658018500045804856857241), (Int.ofNat 560065488295622248245929), (Int.ofNat 73994664340410991673622), (Int.negOfNat 1800601134223631434040), (Int.negOfNat 302852343538368873971), (Int.ofNat 4036141230599279321), (Int.ofNat 1023057725965921488), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-4061458694938634381134737020485917/11258999068426240000000000000000000), (35187354848735416806507885234107/703687441776640000000000000000000), (34948765530438999372141367634717/11258999068426240000000000000000000), (18239961292292730818079646713703/11258999068426240000000000000000000), (-167573691017266612142907326779/2251799813685248000000000000000000), (-1051816130477953780263130226321/11258999068426240000000000000000000), (-12020248284287218256578452721/2251799813685248000000000000000000), (24509970727338328270450137/17592186044416000000000000000000), (1330057785274144538790396909/11258999068426240000000000000000000), (-59414134674390031473763713/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial131.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial131.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial131.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial131 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 2698383097928585455086536963569712), (Int.ofNat 807234642436660392211971531111708), (Int.ofNat 37961809890972855505029796026619), (Int.negOfNat 29785990356434457628404798961010), (Int.negOfNat 9697409712989679095822638282367), (Int.negOfNat 177962918438743391316477396501), (Int.ofNat 198136250511901786825704702221), (Int.ofNat 12217924992730785057225769656), (Int.negOfNat 1888077931664557951933557858), (Int.negOfNat 155966061823527442943302180), (Int.ofNat 11057870551683618287811171), (Int.ofNat 1098027456422364995512083), (Int.negOfNat 44800616953625000715909), (Int.negOfNat 5195370537386781326901), (Int.ofNat 133841808292952348752), (Int.ofNat 18501034010729585727), (Int.negOfNat 247218185773305583), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-168648943620536590942908560223107/703687441776640000000000000000000), (201808660609165098052992882777927/2814749767106560000000000000000000), (37961809890972855505029796026619/11258999068426240000000000000000000), (-2978599035643445762840479896101/1125899906842624000000000000000000), (-9697409712989679095822638282367/11258999068426240000000000000000000), (-177962918438743391316477396501/11258999068426240000000000000000000), (198136250511901786825704702221/11258999068426240000000000000000000), (1527240624091348132153221207/1407374883553280000000000000000000), (-944038965832278975966778929/5629499534213120000000000000000000), (-7798303091176372147165109/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial131.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial131.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial131.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial131 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 1317513104589133303826327050314545), (Int.ofNat 318386532592604927711149948471873), (Int.negOfNat 335913466698334839528262330997915), (Int.negOfNat 79952063234157100712595754409022), (Int.ofNat 1276256012774211121834244751097), (Int.ofNat 2181263372629841623376238208628), (Int.ofNat 102655728528648143091721013892), (Int.negOfNat 25657549773435280263767548548), (Int.negOfNat 1785439205578338411347616066), (Int.ofNat 182102623449386013366265412), (Int.ofNat 15112712400103813842162497), (Int.negOfNat 890868263852025279749699), (Int.negOfNat 82652332228338873964896), (Int.ofNat 3231077731210064360638), (Int.ofNat 325010210928491296438), (Int.negOfNat 8690082240386128756), (Int.negOfNat 1001383640848240311), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-263502620917826660765265410062909/2251799813685248000000000000000000), (318386532592604927711149948471873/11258999068426240000000000000000000), (-67182693339666967905652466199583/2251799813685248000000000000000000), (-39976031617078550356297877204511/5629499534213120000000000000000000), (1276256012774211121834244751097/11258999068426240000000000000000000), (545315843157460405844059552157/2814749767106560000000000000000000), (25663932132162035772930253473/2814749767106560000000000000000000), (-6414387443358820065941887137/2814749767106560000000000000000000), (-892719602789169205673808033/5629499534213120000000000000000000), (45525655862346503341566353/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial131.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial131.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial131.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial131 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 2570854579767978143622707137531635), (Int.negOfNat 1762478720809732539705526450370150), (Int.negOfNat 605315455417876358621440167956040), (Int.ofNat 17531043657400832926343487321646), (Int.ofNat 20955160172088004188335361067821), (Int.ofNat 913650596719368080152146574010), (Int.negOfNat 300496801315193150794684595354), (Int.negOfNat 19814608566132362681980601597), (Int.ofNat 2567335255896990924164555600), (Int.ofNat 196525078004774670932991041), (Int.negOfNat 15007160085929788673579910), (Int.negOfNat 1230222997341068296002983), (Int.ofNat 64609476037599248188450), (Int.ofNat 5453869446471277441314), (Int.negOfNat 214303456920217049829), (Int.negOfNat 18322092795509783009), (Int.ofNat 518951312820366793), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-514170915953595628724541427506327/2251799813685248000000000000000000), (-35249574416194650794110529007403/225179981368524800000000000000000), (-15132886385446908965536004198901/281474976710656000000000000000000), (8765521828700416463171743660823/5629499534213120000000000000000000), (20955160172088004188335361067821/11258999068426240000000000000000000), (91365059671936808015214657401/1125899906842624000000000000000000), (-150248400657596575397342297677/5629499534213120000000000000000000), (-19814608566132362681980601597/11258999068426240000000000000000000), (6418338139742477310411389/28147497671065600000000000000000), (196525078004774670932991041/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial131.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial131.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial131.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial131 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 8033333900046605821859134506102146), (Int.negOfNat 3293290275140070953702025913425704), (Int.negOfNat 4244080657128603672412405188079), (Int.ofNat 167926072926903045415739046078274), (Int.ofNat 9937829494651311621334136154644), (Int.negOfNat 2959693384231336430998782116685), (Int.negOfNat 222093799339092768317234744809), (Int.ofNat 30776252516745561106150702545), (Int.ofNat 2462073840343422361046355375), (Int.negOfNat 216655473333969747380973723), (Int.negOfNat 17332577739471768454404006), (Int.ofNat 1109621967115398874494941), (Int.ofNat 85937065970097533472221), (Int.negOfNat 4327974314130324564277), (Int.negOfNat 319270348489401928012), (Int.ofNat 13018373931357062871), (Int.ofNat 979709555730559134), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-4016666950023302910929567253051073/5629499534213120000000000000000000), (-411661284392508869212753239178213/1407374883553280000000000000000000), (-4244080657128603672412405188079/11258999068426240000000000000000000), (83963036463451522707869523039137/5629499534213120000000000000000000), (2484457373662827905333534038661/2814749767106560000000000000000000), (-591938676846267286199756423337/2251799813685248000000000000000000), (-222093799339092768317234744809/11258999068426240000000000000000000), (6155250503349112221230140509/2251799813685248000000000000000000), (19696590722747378888370843/90071992547409920000000000000000), (-216655473333969747380973723/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial131.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial131.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial131.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial131 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 13238957549695811796726237409812080), (Int.negOfNat 1240825303818802567111149015233561), (Int.ofNat 975674198352333365410304302601363), (Int.ofNat 113776809024007358906421109520377), (Int.negOfNat 22660471007743781417074293427458), (Int.negOfNat 2473335261818696831063027862936), (Int.ofNat 301027660255132970281270671518), (Int.ofNat 29779731803152904515288645715), (Int.negOfNat 2638286561054165327498212434), (Int.negOfNat 232520550679725911718961894), (Int.ofNat 16405242108416886174546267), (Int.ofNat 1279199446078168590622552), (Int.negOfNat 75962867883671987776379), (Int.negOfNat 5237851607766898091647), (Int.ofNat 272202551287968077287), (Int.ofNat 16282722235986587745), (Int.negOfNat 783459744828200944), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-165486969371197647459077967622651/140737488355328000000000000000000), (-1240825303818802567111149015233561/11258999068426240000000000000000000), (975674198352333365410304302601363/11258999068426240000000000000000000), (113776809024007358906421109520377/11258999068426240000000000000000000), (-11330235503871890708537146713729/5629499534213120000000000000000000), (-309166907727337103882878482867/1407374883553280000000000000000000), (150513830127566485140635335759/5629499534213120000000000000000000), (5955946360630580903057729143/2251799813685248000000000000000000), (-1319143280527082663749106217/5629499534213120000000000000000000), (-116260275339862955859480947/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial131.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial131.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial131.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial131.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial131 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial131 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial131 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 16007970348279126716584618914904709), (Int.ofNat 325900301155329894909306765183519), (Int.ofNat 1057059102374237369782584009201224), (Int.negOfNat 101940264398361070198778694002893), (Int.negOfNat 23323158269467341075820588454999), (Int.ofNat 2403294095374682634227308339757), (Int.ofNat 303934295673304156894612911559), (Int.negOfNat 29545423451643208043194474315), (Int.negOfNat 2645799716848576002814301734), (Int.ofNat 232041645305913052188369994), (Int.ofNat 16417615051094878070144067), (Int.negOfNat 1278551521754439811368152), (Int.negOfNat 75977160331989534377579), (Int.ofNat 5235469533047306991447), (Int.ofNat 272202551287968077287), (Int.negOfNat 16282722235986587745), (Int.negOfNat 783459744828200944), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-16007970348279126716584618914904709/11258999068426240000000000000000000), (325900301155329894909306765183519/11258999068426240000000000000000000), (132132387796779671222823001150153/1407374883553280000000000000000000), (-101940264398361070198778694002893/11258999068426240000000000000000000), (-23323158269467341075820588454999/11258999068426240000000000000000000), (2403294095374682634227308339757/11258999068426240000000000000000000), (303934295673304156894612911559/11258999068426240000000000000000000), (-5909084690328641608638894863/2251799813685248000000000000000000), (-1322899858424288001407150867/5629499534213120000000000000000000), (116020822652956526094184997/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial131.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial131.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial131.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 12224595182875156221750115792045001), (Int.ofNat 2819788455923505659210292813527188), (Int.ofNat 127491840598091227946156681096149), (Int.negOfNat 163612221222541266565562080615565), (Int.ofNat 8804581012859465330598477955559), (Int.ofNat 2939999692857088538415406165736), (Int.negOfNat 217019950253149531500026092409), (Int.negOfNat 30716236057791513466605299045), (Int.ofNat 2448888768858049574163674575), (Int.ofNat 216535704977340824944781823), (Int.negOfNat 17310838255704126492240306), (Int.negOfNat 1109459986034466679681341), (Int.ofNat 85913245222901622470221), (Int.ofNat 4327974314130324564277), (Int.negOfNat 319270348489401928012), (Int.negOfNat 13018373931357062871), (Int.ofNat 979709555730559134), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-12224595182875156221750115792045001/11258999068426240000000000000000000), (704947113980876414802573203381797/2814749767106560000000000000000000), (127491840598091227946156681096149/11258999068426240000000000000000000), (-32722444244508253313112416123113/2251799813685248000000000000000000), (8804581012859465330598477955559/11258999068426240000000000000000000), (367499961607136067301925770717/1407374883553280000000000000000000), (-217019950253149531500026092409/11258999068426240000000000000000000), (-6143247211558302693321059809/2251799813685248000000000000000000), (97955550754321982966546983/450359962737049600000000000000000), (216535704977340824944781823/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial131.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial131.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial131.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 7166098181970008300413031728655766), (Int.ofNat 1830834761781610082309816928613361), (Int.negOfNat 475235754225671507970786999324062), (Int.negOfNat 22249436005476899881961315290893), (Int.ofNat 19931255966007279282638362110328), (Int.negOfNat 873387537713131665533139323302), (Int.negOfNat 296065980699966930845188999954), (Int.ofNat 19667506873536872011672366697), (Int.ofNat 2555923143433657570562412500), (Int.negOfNat 196218284694859466970116041), (Int.negOfNat 14988382960226932935978610), (Int.ofNat 1229806134265139853467983), (Int.ofNat 64588037365122928286650), (Int.negOfNat 5453869446471277441314), (Int.negOfNat 214303456920217049829), (Int.ofNat 18322092795509783009), (Int.ofNat 518951312820366793), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-3583049090985004150206515864327883/5629499534213120000000000000000000), (1830834761781610082309816928613361/11258999068426240000000000000000000), (-237617877112835753985393499662031/5629499534213120000000000000000000), (-22249436005476899881961315290893/11258999068426240000000000000000000), (2491406995750909910329795263791/1407374883553280000000000000000000), (-436693768856565832766569661651/5629499534213120000000000000000000), (-148032990349983465422594499977/5629499534213120000000000000000000), (19667506873536872011672366697/11258999068426240000000000000000000), (204473851474692605644993/900719925474099200000000000000), (-196218284694859466970116041/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial131.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial131.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial131.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 5308305010900962956918602516948439), (Int.ofNat 184897642892745748967505893901610), (Int.negOfNat 254551064798140244911809904697800), (Int.ofNat 69260981315944058315366766348686), (Int.ofNat 868330819068011999610560417547), (Int.negOfNat 2104544046433775655308593741178), (Int.ofNat 104010909185600784233970295033), (Int.ofNat 25387371372373585613793890348), (Int.negOfNat 1788647742596555702557893666), (Int.negOfNat 181543720757337349655093712), (Int.ofNat 15117883115008365215421397), (Int.ofNat 890110764091195309886099), (Int.negOfNat 82657096377778056165296), (Int.negOfNat 3231077731210064360638), (Int.ofNat 325010210928491296438), (Int.ofNat 8690082240386128756), (Int.negOfNat 1001383640848240311), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-5308305010900962956918602516948439/11258999068426240000000000000000000), (18489764289274574896750589390161/1125899906842624000000000000000000), (-1272755323990701224559049523489/56294995342131200000000000000000), (34630490657972029157683383174343/5629499534213120000000000000000000), (868330819068011999610560417547/11258999068426240000000000000000000), (-1052272023216887827654296870589/5629499534213120000000000000000000), (104010909185600784233970295033/11258999068426240000000000000000000), (6346842843093396403448472587/2814749767106560000000000000000000), (-894323871298277851278946833/5629499534213120000000000000000000), (-11346482547333584353443357/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial131.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial131.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial131.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 5446705868451031278245661386668229), (Int.negOfNat 113572727704478052819912359169442), (Int.ofNat 51665608878147469946312111141491), (Int.ofNat 18963110871678318975691429374112), (Int.negOfNat 9333783808584114639230630354104), (Int.ofNat 247957690364431919264293977643), (Int.ofNat 195731146489111033271320296550), (Int.negOfNat 12458062421550968002743809256), (Int.negOfNat 1881311655536385840790576458), (Int.ofNat 156459838764570815704303780), (Int.ofNat 11046515871371981094896271), (Int.negOfNat 1098694437343850503568083), (Int.negOfNat 44786324505307454114709), (Int.ofNat 5197752612106372427101), (Int.ofNat 133841808292952348752), (Int.negOfNat 18501034010729585727), (Int.negOfNat 247218185773305583), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-5446705868451031278245661386668229/11258999068426240000000000000000000), (-56786363852239026409956179584721/5629499534213120000000000000000000), (51665608878147469946312111141491/11258999068426240000000000000000000), (592597214739947467990357167941/351843720888320000000000000000000), (-1166722976073014329903828794263/1407374883553280000000000000000000), (247957690364431919264293977643/11258999068426240000000000000000000), (3914622929782220665426405931/225179981368524800000000000000000), (-1557257802693871000342976157/1407374883553280000000000000000000), (-940655827768192920395288229/5629499534213120000000000000000000), (7822991938228540785215189/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial131.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial131.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial131.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 5446350320959268879755965136393893), (Int.ofNat 72279129455224860757925996426462), (Int.negOfNat 2682454411654943528661412064266), (Int.negOfNat 23858757563010847097765913052137), (Int.ofNat 23550601880228918501518732819), (Int.ofNat 1076695033104688006554466957841), (Int.negOfNat 64825769667858001815882551005), (Int.negOfNat 15761193330193856913875298780), (Int.ofNat 1342911642686907564384866409), (Int.ofNat 118977021474392638706225226), (Int.negOfNat 12679431242709940778902941), (Int.negOfNat 560265582572067900662729), (Int.ofNat 74020867162326493775822), (Int.ofNat 1800601134223631434040), (Int.negOfNat 302852343538368873971), (Int.negOfNat 4036141230599279321), (Int.ofNat 1023057725965921488), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-5446350320959268879755965136393893/11258999068426240000000000000000000), (36139564727612430378962998213231/5629499534213120000000000000000000), (-1341227205827471764330706032133/5629499534213120000000000000000000), (-23858757563010847097765913052137/11258999068426240000000000000000000), (23550601880228918501518732819/11258999068426240000000000000000000), (1076695033104688006554466957841/11258999068426240000000000000000000), (-12965153933571600363176510201/2251799813685248000000000000000000), (-788059666509692845693764939/562949953421312000000000000000000), (1342911642686907564384866409/11258999068426240000000000000000000), (59488510737196319353112613/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial131.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial131.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial131.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 5474336288155140222078111229250132), (Int.negOfNat 155794204599021561768285974152827), (Int.negOfNat 82485813987691315135071181033640), (Int.ofNat 3035389536037315578867457147828), (Int.ofNat 4287243987136598866256320984288), (Int.negOfNat 294702742650730159815590851226), (Int.negOfNat 101472588441179244604142518655), (Int.ofNat 9666988801589362461094087244), (Int.ofNat 1064507638409717520761231499), (Int.negOfNat 126365279922121060381808146), (Int.negOfNat 6121180035097657805218212), (Int.ofNat 932638762128606228022170), (Int.ofNat 21458399351733748141381), (Int.negOfNat 4570446917032312271677), (Int.negOfNat 44315082699302349063), (Int.ofNat 16853971655557192927), (Int.negOfNat 24514941273755627), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-1368584072038785055519527807312533/2814749767106560000000000000000000), (-155794204599021561768285974152827/11258999068426240000000000000000000), (-2062145349692282878376779525841/281474976710656000000000000000000), (758847384009328894716864286957/2814749767106560000000000000000000), (133976374598018714570510030759/351843720888320000000000000000000), (-147351371325365079907795425613/5629499534213120000000000000000000), (-20294517688235848920828503731/2251799813685248000000000000000000), (2416747200397340615273521811/2814749767106560000000000000000000), (1064507638409717520761231499/11258999068426240000000000000000000), (-63182639961060530190904073/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial131.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial131.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial131.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 6037472784953526140775189336814314), (Int.negOfNat 350070766165398645713352107391881), (Int.negOfNat 1531274563737522734554801980375), (Int.ofNat 15897837293993015154502706349887), (Int.negOfNat 1400467699814188298065412477762), (Int.negOfNat 499312391475905058620913552826), (Int.ofNat 61664693920595287385636330857), (Int.ofNat 7598634125871785010196541219), (Int.negOfNat 1094806955449473709700664875), (Int.negOfNat 56033910023194280068762277), (Int.ofNat 10355230653807402453705545), (Int.ofNat 217006335360718987540887), (Int.negOfNat 61684069200156906318410), (Int.negOfNat 349449840899567993409), (Int.ofNat 255481504638960235004), (Int.negOfNat 868458897776428574), (Int.negOfNat 954154102067915595), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-3018736392476763070387594668407157/5629499534213120000000000000000000), (-350070766165398645713352107391881/11258999068426240000000000000000000), (-12250196509900181876438415843/90071992547409920000000000000000), (15897837293993015154502706349887/11258999068426240000000000000000000), (-700233849907094149032706238881/5629499534213120000000000000000000), (-249656195737952529310456776413/5629499534213120000000000000000000), (61664693920595287385636330857/11258999068426240000000000000000000), (7598634125871785010196541219/11258999068426240000000000000000000), (-8758455643595789677605319/90071992547409920000000000000000), (-56033910023194280068762277/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial131.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial131.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial131.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 6650321194487543093403068910278921), (Int.negOfNat 236134192336517004168189513339637), (Int.ofNat 38106515343488867458679153081042), (Int.negOfNat 3258587639731470810102678799039), (Int.negOfNat 1877553669728745034036636179813), (Int.ofNat 359317777771432913420197162331), (Int.ofNat 42238790432965854169497402077), (Int.negOfNat 8394989854696040011753484867), (Int.negOfNat 409730888298418391420730135), (Int.ofNat 101362703899738944757360893), (Int.ofNat 1708872336724623843884049), (Int.negOfNat 741127908659000030314311), (Int.negOfNat 46894875853391319626), (Int.ofNat 3647173533098457588309), (Int.negOfNat 35311332566565959880), (Int.negOfNat 13328687239508688766), (Int.ofNat 220119749383583885), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-6650321194487543093403068910278921/11258999068426240000000000000000000), (-236134192336517004168189513339637/11258999068426240000000000000000000), (19053257671744433729339576540521/5629499534213120000000000000000000), (-3258587639731470810102678799039/11258999068426240000000000000000000), (-1877553669728745034036636179813/11258999068426240000000000000000000), (359317777771432913420197162331/11258999068426240000000000000000000), (42238790432965854169497402077/11258999068426240000000000000000000), (-8394989854696040011753484867/11258999068426240000000000000000000), (-81946177659683678284146027/2251799813685248000000000000000000), (101362703899738944757360893/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial131.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial131.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial131.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 7013198917494367522467968816059974), (Int.negOfNat 149984022983342667482572709899255), (Int.ofNat 6467213490455873467982385901215), (Int.negOfNat 2042648868179330318608087810266), (Int.ofNat 1842071202498460374833428908770), (Int.ofNat 174782120523571478949530202456), (Int.negOfNat 57539704128750181830369942639), (Int.negOfNat 2262735066826603458124739328), (Int.ofNat 877553355413818535171377103), (Int.ofNat 8213466120377815547609434), (Int.negOfNat 7894271951579859160029728), (Int.ofNat 61671063318664246472322), (Int.ofNat 46327721673411201120289), (Int.negOfNat 839307772216684508399), (Int.negOfNat 191325296288718595671), (Int.ofNat 4801721638591524573), (Int.ofNat 787448074114995573), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-3506599458747183761233984408029987/5629499534213120000000000000000000), (-29996804596668533496514541979851/2251799813685248000000000000000000), (1293442698091174693596477180243/2251799813685248000000000000000000), (-1021324434089665159304043905133/5629499534213120000000000000000000), (184207120249846037483342890877/1125899906842624000000000000000000), (21847765065446434868691275307/1407374883553280000000000000000000), (-57539704128750181830369942639/11258999068426240000000000000000000), (-8838808854791419758299763/43980465111040000000000000000000), (877553355413818535171377103/11258999068426240000000000000000000), (4106733060188907773804717/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial131.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial131.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial131.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 7272324223060155414199014128824273), (Int.negOfNat 86880548130632503521760683264386), (Int.ofNat 38597660122086351838356077601309), (Int.ofNat 10714641985868712647066538707004), (Int.ofNat 421810422465988356179326608229), (Int.negOfNat 353655324603120665757176167659), (Int.negOfNat 8601456299388080614914648273), (Int.ofNat 6716456744684546480717539564), (Int.negOfNat 13113465542786789365461359), (Int.negOfNat 74210913769335597369048286), (Int.ofNat 1403960539915203370251191), (Int.ofNat 521298254736726509186645), (Int.negOfNat 15507848936606477361398), (Int.negOfNat 2507745067427750527192), (Int.ofNat 94139795119951115537), (Int.ofNat 8600875194644306821), (Int.negOfNat 332371543516952132), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-7272324223060155414199014128824273/11258999068426240000000000000000000), (-43440274065316251760880341632193/5629499534213120000000000000000000), (38597660122086351838356077601309/11258999068426240000000000000000000), (2678660496467178161766634676751/2814749767106560000000000000000000), (421810422465988356179326608229/11258999068426240000000000000000000), (-353655324603120665757176167659/11258999068426240000000000000000000), (-8601456299388080614914648273/11258999068426240000000000000000000), (1679114186171136620179384891/2814749767106560000000000000000000), (-13113465542786789365461359/11258999068426240000000000000000000), (-37105456884667798684524143/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial131.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial131.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial131.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 7210275263366664600151126918673898), (Int.ofNat 182476944670756829659072507371332), (Int.ofNat 86829628282000001998857470981401), (Int.ofNat 1946624567681711778980304904516), (Int.negOfNat 2026005844700908786962118631693), (Int.negOfNat 23719390594795625887671364046), (Int.ofNat 45137029461065461355441128436), (Int.negOfNat 695244023499371114314774528), (Int.negOfNat 610564345746977747002924358), (Int.ofNat 20677959882472266503378668), (Int.ofNat 5138695210976048290441423), (Int.negOfNat 236082687987319170540493), (Int.negOfNat 28837696476017942688865), (Int.ofNat 1580107997291691973651), (Int.ofNat 114176346574861673484), (Int.negOfNat 7171253497686623273), (Int.negOfNat 515714947067934363), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-3605137631683332300075563459336949/5629499534213120000000000000000000), (45619236167689207414768126842833/2814749767106560000000000000000000), (86829628282000001998857470981401/11258999068426240000000000000000000), (486656141920427944745076226129/2814749767106560000000000000000000), (-2026005844700908786962118631693/11258999068426240000000000000000000), (-11859695297397812943835682023/5629499534213120000000000000000000), (11284257365266365338860282109/2814749767106560000000000000000000), (-339474620849302301911511/5497558138880000000000000000000), (-305282172873488873501462179/5629499534213120000000000000000000), (5169489970618066625844667/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial131.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial131.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial131.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 6512946242092433799773735639658739), (Int.ofNat 494225516401507410518946317795338), (Int.ofNat 57405409332425599545913759757395), (Int.negOfNat 9294332398385959716188206681606), (Int.negOfNat 293992785532865283282212341549), (Int.ofNat 259827107402429394487109032262), (Int.negOfNat 6598513592859413278747685432), (Int.negOfNat 4320072579046882990510452284), (Int.ofNat 227066171940218291101200354), (Int.ofNat 43572403696105882170447184), (Int.negOfNat 3009352541739506179362551), (Int.negOfNat 283713616213868678611523), (Int.ofNat 23306534416069215467808), (Int.ofNat 1269690112137811419946), (Int.negOfNat 119740115491068274670), (Int.negOfNat 3834734466799700976), (Int.ofNat 354045628634633309), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-6512946242092433799773735639658739/11258999068426240000000000000000000), (247112758200753705259473158897669/5629499534213120000000000000000000), (11481081866485119909182751951479/2251799813685248000000000000000000), (-4647166199192979858094103340803/5629499534213120000000000000000000), (-293992785532865283282212341549/11258999068426240000000000000000000), (129913553701214697243554516131/5629499534213120000000000000000000), (-824814199107426659843460679/1407374883553280000000000000000000), (-1080018144761720747627613071/2814749767106560000000000000000000), (113533085970109145550600177/5629499534213120000000000000000000), (2723275231006617635652949/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial131.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial131.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial131.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 5366516043276428578039475272681442), (Int.ofNat 620806185946976261715597020626890), (Int.ofNat 11449781948816565605787303984874), (Int.negOfNat 4142351782318971651579302875924), (Int.ofNat 1079601602922716169046202462488), (Int.negOfNat 22681178316737128924126786871), (Int.negOfNat 25115790072903870753385144122), (Int.ofNat 1873450293369225047791260199), (Int.ofNat 307015229124628173158441372), (Int.negOfNat 31848188445280374051204779), (Int.negOfNat 2279701859736185336459478), (Int.ofNat 296279600642091258400661), (Int.ofNat 11002331746440407667150), (Int.negOfNat 1790503955707825726654), (Int.negOfNat 36744147106131629201), (Int.ofNat 7743680566546434691), (Int.ofNat 243981820020873153), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-2683258021638214289019737636340721/5629499534213120000000000000000000), (62080618594697626171559702062689/1125899906842624000000000000000000), (5724890974408282802893651992437/5629499534213120000000000000000000), (-1035587945579742912894825718981/2814749767106560000000000000000000), (134950200365339521130775307811/1407374883553280000000000000000000), (-22681178316737128924126786871/11258999068426240000000000000000000), (-12557895036451935376692572061/5629499534213120000000000000000000), (1873450293369225047791260199/11258999068426240000000000000000000), (76753807281157043289610343/2814749767106560000000000000000000), (-31848188445280374051204779/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial131.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial131.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial131.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 4097002546764257208837731731839382), (Int.ofNat 645879766915110770329723338834849), (Int.ofNat 6308731353363006803202066096925), (Int.ofNat 974976560962698700064153557320), (Int.ofNat 68453123620714199792805376425), (Int.negOfNat 102474530557024790844557350884), (Int.ofNat 11066189684836508830002010687), (Int.ofNat 1654481266779888375814694769), (Int.negOfNat 272728289526139740996026961), (Int.negOfNat 13258470141182671120587491), (Int.ofNat 3188391522546183232768838), (Int.ofNat 56660993069659281909109), (Int.negOfNat 23057456491683915512271), (Int.negOfNat 88074168282230802161), (Int.ofNat 114355709517247867840), (Int.negOfNat 894744743798071909), (Int.negOfNat 375719713752314486), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-2048501273382128604418865865919691/5629499534213120000000000000000000), (645879766915110770329723338834849/11258999068426240000000000000000000), (252349254134520272128082643877/450359962737049600000000000000000), (24374414024067467501603838933/281474976710656000000000000000000), (2738124944828567991712215057/450359962737049600000000000000000), (-25618632639256197711139337721/2814749767106560000000000000000000), (11066189684836508830002010687/11258999068426240000000000000000000), (1654481266779888375814694769/11258999068426240000000000000000000), (-272728289526139740996026961/11258999068426240000000000000000000), (-13258470141182671120587491/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial131.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial131.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial131.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 2773545519435687074484436683825098), (Int.ofNat 679379447636526301825596530574190), (Int.ofNat 8858171228225007540831115288110), (Int.negOfNat 390459281386549807054259170449), (Int.negOfNat 145574950883127640720776845220), (Int.ofNat 45517812626886075357957824260), (Int.ofNat 5025465383153974870797320419), (Int.negOfNat 1804942800106331680067536857), (Int.negOfNat 28477748689717146175027914), (Int.ofNat 28044717696348384082745710), (Int.negOfNat 248757390184111200575009), (Int.negOfNat 250446575499169495627684), (Int.ofNat 4643210552017899012305), (Int.ofNat 1481446267003815161253), (Int.negOfNat 33717280139344251817), (Int.negOfNat 6553428619082155855), (Int.ofNat 34976002065415116), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1386772759717843537242218341912549/5629499534213120000000000000000000), (67937944763652630182559653057419/1125899906842624000000000000000000), (885817122822500754083111528811/1125899906842624000000000000000000), (-390459281386549807054259170449/11258999068426240000000000000000000), (-7278747544156382036038842261/562949953421312000000000000000000), (2275890631344303767897891213/562949953421312000000000000000000), (5025465383153974870797320419/11258999068426240000000000000000000), (-1804942800106331680067536857/11258999068426240000000000000000000), (-14238874344858573087513957/5629499534213120000000000000000000), (2804471769634838408274571/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial131.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial131.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial131.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 1383253314245548739474570064724114), (Int.ofNat 709297469568358736803488290336532), (Int.ofNat 6725044403173467440658840287687), (Int.ofNat 145217543475970422561090131309), (Int.ofNat 174086263693758613344750027559), (Int.negOfNat 10516096535464737527842556191), (Int.negOfNat 8565926600407660869787090679), (Int.ofNat 473177215263624174552597863), (Int.ofNat 187831937335081201858678154), (Int.negOfNat 10741936627340654788444110), (Int.negOfNat 2163886278524477181690491), (Int.ofNat 122762791315400972949856), (Int.ofNat 15661199277211601511695), (Int.negOfNat 854001348062372280647), (Int.negOfNat 78519048744265833903), (Int.ofNat 4296662307101535585), (Int.ofNat 209013685799394464), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-691626657122774369737285032362057/5629499534213120000000000000000000), (177324367392089684200872072584133/2814749767106560000000000000000000), (6725044403173467440658840287687/11258999068426240000000000000000000), (145217543475970422561090131309/11258999068426240000000000000000000), (174086263693758613344750027559/11258999068426240000000000000000000), (-10516096535464737527842556191/11258999068426240000000000000000000), (-8565926600407660869787090679/11258999068426240000000000000000000), (473177215263624174552597863/11258999068426240000000000000000000), (93915968667540600929339077/5629499534213120000000000000000000), (-1074193662734065478844411/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial131.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial131.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial131.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 65405432081383916848793275559463), (Int.ofNat 741395281638679956887828531436963), (Int.ofNat 9461806790379835475541846411889), (Int.ofNat 263953439092565300191058184783), (Int.negOfNat 167772685304958776391144103054), (Int.negOfNat 23646443441004380113457804356), (Int.ofNat 7112093452658630633460404573), (Int.ofNat 779249418327333324410085869), (Int.negOfNat 155093502467562582757171139), (Int.negOfNat 12625619858168957653253411), (Int.ofNat 1955984769927803610042242), (Int.ofNat 118807409275370380523949), (Int.negOfNat 15440019314352448716749), (Int.negOfNat 737020983160437948261), (Int.ofNat 82229835130022463580), (Int.ofNat 3827236986896159191), (Int.negOfNat 230580810175243374), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(65405432081383916848793275559463/11258999068426240000000000000000000), (741395281638679956887828531436963/11258999068426240000000000000000000), (9461806790379835475541846411889/11258999068426240000000000000000000), (263953439092565300191058184783/11258999068426240000000000000000000), (-83886342652479388195572051527/5629499534213120000000000000000000), (-5911610860251095028364451089/2814749767106560000000000000000000), (7112093452658630633460404573/11258999068426240000000000000000000), (779249418327333324410085869/11258999068426240000000000000000000), (-155093502467562582757171139/11258999068426240000000000000000000), (-12625619858168957653253411/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial131.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial131.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial131.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1585224728916718237742638822932849), (Int.ofNat 776687173351224451809577171544061), (Int.ofNat 7046469079326542544886469096005), (Int.negOfNat 762401131415456590153823355232), (Int.ofNat 45238216829100117878662953925), (Int.ofNat 49789476726085191187208939350), (Int.negOfNat 510990003525717204666386398), (Int.negOfNat 1448065248032927622659891461), (Int.negOfNat 8727447673951812510685312), (Int.ofNat 22837741097222671396975401), (Int.ofNat 261869257658628673415358), (Int.negOfNat 219226799080603955288759), (Int.negOfNat 2887021495448573050190), (Int.ofNat 1388494401740949933466), (Int.ofNat 18137660533802873821), (Int.negOfNat 6336032866624730849), (Int.ofNat 55494746208439687), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(1585224728916718237742638822932849/11258999068426240000000000000000000), (776687173351224451809577171544061/11258999068426240000000000000000000), (1409293815865308508977293819201/2251799813685248000000000000000000), (-23825035356733018442306979851/351843720888320000000000000000000), (1809528673164004715146518157/450359962737049600000000000000000), (995789534521703823744178787/225179981368524800000000000000000), (-255495001762858602333193199/5629499534213120000000000000000000), (-1448065248032927622659891461/11258999068426240000000000000000000), (-68183184952748535239729/87960930222080000000000000000000), (22837741097222671396975401/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial131.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial131.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial131.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3162794039429867937636257761922279), (Int.ofNat 800450730140471605277361376436985), (Int.ofNat 6531668627275509767732381991949), (Int.ofNat 800390992334619661633517088910), (Int.ofNat 183726195528741799027268391103), (Int.negOfNat 40054221911673759221550924428), (Int.negOfNat 8642723809419676879037089559), (Int.ofNat 872209028848652997660687436), (Int.ofNat 192964150802389891248038266), (Int.negOfNat 10111234621673493218535236), (Int.negOfNat 2428795751551353439443649), (Int.ofNat 69276291784373963891977), (Int.ofNat 19163728776904186747732), (Int.negOfNat 299112435945743445794), (Int.negOfNat 101516087953700921610), (Int.ofNat 501054704074774924), (Int.ofNat 252254895292924551), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(3162794039429867937636257761922279/11258999068426240000000000000000000), (160090146028094321055472275287397/2251799813685248000000000000000000), (6531668627275509767732381991949/11258999068426240000000000000000000), (80039099233461966163351708891/1125899906842624000000000000000000), (183726195528741799027268391103/11258999068426240000000000000000000), (-10013555477918439805387731107/2814749767106560000000000000000000), (-8642723809419676879037089559/11258999068426240000000000000000000), (218052257212163249415171859/2814749767106560000000000000000000), (96482075401194945624019133/5629499534213120000000000000000000), (-2527808655418373304633809/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial131.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial131.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial131.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4797483645705740586824085203866620), (Int.ofNat 837751431388971178459332692947338), (Int.ofNat 11325357404322639571576497492717), (Int.ofNat 32684915547815753899612937592), (Int.negOfNat 343306782866488552391963593636), (Int.negOfNat 20229495943768425194345052508), (Int.ofNat 12243241288116877863639757994), (Int.ofNat 949333170827780804897280172), (Int.negOfNat 213024772640894490225942142), (Int.negOfNat 18877029408309946257476432), (Int.ofNat 2099114086680081064078717), (Int.ofNat 205677374822143958237367), (Int.negOfNat 12946054309570444114375), (Int.negOfNat 1397996709720913251429), (Int.ofNat 53511207222008173276), (Int.ofNat 6514974081844533567), (Int.negOfNat 327227873255500897), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(239874182285287029341204260193331/562949953421312000000000000000000), (418875715694485589229666346473669/5629499534213120000000000000000000), (11325357404322639571576497492717/11258999068426240000000000000000000), (4085614443476969237451617199/1407374883553280000000000000000000), (-85826695716622138097990898409/2814749767106560000000000000000000), (-5057373985942106298586263127/2814749767106560000000000000000000), (6121620644058438931819878997/5629499534213120000000000000000000), (237333292706945201224320043/2814749767106560000000000000000000), (-106512386320447245112971071/5629499534213120000000000000000000), (-1179814338019371641092277/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial131.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial131.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial131.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 6513252555059644787273946065334415), (Int.ofNat 873367956090501055017654729060800), (Int.ofNat 4800249154421541278456713330974), (Int.negOfNat 1476513462675491045844010003760), (Int.ofNat 174925478187595204167782779210), (Int.ofNat 94251128103292999332510857812), (Int.negOfNat 1932911983254004181132685707), (Int.negOfNat 2524862373430390801914195356), (Int.negOfNat 48669626720571555384032841), (Int.ofNat 34745166428997573515488434), (Int.ofNat 1362554515152163664196129), (Int.negOfNat 280219176268035808291295), (Int.negOfNat 14370820382280130554322), (Int.ofNat 1460524016912538952848), (Int.ofNat 88555965055512869163), (Int.negOfNat 5154995713861624359), (Int.negOfNat 273928980410605728), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(1302650511011928957454789213066883/2251799813685248000000000000000000), (545854972556563159386034205663/7036874417766400000000000000000), (2400124577210770639228356665487/5629499534213120000000000000000000), (-18456418283443638073050125047/140737488355328000000000000000000), (17492547818759520416778277921/1125899906842624000000000000000000), (23562782025823249833127714453/2814749767106560000000000000000000), (-1932911983254004181132685707/11258999068426240000000000000000000), (-631215593357597700478548839/2814749767106560000000000000000000), (-48669626720571555384032841/11258999068426240000000000000000000), (17372583214498786757744217/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial131.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial131.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial131.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 8272751416975568459354161502383312), (Int.ofNat 886520007549450086324183712419593), (Int.ofNat 5598848854181887153229600055800), (Int.ofNat 2077276395586550518439863378138), (Int.ofNat 385346048929147555983167907486), (Int.negOfNat 90992432476739964735452755155), (Int.negOfNat 19425351302479239731974418061), (Int.ofNat 1352506116663562864305051812), (Int.ofNat 409983761656089178065089437), (Int.negOfNat 4731743927344714999767026), (Int.negOfNat 4499672725120611294972852), (Int.negOfNat 65795324894984454602778), (Int.ofNat 29484165185791151407091), (Int.ofNat 832627868231931410701), (Int.negOfNat 129568535155165226569), (Int.negOfNat 4867911726672140767), (Int.ofNat 598961000302562107), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(517046963560973028709635093898957/703687441776640000000000000000000), (886520007549450086324183712419593/11258999068426240000000000000000000), (27994244270909435766148000279/56294995342131200000000000000000), (1038638197793275259219931689069/5629499534213120000000000000000000), (192673024464573777991583953743/5629499534213120000000000000000000), (-18198486495347992947090551031/2251799813685248000000000000000000), (-19425351302479239731974418061/11258999068426240000000000000000000), (338126529165890716076262953/2814749767106560000000000000000000), (409983761656089178065089437/11258999068426240000000000000000000), (-2365871963672357499883513/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial131.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial131.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial131.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 10087086632023694679263075755721111), (Int.ofNat 936156549172904864104480197044004), (Int.ofNat 16939489966443174566247473575202), (Int.negOfNat 189484487718438538127140289366), (Int.negOfNat 930650253828150960610743760775), (Int.negOfNat 71463067327586735469545739160), (Int.ofNat 27975221614141128581630987873), (Int.ofNat 3340531757651440680295167953), (Int.negOfNat 331427506399192802804621285), (Int.negOfNat 56912817662021007976552067), (Int.ofNat 1453274593102833625791331), (Int.ofNat 487436971714035560418249), (Int.ofNat 762160317287408453366), (Int.negOfNat 2603031665309763724711), (Int.negOfNat 39164788657969156820), (Int.ofNat 10059595842237332254), (Int.ofNat 205025356512599835), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(10087086632023694679263075755721111/11258999068426240000000000000000000), (234039137293226216026120049261001/2814749767106560000000000000000000), (8469744983221587283123736787601/5629499534213120000000000000000000), (-94742243859219269063570144683/5629499534213120000000000000000000), (-37226010153126038424429750431/450359962737049600000000000000000), (-1786576683189668386738643479/281474976710656000000000000000000), (27975221614141128581630987873/11258999068426240000000000000000000), (3340531757651440680295167953/11258999068426240000000000000000000), (-66285501279838560560924257/2251799813685248000000000000000000), (-56912817662021007976552067/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial131.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial131.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial131.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 12010571077459669550164817900964640), (Int.ofNat 972552942843980293628824684428309), (Int.negOfNat 4117252767480353966298545396135), (Int.negOfNat 5004132964857941490238982986490), (Int.ofNat 407162696576351390803843101850), (Int.ofNat 306970561520906941360688712623), (Int.ofNat 10935684097827127398020268043), (Int.negOfNat 6456027250868903522065534481), (Int.negOfNat 551177781652018161400816225), (Int.ofNat 51702325300481789403228523), (Int.ofNat 6771945917530814180455315), (Int.negOfNat 199902537054666482679553), (Int.negOfNat 45088439168230105551490), (Int.ofNat 258589751544333307251), (Int.ofNat 197784386620723734096), (Int.ofNat 1342627310623636606), (Int.negOfNat 794565808412390365), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(75066069234122934688530111881029/70368744177664000000000000000000), (972552942843980293628824684428309/11258999068426240000000000000000000), (-823450553496070793259709079227/2251799813685248000000000000000000), (-500413296485794149023898298649/1125899906842624000000000000000000), (8143253931527027816076862037/225179981368524800000000000000000), (306970561520906941360688712623/11258999068426240000000000000000000), (10935684097827127398020268043/11258999068426240000000000000000000), (-6456027250868903522065534481/11258999068426240000000000000000000), (-22047111266080726456032649/450359962737049600000000000000000), (51702325300481789403228523/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial131.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial131.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial131.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 13915277777608586598287083813085484), (Int.ofNat 932414603758260627129751467059113), (Int.negOfNat 2206401799034167091303915720270), (Int.ofNat 8047284126881339562302702354910), (Int.ofNat 1993620977274775510715206014160), (Int.negOfNat 202388864890309345494030907523), (Int.negOfNat 89097080386167514019362372465), (Int.negOfNat 3412869689420095522250995836), (Int.ofNat 1025201491906814902852789781), (Int.ofNat 78957175673523895548881854), (Int.negOfNat 5962918157943126511215348), (Int.negOfNat 684353880794914222753130), (Int.ofNat 20221747059823628206399), (Int.ofNat 3613553937219877187903), (Int.negOfNat 36094012596197711097), (Int.negOfNat 13992858583052428253), (Int.negOfNat 38319328559679813), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(3478819444402146649571770953271371/2814749767106560000000000000000000), (932414603758260627129751467059113/11258999068426240000000000000000000), (-220640179903416709130391572027/1125899906842624000000000000000000), (804728412688133956230270235491/1125899906842624000000000000000000), (24920262215934693883940075177/140737488355328000000000000000000), (-202388864890309345494030907523/11258999068426240000000000000000000), (-17819416077233502803872474493/2251799813685248000000000000000000), (-853217422355023880562748959/2814749767106560000000000000000000), (1025201491906814902852789781/11258999068426240000000000000000000), (39478587836761947774440927/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial131.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial131.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial131.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 15855237563890887318931532429315797), (Int.ofNat 1050319729896235622025622255638668), (Int.ofNat 56171299585231183742083109860843), (Int.ofNat 1878378331158775078027934367397), (Int.negOfNat 4970353521104403973066833260125), (Int.negOfNat 1004924971906697971207538797619), (Int.ofNat 2779026055097267283532128565), (Int.ofNat 15893995535726237508245459020), (Int.ofNat 760980958648395431834554411), (Int.negOfNat 120382340715110905223257914), (Int.negOfNat 9205358744922508130335519), (Int.ofNat 556291970329807670642931), (Int.ofNat 59021274369178457392458), (Int.negOfNat 1705712029787571132800), (Int.negOfNat 254130555331396957129), (Int.ofNat 3385184734240745339), (Int.ofNat 906817602545758612), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(15855237563890887318931532429315797/11258999068426240000000000000000000), (262579932474058905506405563909667/2814749767106560000000000000000000), (56171299585231183742083109860843/11258999068426240000000000000000000), (1878378331158775078027934367397/11258999068426240000000000000000000), (-39762828168835231784534666081/90071992547409920000000000000000), (-1004924971906697971207538797619/11258999068426240000000000000000000), (555805211019453456706425713/2251799813685248000000000000000000), (794699776786311875412272951/562949953421312000000000000000000), (760980958648395431834554411/11258999068426240000000000000000000), (-60191170357555452611628957/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial131.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial131.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial131.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 18086243394486893467365050959355292), (Int.ofNat 1066216590874098876194637211491772), (Int.negOfNat 120170979540865874610495818890779), (Int.negOfNat 68131591659793415478338937394850), (Int.negOfNat 10129238000623641248274456246533), (Int.ofNat 409142825688551664429359901741), (Int.ofNat 209857782612598004123883102799), (Int.ofNat 6041890333019778425114413864), (Int.negOfNat 1974792027491412195414351262), (Int.negOfNat 111792027231219636301357780), (Int.ofNat 11359917322044942242189929), (Int.ofNat 878735530621595163629377), (Int.negOfNat 44664074067632673321011), (Int.negOfNat 4402077981314719999459), (Int.ofNat 126789352694643722888), (Int.ofNat 16362390442147526953), (Int.negOfNat 233413798487381397), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(4521560848621723366841262739838823/2814749767106560000000000000000000), (266554147718524719048659302872943/2814749767106560000000000000000000), (-120170979540865874610495818890779/11258999068426240000000000000000000), (-1362631833195868309566778747897/225179981368524800000000000000000), (-10129238000623641248274456246533/11258999068426240000000000000000000), (409142825688551664429359901741/11258999068426240000000000000000000), (209857782612598004123883102799/11258999068426240000000000000000000), (755236291627472303139301733/1407374883553280000000000000000000), (-987396013745706097707175631/5629499534213120000000000000000000), (-5589601361560981815067889/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial131.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial131.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial131.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 19057619378741846025518460845098265), (Int.negOfNat 482664164930261241893484528384813), (Int.negOfNat 688806812627554950435970890069725), (Int.negOfNat 99773492032465784647432658368838), (Int.ofNat 5765568908355967888430145396503), (Int.ofNat 2436661118326641731408129941252), (Int.ofNat 45830452519163915634786537348), (Int.negOfNat 27643596556304501786576560652), (Int.negOfNat 1281322616903582400066834574), (Int.ofNat 192324378300846285473036828), (Int.ofNat 12149390917393257498660243), (Int.negOfNat 918950973044961811437201), (Int.negOfNat 70514794223264842540404), (Int.ofNat 3220043397497030935302), (Int.ofNat 288543656573967770242), (Int.negOfNat 8151325462085351184), (Int.negOfNat 928491687663439789), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(3811523875748369205103692169019653/2251799813685248000000000000000000), (-482664164930261241893484528384813/11258999068426240000000000000000000), (-27552272505102198017438835602789/450359962737049600000000000000000), (-49886746016232892323716329184419/5629499534213120000000000000000000), (5765568908355967888430145396503/11258999068426240000000000000000000), (609165279581660432852032485313/2814749767106560000000000000000000), (11457613129790978908696634337/2814749767106560000000000000000000), (-6910899139076125446644140163/2814749767106560000000000000000000), (-640661308451791200033417287/5629499534213120000000000000000000), (48081094575211571368259207/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial131.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial131.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial131.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 14708273641429635791871535818816675), (Int.negOfNat 4060145745823024356386517880881970), (Int.negOfNat 963018378712636696987396219374560), (Int.ofNat 34548761625797022842621281429134), (Int.ofNat 24599150706997577744467269082819), (Int.ofNat 543233254430090854192069031390), (Int.negOfNat 331479551796196223339886261146), (Int.negOfNat 14964380044373805443654743683), (Int.ofNat 2774250143067864022288131860), (Int.ofNat 160450706614650839611741599), (Int.negOfNat 15913992953244465723592110), (Int.negOfNat 1057276362691325126206637), (Int.ofNat 66709735037434910526750), (Int.ofNat 4875521702788005833686), (Int.negOfNat 213419296655308137191), (Int.negOfNat 16934817511007338371), (Int.ofNat 505146925534442607), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(588330945657185431674861432752667/450359962737049600000000000000000), (-406014574582302435638651788088197/1125899906842624000000000000000000), (-6018864866953979356171226371091/70368744177664000000000000000000), (17274380812898511421310640714567/5629499534213120000000000000000000), (24599150706997577744467269082819/11258999068426240000000000000000000), (54323325443009085419206903139/1125899906842624000000000000000000), (-165739775898098111669943130573/5629499534213120000000000000000000), (-14964380044373805443654743683/11258999068426240000000000000000000), (138712507153393201114406593/562949953421312000000000000000000), (160450706614650839611741599/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial131.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial131.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial131.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 3400912678171426129881944994850406), (Int.negOfNat 6734231761859790814990107343544536), (Int.negOfNat 205995781948331225222924315561381), (Int.ofNat 197208211714256168774478413876526), (Int.ofNat 9458214865838690874450451232336), (Int.negOfNat 3276684282123646229366381138375), (Int.negOfNat 186729788600204922681131998571), (Int.ofNat 33777226480103936537242746575), (Int.ofNat 2078736730301923812910616845), (Int.negOfNat 235284188367074502766676957), (Int.negOfNat 15073093870523746990219514), (Int.ofNat 1180517167665344410428299), (Int.ofNat 77306676821165182336159), (Int.negOfNat 4471995522619766306303), (Int.negOfNat 296628648260640309808), (Int.ofNat 12880804672683124069), (Int.ofNat 950165772781120966), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(1700456339085713064940972497425203/5629499534213120000000000000000000), (-841778970232473851873763417943067/1407374883553280000000000000000000), (-205995781948331225222924315561381/11258999068426240000000000000000000), (98604105857128084387239206938263/5629499534213120000000000000000000), (591138429114918179653153202021/703687441776640000000000000000000), (-26213474256989169834931049107/90071992547409920000000000000000), (-186729788600204922681131998571/11258999068426240000000000000000000), (1351089059204157461489709863/450359962737049600000000000000000), (415747346060384762582123369/2251799813685248000000000000000000), (-235284188367074502766676957/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial131.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial131.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial131.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 9274619010676830155491019500970040), (Int.negOfNat 5170383851630601506626324743998439), (Int.ofNat 922503970471238528906814943050757), (Int.ofNat 133130796577021324831856727790343), (Int.negOfNat 23820091251564970473684976836862), (Int.negOfNat 2303749619406385649331153749704), (Int.ofNat 331068054364621799388088152862), (Int.ofNat 26283347523515768106727197625), (Int.negOfNat 2926723767467171386129150226), (Int.negOfNat 205808123151169652627464886), (Int.ofNat 17959490775329276311443273), (Int.ofNat 1158882714252195950308388), (Int.negOfNat 81091915132572871413781), (Int.negOfNat 4888147003805077400333), (Int.ofNat 281860386402648944833), (Int.ofNat 15744565563543059535), (Int.negOfNat 784104747620730876), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-231865475266920753887275487524251/281474976710656000000000000000000), (-5170383851630601506626324743998439/11258999068426240000000000000000000), (922503970471238528906814943050757/11258999068426240000000000000000000), (133130796577021324831856727790343/11258999068426240000000000000000000), (-11910045625782485236842488418431/5629499534213120000000000000000000), (-287968702425798206166394218713/1407374883553280000000000000000000), (165534027182310899694044076431/5629499534213120000000000000000000), (210266780188126144853817581/90071992547409920000000000000000), (-1463361883733585693064575113/5629499534213120000000000000000000), (-102904061575584826313732443/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial131.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial131.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial131.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial131.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial131.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial131.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial131.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial131.reflect := by
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

end Bin131
end
end ErdosOverlap.OuterNumerics
