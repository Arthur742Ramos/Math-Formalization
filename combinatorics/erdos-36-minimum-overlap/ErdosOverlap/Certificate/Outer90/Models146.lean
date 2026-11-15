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

/-! # Exact integer weighted outer models for source bin 146

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin146

def weightDenominator : ℤ := (Int.ofNat 50000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 12566155669580715000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 12407487081891194000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 10990225175510727500)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 7525486729409155000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 4862232057424530000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 2767004004365328250)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 1623581105660651750)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 2505734066613145500)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 861009381537529600)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial146.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial146.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 48779902185893155000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 11374638777868835000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 7440739790677063000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 4677834788492831000)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 1474977331751093850)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 243628439685948550)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 564174986525582050)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 548365970657612950)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 7040726392418461)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial146.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial146.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 48779902185893155000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 11374638777868835000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 7440739790677063000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 4677834788492831000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 1474977331751093850)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 243628439685948550)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 564174986525582050)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 548365970657612950)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 7040726392418461)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial146.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial146.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial146.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 43909653054748616662697131258436253), (Int.ofNat 24655051696422619578729715378247687), (Int.ofNat 4733018730878550692556633675522580), (Int.negOfNat 811540258434050401232530545405799), (Int.negOfNat 138754770525078039019205048260867), (Int.ofNat 16486340397108464196816518080399), (Int.ofNat 2182905409187913618361574682459), (Int.negOfNat 204417900081001568731784516359), (Int.negOfNat 21408506768019636283780554794), (Int.ofNat 1671177706961444675187300432), (Int.ofNat 142471672157546782782979939), (Int.negOfNat 9629363294800014236472704), (Int.negOfNat 683993317892137907160877), (Int.ofNat 41159261636876313602067), (Int.ofNat 2478270226791082359035), (Int.negOfNat 134618009362971595985), (Int.negOfNat 7316902586603895684), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-43909653054748616662697131258436253/56294995342131200000000000000000000), (24655051696422619578729715378247687/56294995342131200000000000000000000), (236650936543927534627831683776129/2814749767106560000000000000000000), (-811540258434050401232530545405799/56294995342131200000000000000000000), (-138754770525078039019205048260867/56294995342131200000000000000000000), (16486340397108464196816518080399/56294995342131200000000000000000000), (2182905409187913618361574682459/56294995342131200000000000000000000), (-204417900081001568731784516359/56294995342131200000000000000000000), (-10704253384009818141890277397/28147497671065600000000000000000000), (104448606685090292199206277/3518437208883200000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial146.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial146.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial146.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial146 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 16256729020071741361728224799459181), (Int.ofNat 31037471415185130487388384235054274), (Int.negOfNat 1790233613508925470812609867569969), (Int.negOfNat 1054995559220519868765404671378731), (Int.ofNat 84045193442794409795228500376725), (Int.ofNat 20098649225495103823643158395870), (Int.negOfNat 1647218016830554514277116046171), (Int.negOfNat 232356261569094473855700000167), (Int.ofNat 18231642656803993374880840917), (Int.ofNat 1776898059089037555928195267), (Int.negOfNat 131661764659514288216233914), (Int.negOfNat 9595954743544652120234985), (Int.ofNat 674133088183405606120625), (Int.ofNat 38495347979363170686789), (Int.negOfNat 2587024103437099320586), (Int.negOfNat 118126087747372364591), (Int.ofNat 8012596672287913594), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(16256729020071741361728224799459181/56294995342131200000000000000000000), (15518735707592565243694192117527137/28147497671065600000000000000000000), (-1790233613508925470812609867569969/56294995342131200000000000000000000), (-1054995559220519868765404671378731/56294995342131200000000000000000000), (3361807737711776391809140015069/2251799813685248000000000000000000), (2009864922549510382364315839587/5629499534213120000000000000000000), (-1647218016830554514277116046171/56294995342131200000000000000000000), (-232356261569094473855700000167/56294995342131200000000000000000000), (18231642656803993374880840917/56294995342131200000000000000000000), (1776898059089037555928195267/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial146.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial146.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial146.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial146 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 64588914867485412601572310377507504), (Int.ofNat 15115566188642986572535092774306815), (Int.negOfNat 5007583374419142343398051958944314), (Int.ofNat 67518717017298380458817028413177), (Int.ofNat 146644477109002477111584511010580), (Int.negOfNat 8703259313050296710061649385536), (Int.negOfNat 2202337602593939924620400253098), (Int.ofNat 158192757494011406651382110939), (Int.ofNat 20207950700701325997933448746), (Int.negOfNat 1531696331748703962271809921), (Int.negOfNat 125113786733639627096612714), (Int.ofNat 9691195478685405395998451), (Int.ofNat 558415878252053644971420), (Int.negOfNat 43921753315009752639350), (Int.negOfNat 1883916296543575476615), (Int.ofNat 150369379258197537079), (Int.ofNat 4726833715598888423), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(4036807179217838287598269398594219/3518437208883200000000000000000000), (3023113237728597314507018554861363/11258999068426240000000000000000000), (-2503791687209571171699025979472157/28147497671065600000000000000000000), (67518717017298380458817028413177/56294995342131200000000000000000000), (7332223855450123855579225550529/2814749767106560000000000000000000), (-135988426766410886094713271649/879609302220800000000000000000000), (-1101168801296969962310200126549/28147497671065600000000000000000000), (158192757494011406651382110939/56294995342131200000000000000000000), (10103975350350662998966724373/28147497671065600000000000000000000), (-1531696331748703962271809921/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial146.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial146.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial146.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial146 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 77281252525064500374281956924308013), (Int.negOfNat 443514946590407911462611871086528), (Int.negOfNat 2173503515417263128076974960990668), (Int.ofNat 655272876159921003312055402560024), (Int.negOfNat 12996266989004734461470550455577), (Int.negOfNat 16559521778534290011330962575950), (Int.ofNat 991585459134028957648104658851), (Int.ofNat 200785208321508763665508662226), (Int.negOfNat 14704210422028270829485455696), (Int.negOfNat 1489520878270359282382648868), (Int.ofNat 120765009289397114241809863), (Int.ofNat 7538775030877136418085591), (Int.negOfNat 663260693095158408796854), (Int.negOfNat 27827993155065483251172), (Int.ofNat 2651676041150311896414), (Int.ofNat 75534182761135189726), (Int.negOfNat 7991474493110658211), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(77281252525064500374281956924308013/56294995342131200000000000000000000), (-6929921040475123616603310485727/879609302220800000000000000000000), (-543375878854315782019243740247667/14073748835532800000000000000000000), (81909109519990125414006925320003/7036874417766400000000000000000000), (-12996266989004734461470550455577/56294995342131200000000000000000000), (-331190435570685800226619251519/1125899906842624000000000000000000), (991585459134028957648104658851/56294995342131200000000000000000000), (100392604160754381832754331113/28147497671065600000000000000000000), (-919013151376766926842840981/3518437208883200000000000000000000), (-372380219567589820595662217/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial146.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial146.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial146.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial146 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 72289317877865410498889667033199963), (Int.negOfNat 2752363795477748428476210492303796), (Int.ofNat 462711378538857304542599845813119), (Int.ofNat 127750265299501348099901115787852), (Int.negOfNat 83500801600018816621494137403318), (Int.ofNat 3738335374269575996655300695135), (Int.ofNat 1628809379746967303172902912258), (Int.negOfNat 111854576380516307508936178514), (Int.negOfNat 15679205073199989867508361258), (Int.ofNat 1281257660693636511318539606), (Int.ofNat 93508263420226918111495847), (Int.negOfNat 8814034245081334952312445), (Int.negOfNat 382646136382518885193187), (Int.ofNat 41901720246516720897655), (Int.ofNat 1138211585819996269508), (Int.negOfNat 149917723283453445107), (Int.negOfNat 2143805570986299623), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(72289317877865410498889667033199963/56294995342131200000000000000000000), (-688090948869437107119052623075949/14073748835532800000000000000000000), (462711378538857304542599845813119/56294995342131200000000000000000000), (31937566324875337024975278946963/14073748835532800000000000000000000), (-41750400800009408310747068701659/28147497671065600000000000000000000), (747667074853915199331060139027/11258999068426240000000000000000000), (814404689873483651586451456129/28147497671065600000000000000000000), (-55927288190258153754468089257/28147497671065600000000000000000000), (-7839602536599994933754180629/28147497671065600000000000000000000), (640628830346818255659269803/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial146.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial146.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial146.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial146 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 68527696862719492381171298197682821), (Int.negOfNat 1491584455118080216587093535195460), (Int.negOfNat 181374424055021104323222191266272), (Int.negOfNat 212927170928232678070517543158339), (Int.ofNat 8749193671514176662443702423579), (Int.ofNat 9916146328095131428835743454125), (Int.negOfNat 661278186095201827597122293309), (Int.negOfNat 139837075551126763601896475262), (Int.ofNat 11369268669474047384496368095), (Int.ofNat 1042634968211233622781249886), (Int.negOfNat 101809692743023914714179445), (Int.negOfNat 4872346419671426660057477), (Int.ofNat 588498632834634553034332), (Int.ofNat 15344096781948438845546), (Int.negOfNat 2427965882370036403957), (Int.negOfNat 32984654645331976631), (Int.ofNat 7970352313933402828), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(68527696862719492381171298197682821/56294995342131200000000000000000000), (-74579222755904010829354676759773/2814749767106560000000000000000000), (-5667950751719409510100693477071/1759218604441600000000000000000000), (-212927170928232678070517543158339/56294995342131200000000000000000000), (8749193671514176662443702423579/56294995342131200000000000000000000), (79329170624761051430685947633/450359962737049600000000000000000), (-661278186095201827597122293309/56294995342131200000000000000000000), (-69918537775563381800948237631/28147497671065600000000000000000000), (2273853733894809476899273619/11258999068426240000000000000000000), (521317484105616811390624943/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial146.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial146.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial146.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial146 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 63516028346545687699373611412203458), (Int.negOfNat 3875071508405989052849789897537255), (Int.negOfNat 684432929989963602575740280445418), (Int.ofNat 93877236142864936950206990031056), (Int.ofNat 44520607865831457240116096302992), (Int.negOfNat 3472987136214810805030931952140), (Int.negOfNat 1022818568181229358511886525497), (Int.ofNat 84270892346544943329403288646), (Int.ofNat 10203307304983042164921689961), (Int.negOfNat 1009345437750440578978940870), (Int.negOfNat 56791501705688849764039370), (Int.ofNat 7269491791905458381550744), (Int.ofNat 191866375408393920379295), (Int.negOfNat 35653777951720791305239), (Int.negOfNat 363260259552218204907), (Int.ofNat 130636380025082946307), (Int.negOfNat 439222573626289177), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(31758014173272843849686805706101729/28147497671065600000000000000000000), (-775014301681197810569957979507451/11258999068426240000000000000000000), (-342216464994981801287870140222709/28147497671065600000000000000000000), (5867327258929058559387936876941/3518437208883200000000000000000000), (2782537991614466077507256018937/3518437208883200000000000000000000), (-173649356810740540251546597607/2814749767106560000000000000000000), (-1022818568181229358511886525497/56294995342131200000000000000000000), (42135446173272471664701644323/28147497671065600000000000000000000), (10203307304983042164921689961/56294995342131200000000000000000000), (-100934543775044057897894087/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial146.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial146.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial146.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial146 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 54327744409437350094037462183994808), (Int.negOfNat 4490167147494378950114398275443489), (Int.ofNat 493830665256565080856204416522603), (Int.ofNat 206967305547057403511744855690487), (Int.negOfNat 21069481962139623641163715142138), (Int.negOfNat 6367122672767964250254536183988), (Int.ofNat 541669950215108268600151941127), (Int.ofNat 87031673184169298932427691723), (Int.negOfNat 8509376641091214279160421775), (Int.negOfNat 600511203627729361039311165), (Int.ofNat 77870985295178491282487767), (Int.ofNat 2235030086103655182621819), (Int.negOfNat 462576877225912910823808), (Int.negOfNat 3392215784654443640629), (Int.ofNat 1938186912581746600772), (Int.negOfNat 10272168869084321394), (Int.negOfNat 7088220753218617845), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(6790968051179668761754682772999351/7036874417766400000000000000000000), (-4490167147494378950114398275443489/56294995342131200000000000000000000), (493830665256565080856204416522603/56294995342131200000000000000000000), (206967305547057403511744855690487/56294995342131200000000000000000000), (-10534740981069811820581857571069/28147497671065600000000000000000000), (-1591780668191991062563634045997/14073748835532800000000000000000000), (541669950215108268600151941127/56294995342131200000000000000000000), (87031673184169298932427691723/56294995342131200000000000000000000), (-340375065643648571166416871/2251799813685248000000000000000000), (-120102240725545872207862233/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial146.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial146.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial146.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial146 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 48481015077613928026926470928983289), (Int.negOfNat 1081523872626561919813718503840843), (Int.ofNat 891996143768680440921963697150436), (Int.negOfNat 98106866620171048055950404215919), (Int.negOfNat 38740348922852963071881062528805), (Int.ofNat 3068683543862349748639066470249), (Int.ofNat 671532640947614455569185806627), (Int.negOfNat 60325398839060722626045544523), (Int.negOfNat 5807336145170835349713143775), (Int.ofNat 709155619859725088784440115), (Int.ofNat 24624022471019998289222817), (Int.negOfNat 5205389555070676503391219), (Int.negOfNat 24582422026433423236708), (Int.ofNat 25995032000927878206729), (Int.negOfNat 295600156858276447078), (Int.negOfNat 96118631174166220956), (Int.ofNat 2147159883916511455), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(48481015077613928026926470928983289/56294995342131200000000000000000000), (-1081523872626561919813718503840843/56294995342131200000000000000000000), (222999035942170110230490924287609/14073748835532800000000000000000000), (-98106866620171048055950404215919/56294995342131200000000000000000000), (-7748069784570592614376212505761/11258999068426240000000000000000000), (3068683543862349748639066470249/56294995342131200000000000000000000), (671532640947614455569185806627/56294995342131200000000000000000000), (-60325398839060722626045544523/56294995342131200000000000000000000), (-232293445806833413988525751/2251799813685248000000000000000000), (141831123971945017756888023/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial146.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial146.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial146.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial146 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 48613596771583736531733364257411022), (Int.ofNat 412645657658426824972112014630063), (Int.negOfNat 267289147612140096110594818952287), (Int.negOfNat 218050832525467544162078532656630), (Int.ofNat 11819359139720962636462263941714), (Int.ofNat 4937872952487860110599458162990), (Int.negOfNat 337301297410722137413064308847), (Int.negOfNat 53006289634654553887367826096), (Int.ofNat 5269671437722585662036625511), (Int.ofNat 265778775809347439097755820), (Int.negOfNat 49135953717710863197215670), (Int.negOfNat 161012622162829068995194), (Int.ofNat 297741266269821116645895), (Int.negOfNat 5913199621889869721561), (Int.negOfNat 1266280547905669606807), (Int.ofNat 41460647077110917093), (Int.ofNat 5352120537358721723), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(24306798385791868265866682128705511/28147497671065600000000000000000000), (412645657658426824972112014630063/56294995342131200000000000000000000), (-267289147612140096110594818952287/56294995342131200000000000000000000), (-21805083252546754416207853265663/5629499534213120000000000000000000), (5909679569860481318231131970857/28147497671065600000000000000000000), (493787295248786011059945816299/5629499534213120000000000000000000), (-337301297410722137413064308847/56294995342131200000000000000000000), (-3312893102165909617960489131/3518437208883200000000000000000000), (5269671437722585662036625511/56294995342131200000000000000000000), (13288938790467371954887791/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial146.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial146.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial146.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial146 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 46945510050483840941107848508872871), (Int.negOfNat 2582618283792503738492882935089680), (Int.negOfNat 1003356096893969760008638949736123), (Int.ofNat 508732834773478617035194427544), (Int.ofNat 32459122270223351296063711895685), (Int.negOfNat 1039545742405280645534856143675), (Int.negOfNat 462591511742465859634854726059), (Int.ofNat 27987643528959206850685788712), (Int.ofNat 2912563044246193277303799795), (Int.negOfNat 359284676238855188756290486), (Int.negOfNat 2370612707499650883371345), (Int.ofNat 2752484253685132197588827), (Int.negOfNat 90729379835721187846068), (Int.negOfNat 14029253873685578089796), (Int.ofNat 740453848321580577493), (Int.ofNat 49757840261417184031), (Int.negOfNat 2987047086276785672), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(46945510050483840941107848508872871/56294995342131200000000000000000000), (-32282728547406296731161036688621/703687441776640000000000000000000), (-1003356096893969760008638949736123/56294995342131200000000000000000000), (63591604346684827129399303443/7036874417766400000000000000000000), (6491824454044670259212742379137/11258999068426240000000000000000000), (-41581829696211225821394245747/2251799813685248000000000000000000), (-462591511742465859634854726059/56294995342131200000000000000000000), (3498455441119900856335723589/7036874417766400000000000000000000), (582512608849238655460759959/11258999068426240000000000000000000), (-179642338119427594378145243/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial146.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial146.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial146.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial146 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 38231540411144461301009441287021648), (Int.negOfNat 5708518072349399527936720568858886), (Int.negOfNat 393056822338221275172811086657015), (Int.ofNat 163612271142175109789959212710100), (Int.ofNat 4026792144934646543081072041171), (Int.negOfNat 3609841904248183781585330956624), (Int.ofNat 38951917028197620004184047808), (Int.ofNat 31655507294665986998348314064), (Int.negOfNat 1472642459163408606565801008), (Int.negOfNat 63129363469602557688517106), (Int.ofNat 16948195184053274102715097), (Int.negOfNat 1061973213183175947466255), (Int.negOfNat 110808847790079018720287), (Int.ofNat 11143908447458270274195), (Int.ofNat 480180587751419930858), (Int.negOfNat 58414336590578918043), (Int.negOfNat 2769092392746132923), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(2389471275696528831313090080438853/3518437208883200000000000000000000), (-2854259036174699763968360284429443/28147497671065600000000000000000000), (-78611364467644255034562217331403/11258999068426240000000000000000000), (1636122711421751097899592127101/562949953421312000000000000000000), (4026792144934646543081072041171/56294995342131200000000000000000000), (-225615119015511486349083184789/3518437208883200000000000000000000), (608623703565587812565375747/879609302220800000000000000000000), (1978469205916624187396769629/3518437208883200000000000000000000), (-92040153697713037910362563/3518437208883200000000000000000000), (-31564681734801278844258553/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial146.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial146.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial146.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial146 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 26506239211968289039579692794384179), (Int.negOfNat 5457248388640819840807177105208676), (Int.ofNat 424323307138070639017995620120861), (Int.ofNat 72620460745485321646967850270448), (Int.negOfNat 22601577194875217041571814673233), (Int.negOfNat 1172352633844971026904914161500), (Int.ofNat 312125831250135787133491193840), (Int.ofNat 8192626593489397793454540274), (Int.negOfNat 1336366368331609074809791746), (Int.negOfNat 14003834701565125816510482), (Int.negOfNat 8299362860116910658115287), (Int.negOfNat 158333907892380026972441), (Int.ofNat 139610463136526249233496), (Int.ofNat 1254316631812786032822), (Int.negOfNat 897530553230921937936), (Int.negOfNat 2762392697317318726), (Int.ofNat 2965924907099530289), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(26506239211968289039579692794384179/56294995342131200000000000000000000), (-1364312097160204960201794276302169/14073748835532800000000000000000000), (424323307138070639017995620120861/56294995342131200000000000000000000), (4538778796592832602935490641903/3518437208883200000000000000000000), (-22601577194875217041571814673233/56294995342131200000000000000000000), (-2344705267689942053809828323/112589990684262400000000000000000), (3901572890626697339168639923/703687441776640000000000000000000), (4096313296744698896727270137/28147497671065600000000000000000000), (-668183184165804537404895873/28147497671065600000000000000000000), (-7001917350782562908255241/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial146.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial146.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial146.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial146 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 17491526004024119703610294096704998), (Int.negOfNat 3643391441008678267057270055520528), (Int.ofNat 301685589577430745300605118638384), (Int.negOfNat 103147049413219875800913231548290), (Int.negOfNat 14957803384739976025924787558742), (Int.ofNat 2576466853507133333298698072625), (Int.ofNat 245368814103080804455170817102), (Int.negOfNat 20715385494724582058324186389), (Int.negOfNat 2299017534818353328222687904), (Int.negOfNat 8704622361756005199310029), (Int.ofNat 14887751280361162362446236), (Int.ofNat 1344818542767346016949999), (Int.negOfNat 74682193105153288394780), (Int.negOfNat 11717933838589907294850), (Int.ofNat 304276855014864091435), (Int.ofNat 59757338126172141821), (Int.ofNat 186064248133544123), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(8745763002012059851805147048352499/28147497671065600000000000000000000), (-227711965063042391691079378470033/3518437208883200000000000000000000), (18855349348589421581287819914899/3518437208883200000000000000000000), (-10314704941321987580091323154829/5629499534213120000000000000000000), (-7478901692369988012962393779371/28147497671065600000000000000000000), (20611734828057066666389584581/450359962737049600000000000000000), (122684407051540402227585408551/28147497671065600000000000000000000), (-20715385494724582058324186389/56294995342131200000000000000000000), (-71844297963073541506958997/1759218604441600000000000000000000), (-8704622361756005199310029/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial146.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial146.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial146.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial146 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 10441907803829617449303680349850402), (Int.negOfNat 3911401002993592126975662454051359), (Int.negOfNat 429056195138736150219291863317525), (Int.negOfNat 95985077230704454263551902566218), (Int.ofNat 17362296779317632464968871043731), (Int.ofNat 2882156593389052441134022689430), (Int.negOfNat 244700890711817115737888111621), (Int.negOfNat 40319588903717229785019051733), (Int.ofNat 1026132568242961196524592667), (Int.ofNat 354983919110290615518513633), (Int.ofNat 7457238828965749824228536), (Int.negOfNat 2225757385403560459794515), (Int.negOfNat 119780583711721049293825), (Int.ofNat 10577320851913222241361), (Int.ofNat 765859347098129253814), (Int.negOfNat 40746640470198466409), (Int.negOfNat 2944802727922274906), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(5220953901914808724651840174925201/28147497671065600000000000000000000), (-3911401002993592126975662454051359/56294995342131200000000000000000000), (-17162247805549446008771674532701/2251799813685248000000000000000000), (-47992538615352227131775951283109/28147497671065600000000000000000000), (17362296779317632464968871043731/56294995342131200000000000000000000), (288215659338905244113402268943/5629499534213120000000000000000000), (-244700890711817115737888111621/56294995342131200000000000000000000), (-40319588903717229785019051733/56294995342131200000000000000000000), (1026132568242961196524592667/56294995342131200000000000000000000), (354983919110290615518513633/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial146.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial146.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial146.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial146 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.ofNat 484651521245106945878285681735886), (Int.negOfNat 6056446983311967857415834048895210), (Int.negOfNat 440030318469884481777811899744738), (Int.ofNat 100226291829767236749418390142345), (Int.ofNat 22788448855556532630794683986666), (Int.negOfNat 2279435472713149681683450655038), (Int.negOfNat 467840001182510024685894403091), (Int.ofNat 21006656726102144772089197609), (Int.ofNat 5413981935422275503514947156), (Int.negOfNat 42358492705306385349245932), (Int.negOfNat 41629405094396654016663211), (Int.negOfNat 737207054763936541216896), (Int.ofNat 231929645536486341747973), (Int.ofNat 7804583409896730014083), (Int.negOfNat 973853359546263549915), (Int.negOfNat 42862990270234214665), (Int.ofNat 2389923170086626216), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(242325760622553472939142840867943/28147497671065600000000000000000000), (-605644698331196785741583404889521/5629499534213120000000000000000000), (-220015159234942240888905949872369/28147497671065600000000000000000000), (20045258365953447349883678028469/11258999068426240000000000000000000), (11394224427778266315397341993333/28147497671065600000000000000000000), (-1139717736356574840841725327519/28147497671065600000000000000000000), (-467840001182510024685894403091/56294995342131200000000000000000000), (21006656726102144772089197609/56294995342131200000000000000000000), (1353495483855568875878736789/14073748835532800000000000000000000), (-10589623176326596337311483/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial146.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial146.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial146.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial146 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 12320811895878067239774824141462008), (Int.negOfNat 6142160656201207934146799509285714), (Int.ofNat 436753103980727682292950836934991), (Int.ofNat 137096977494371870989598065026203), (Int.negOfNat 16861059030984767728475262355561), (Int.negOfNat 4121402326273846295499803776699), (Int.ofNat 267979364678842930508582611491), (Int.ofNat 63931381863122196250555344009), (Int.negOfNat 1867059195157241124020208656), (Int.negOfNat 610293710382485247265232182), (Int.ofNat 3482667249763537939017611), (Int.ofNat 4036456387986084099067304), (Int.ofNat 39243360654009048565427), (Int.negOfNat 19685642414633975800617), (Int.negOfNat 376762007405385482435), (Int.ofNat 75229392503715857885), (Int.ofNat 1208702512062378784), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-1540101486984758404971853017682751/7036874417766400000000000000000000), (-3071080328100603967073399754642857/28147497671065600000000000000000000), (436753103980727682292950836934991/56294995342131200000000000000000000), (137096977494371870989598065026203/56294995342131200000000000000000000), (-16861059030984767728475262355561/56294995342131200000000000000000000), (-4121402326273846295499803776699/56294995342131200000000000000000000), (267979364678842930508582611491/56294995342131200000000000000000000), (63931381863122196250555344009/56294995342131200000000000000000000), (-116691199697327570251263041/3518437208883200000000000000000000), (-305146855191242623632616091/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial146.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial146.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial146.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial146 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 22138451503936088501415354847400649), (Int.negOfNat 3542412083952549115821512339258739), (Int.ofNat 626229518776328477918487081572113), (Int.negOfNat 90373513429845866110606201796631), (Int.negOfNat 28432441482375952817756652023008), (Int.ofNat 2542569299978850157860082234380), (Int.ofNat 613072699064424758539911805721), (Int.negOfNat 30373384711993900911943790683), (Int.negOfNat 7405896009858987921079474467), (Int.ofNat 191896113223791488246988633), (Int.ofNat 58984943402595681843932464), (Int.negOfNat 588420115018826537404315), (Int.negOfNat 336233226405453507109675), (Int.negOfNat 225607373372691301089), (Int.ofNat 1436158699280010385536), (Int.ofNat 13900562132065487191), (Int.negOfNat 4097860480376848494), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-22138451503936088501415354847400649/56294995342131200000000000000000000), (-3542412083952549115821512339258739/56294995342131200000000000000000000), (626229518776328477918487081572113/56294995342131200000000000000000000), (-90373513429845866110606201796631/56294995342131200000000000000000000), (-888513796324248525554895375719/1759218604441600000000000000000000), (127128464998942507893004111719/2814749767106560000000000000000000), (613072699064424758539911805721/56294995342131200000000000000000000), (-30373384711993900911943790683/56294995342131200000000000000000000), (-7405896009858987921079474467/56294995342131200000000000000000000), (191896113223791488246988633/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial146.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial146.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial146.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial146 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 27781293509345789530827628656890149), (Int.negOfNat 2731160315887195184904852996605463), (Int.negOfNat 280004476676613198214159447968049), (Int.negOfNat 146443185875107894257537701344864), (Int.ofNat 18478866325145687256806047878309), (Int.ofNat 4842656420708306939914274257986), (Int.negOfNat 342011607762915809334996687902), (Int.negOfNat 75641870944238286889241648489), (Int.ofNat 3485591216250459978652876404), (Int.ofNat 736233131547407127219190021), (Int.negOfNat 21643646001606060923412736), (Int.negOfNat 4968578055059836781998601), (Int.ofNat 85515276984307862859930), (Int.ofNat 24586999814200654898950), (Int.negOfNat 213411698377701221335), (Int.negOfNat 92604343504602450729), (Int.ofNat 1381366358942628477), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-27781293509345789530827628656890149/56294995342131200000000000000000000), (-2731160315887195184904852996605463/56294995342131200000000000000000000), (-280004476676613198214159447968049/56294995342131200000000000000000000), (-4576349558597121695548053167027/1759218604441600000000000000000000), (18478866325145687256806047878309/56294995342131200000000000000000000), (2421328210354153469957137128993/28147497671065600000000000000000000), (-171005803881457904667498343951/28147497671065600000000000000000000), (-75641870944238286889241648489/56294995342131200000000000000000000), (871397804062614994663219101/14073748835532800000000000000000000), (736233131547407127219190021/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial146.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial146.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial146.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial146 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 35114884101346777558827839566654697), (Int.negOfNat 4724211894733628504873209372292429), (Int.negOfNat 451413367675189361114198996766703), (Int.ofNat 107691053176955525768247124432004), (Int.ofNat 31595970015884468726960913290371), (Int.negOfNat 2874776515720707872800007582000), (Int.negOfNat 651973994756766763771128585601), (Int.ofNat 43762454927419339867397781074), (Int.ofNat 7860717568972684813320857646), (Int.negOfNat 399055706291765423484257182), (Int.negOfNat 63600593899880456017692063), (Int.ofNat 2362090145894643728453309), (Int.ofNat 369081999598883915249604), (Int.negOfNat 9665445039502607202178), (Int.negOfNat 1593739881780562905214), (Int.ofNat 27067761748511035924), (Int.ofNat 4076738301199593111), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-35114884101346777558827839566654697/56294995342131200000000000000000000), (-4724211894733628504873209372292429/56294995342131200000000000000000000), (-451413367675189361114198996766703/56294995342131200000000000000000000), (26922763294238881442061781108001/14073748835532800000000000000000000), (31595970015884468726960913290371/56294995342131200000000000000000000), (-1437388257860353936400003791/28147497671065600000000000000000), (-651973994756766763771128585601/56294995342131200000000000000000000), (21881227463709669933698890537/28147497671065600000000000000000000), (3930358784486342406660428823/28147497671065600000000000000000000), (-199527853145882711742128591/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial146.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial146.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial146.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial146 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 45128265860320014559641080975205728), (Int.negOfNat 4555217930557781624179585569897372), (Int.ofNat 607592956367214986607111670948647), (Int.ofNat 176760470154735203955586462103296), (Int.negOfNat 17535040064673417962430248684982), (Int.negOfNat 4715617562659845459454336037696), (Int.ofNat 412748466027658651173484524292), (Int.ofNat 71152399860007873970876752364), (Int.negOfNat 5394595095276813482008332192), (Int.negOfNat 698494973788766512600399256), (Int.ofNat 43273111097521053111325503), (Int.ofNat 4817137361366874800562045), (Int.negOfNat 232481393148182951091263), (Int.negOfNat 24356673402789195025905), (Int.ofNat 888559633819869987192), (Int.ofNat 93776268635519010507), (Int.negOfNat 3964394503555217277), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-1410258308135000454988783780475179/1759218604441600000000000000000000), (-1138804482639445406044896392474343/14073748835532800000000000000000000), (607592956367214986607111670948647/56294995342131200000000000000000000), (690470586541934390451509617591/219902325555200000000000000000000), (-8767520032336708981215124342491/28147497671065600000000000000000000), (-73681524416560085303974000589/879609302220800000000000000000000), (103187116506914662793371131073/14073748835532800000000000000000000), (17788099965001968492719188091/14073748835532800000000000000000000), (-168581096727400421312760381/1759218604441600000000000000000000), (-87311871723595814075049907/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial146.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial146.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial146.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial146 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 50791868731684679470501122197094721), (Int.negOfNat 837831635872577323811108713094050), (Int.ofNat 1004668636024378386055148574085810), (Int.negOfNat 58846023751063201299588630829416), (Int.negOfNat 28114074698021372420375517768612), (Int.ofNat 2850185865009573764216125747786), (Int.ofNat 533711174876421093084979088459), (Int.negOfNat 56809891057053059020318017338), (Int.negOfNat 6427660103904480890249474345), (Int.ofNat 620573912448423636720038214), (Int.ofNat 53459674284956435552162295), (Int.negOfNat 4275062542704625955489373), (Int.negOfNat 321200338046085181298682), (Int.ofNat 20254063628996747068454), (Int.ofNat 1437341161547113566257), (Int.negOfNat 67993708758653597269), (Int.negOfNat 4055616122022337728), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-50791868731684679470501122197094721/56294995342131200000000000000000000), (-16756632717451546476222174261881/1125899906842624000000000000000000), (100466863602437838605514857408581/5629499534213120000000000000000000), (-7355752968882900162448578853677/7036874417766400000000000000000000), (-7028518674505343105093879442153/14073748835532800000000000000000000), (1425092932504786882108062873893/28147497671065600000000000000000000), (533711174876421093084979088459/56294995342131200000000000000000000), (-28404945528526529510159008669/28147497671065600000000000000000000), (-1285532020780896178049894869/11258999068426240000000000000000000), (310286956224211818360019107/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial146.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial146.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial146.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial146 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 49252641936324690343360404145502144), (Int.ofNat 1875143583243355374474980185817847), (Int.ofNat 286602704420331411602053799095560), (Int.negOfNat 123741869364120593678572441879332), (Int.ofNat 12312730257119374477592621965080), (Int.ofNat 3134193069286024121397754851901), (Int.negOfNat 461736654743229829639856556853), (Int.negOfNat 46967527839300896839464694946), (Int.ofNat 7216811087191364299650109139), (Int.ofNat 479238568033020292813715670), (Int.negOfNat 64757939765235294536836130), (Int.negOfNat 3515485002573033699755694), (Int.ofNat 378640834254274158666105), (Int.ofNat 18812394664216251363389), (Int.negOfNat 1563438323530748643393), (Int.negOfNat 76118506482809163457), (Int.ofNat 6547422648167806077), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-769572530255073286615006314773471/879609302220800000000000000000000), (1875143583243355374474980185817847/56294995342131200000000000000000000), (7165067610508285290051344977389/1407374883553280000000000000000000), (-30935467341030148419643110469833/14073748835532800000000000000000000), (307818256427984361939815549127/1407374883553280000000000000000000), (3134193069286024121397754851901/56294995342131200000000000000000000), (-461736654743229829639856556853/56294995342131200000000000000000000), (-23483763919650448419732347473/28147497671065600000000000000000000), (7216811087191364299650109139/56294995342131200000000000000000000), (47923856803302029281371567/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial146.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial146.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial146.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial146 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 45082122994947430966690315519804577), (Int.ofNat 2079833025609878370915910751507482), (Int.negOfNat 37662708047349524444107164219770), (Int.ofNat 14360629993806676762932655199284), (Int.ofNat 11848927306151720249189663210221), (Int.negOfNat 2735998610122448709853503579262), (Int.negOfNat 233336938149615535446595653177), (Int.ofNat 67666241733691636765025317527), (Int.ofNat 2975682404250342121659640725), (Int.negOfNat 823751455981683744156199785), (Int.negOfNat 28454911285098653079943767), (Int.ofNat 6050099772064679604985081), (Int.ofNat 195024801337715623699308), (Int.negOfNat 29984658324321396374171), (Int.negOfNat 955373498871151951422), (Int.ofNat 108003370061748591794), (Int.ofNat 3173484561307552745), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-45082122994947430966690315519804577/56294995342131200000000000000000000), (1039916512804939185457955375753741/28147497671065600000000000000000000), (-3766270804734952444410716421977/5629499534213120000000000000000000), (3590157498451669190733163799821/14073748835532800000000000000000000), (11848927306151720249189663210221/56294995342131200000000000000000000), (-1367999305061224354926751789631/28147497671065600000000000000000000), (-233336938149615535446595653177/56294995342131200000000000000000000), (67666241733691636765025317527/56294995342131200000000000000000000), (119027296170013684866385629/2251799813685248000000000000000000), (-164750291196336748831239957/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial146.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial146.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial146.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial146 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 40862140331777041446505359158918570), (Int.ofNat 2248384071425634094927203628917225), (Int.ofNat 104853565791948143092247427645531), (Int.ofNat 1006398570542620884697317896090), (Int.negOfNat 10667130340698679445458953454028), (Int.negOfNat 220960633777661787973962038799), (Int.ofNat 492050102564919850130156274073), (Int.ofNat 2705817368408057175497603273), (Int.negOfNat 8765430878500792617669839175), (Int.negOfNat 85249634411524690782363065), (Int.ofNat 83549241026358778058941683), (Int.ofNat 1172430130352446762463619), (Int.negOfNat 504392192308112322351542), (Int.negOfNat 8590342886031515723779), (Int.ofNat 2126267120891012157978), (Int.ofNat 41600757631892438106), (Int.negOfNat 8255359958458028355), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-4086214033177704144650535915891857/5629499534213120000000000000000000), (89935362857025363797088145156689/2251799813685248000000000000000000), (104853565791948143092247427645531/56294995342131200000000000000000000), (100639857054262088469731789609/5629499534213120000000000000000000), (-2666782585174669861364738363507/14073748835532800000000000000000000), (-220960633777661787973962038799/56294995342131200000000000000000000), (492050102564919850130156274073/56294995342131200000000000000000000), (2705817368408057175497603273/56294995342131200000000000000000000), (-350617235140031704706793567/2251799813685248000000000000000000), (-17049926882304938156472613/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial146.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial146.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial146.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial146 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 36086015754836332517352235014840786), (Int.ofNat 2407792081256432592013851578143379), (Int.negOfNat 58025312421350449935831595460744), (Int.negOfNat 27816607261641104039287709928996), (Int.ofNat 8350499692894092743348564771864), (Int.ofNat 2468844103080254070974343744971), (Int.negOfNat 241055235079031699815658889553), (Int.negOfNat 76183995952258460918137435954), (Int.ofNat 2357883105662073938232905139), (Int.ofNat 996913621622737048371286230), (Int.negOfNat 9036249421488402809709330), (Int.negOfNat 7499123665830715375013006), (Int.negOfNat 6500881626315318601295), (Int.ofNat 37591451360021296437461), (Int.ofNat 238417422243977897607), (Int.negOfNat 139191848269775187493), (Int.negOfNat 1437384345447656623), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-18043007877418166258676117507420393/28147497671065600000000000000000000), (2407792081256432592013851578143379/56294995342131200000000000000000000), (-7253164052668806241978949432593/7036874417766400000000000000000000), (-6954151815410276009821927482249/14073748835532800000000000000000000), (1043812461611761592918570596483/7036874417766400000000000000000000), (2468844103080254070974343744971/56294995342131200000000000000000000), (-241055235079031699815658889553/56294995342131200000000000000000000), (-38091997976129230459068717977/28147497671065600000000000000000000), (2357883105662073938232905139/56294995342131200000000000000000000), (99691362162273704837128623/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial146.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial146.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial146.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial146 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 31536544073117024217951305023680971), (Int.ofNat 2230784487732458415435656225866770), (Int.ofNat 72455028476482350234673130923135), (Int.ofNat 65648647013062228371875397062751), (Int.ofNat 3479073895449173329985363417609), (Int.negOfNat 4040224889735517622650742205175), (Int.negOfNat 507151020332545333311644565591), (Int.ofNat 60668380577098143457444957188), (Int.ofNat 10206358574171734714798894705), (Int.negOfNat 443356918761580184385636164), (Int.negOfNat 98826281211557042412721505), (Int.ofNat 1891326864623980039257823), (Int.ofNat 596122384618635575028918), (Int.negOfNat 4792454793889785609704), (Int.negOfNat 2514636117110398248543), (Int.ofNat 4760033280856598819), (Int.ofNat 9095247160818302572), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-31536544073117024217951305023680971/56294995342131200000000000000000000), (223078448773245841543565622586677/5629499534213120000000000000000000), (14491005695296470046934626184627/11258999068426240000000000000000000), (65648647013062228371875397062751/56294995342131200000000000000000000), (3479073895449173329985363417609/56294995342131200000000000000000000), (-161608995589420704906029688207/2251799813685248000000000000000000), (-507151020332545333311644565591/56294995342131200000000000000000000), (15167095144274535864361239297/14073748835532800000000000000000000), (2041271714834346942959778941/11258999068426240000000000000000000), (-110839229690395046096409041/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial146.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial146.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial146.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial146 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 26355989068077542848670220621700522), (Int.ofNat 3035266419927084369395408473873968), (Int.ofNat 160879791116714386406762844088499), (Int.negOfNat 100765488937782214902123101993552), (Int.negOfNat 41898639824405868402291204250321), (Int.negOfNat 2035905204429291845318417375087), (Int.ofNat 915629507718490759069250864681), (Int.ofNat 88769854009186808245998919286), (Int.negOfNat 8996305181883932224865026042), (Int.negOfNat 1157774839974010103533220544), (Int.ofNat 53275965750753203135107303), (Int.ofNat 8531055174497650600022355), (Int.negOfNat 214289158453750865631763), (Int.negOfNat 42152425892719922395695), (Int.ofNat 619505228324023249442), (Int.ofNat 152898375571921884943), (Int.negOfNat 1145643799164932177), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-13177994534038771424335110310850261/28147497671065600000000000000000000), (189704151245442773087213029617123/3518437208883200000000000000000000), (160879791116714386406762844088499/56294995342131200000000000000000000), (-6297843058611388431382693874597/3518437208883200000000000000000000), (-41898639824405868402291204250321/56294995342131200000000000000000000), (-2035905204429291845318417375087/56294995342131200000000000000000000), (915629507718490759069250864681/56294995342131200000000000000000000), (44384927004593404122999459643/28147497671065600000000000000000000), (-4498152590941966112432513021/28147497671065600000000000000000000), (-18090231874593907867706571/879609302220800000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial146.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial146.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial146.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial146 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 21116450365815818528636298297749895), (Int.ofNat 1170022320367734610164601269825619), (Int.negOfNat 1353371779837196636527371901582701), (Int.negOfNat 342381626815751776343566772521870), (Int.ofNat 3826468969515216366551258128689), (Int.ofNat 10691233921459922860892834834200), (Int.ofNat 656843532991263997379931845760), (Int.negOfNat 135253732554228434421881211974), (Int.negOfNat 12183246823175171543643246454), (Int.ofNat 1009344292060938829032045182), (Int.ofNat 110849293615846920959115987), (Int.negOfNat 5127190844061639374328909), (Int.negOfNat 644928844735278766085996), (Int.ofNat 19124791277391071596828), (Int.ofNat 2664337704229438766236), (Int.negOfNat 53379061950617115874), (Int.negOfNat 9074124981641047189), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-4223290073163163705727259659549979/11258999068426240000000000000000000), (1170022320367734610164601269825619/56294995342131200000000000000000000), (-1353371779837196636527371901582701/56294995342131200000000000000000000), (-34238162681575177634356677252187/5629499534213120000000000000000000), (3826468969515216366551258128689/56294995342131200000000000000000000), (53456169607299614304464174171/281474976710656000000000000000000), (1026318020298849995906143509/87960930222080000000000000000000), (-67626866277114217210940605987/28147497671065600000000000000000000), (-6091623411587585771821623227/28147497671065600000000000000000000), (504672146030469414516022591/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial146.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial146.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial146.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial146 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 26503378922962796006828302738901903), (Int.negOfNat 7318433177170682383740372556886420), (Int.negOfNat 2409863951137746129198698081503532), (Int.ofNat 130247090272710904674614599484442), (Int.ofNat 103903852209151948439989303652753), (Int.ofNat 4474488113578696180139298277836), (Int.negOfNat 1658392873948323001531187286102), (Int.negOfNat 118705619323654554429999932911), (Int.ofNat 15291789106907821754246511004), (Int.ofNat 1324309519258486866150063129), (Int.negOfNat 94776852564866934970926286), (Int.negOfNat 9062978909923573210917899), (Int.ofNat 427000542627500766207430), (Int.ofNat 43051781142766470793950), (Int.negOfNat 1468026947425812121735), (Int.negOfNat 152617796001854456971), (Int.ofNat 3728671943777520977), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-26503378922962796006828302738901903/56294995342131200000000000000000000), (-365921658858534119187018627844321/2814749767106560000000000000000000), (-602465987784436532299674520375883/14073748835532800000000000000000000), (65123545136355452337307299742221/28147497671065600000000000000000000), (103903852209151948439989303652753/56294995342131200000000000000000000), (1118622028394674045034824569459/14073748835532800000000000000000000), (-829196436974161500765593643051/28147497671065600000000000000000000), (-118705619323654554429999932911/56294995342131200000000000000000000), (3822947276726955438561627751/14073748835532800000000000000000000), (1324309519258486866150063129/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial146.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial146.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial146.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial146 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 48048931362974824878352290793627034), (Int.negOfNat 12065497886687168523837563457277456), (Int.ofNat 777678954757209189121428891994881), (Int.ofNat 841382556537524455504901011529656), (Int.ofNat 36785362162592424012678068225502), (Int.negOfNat 16853679533948566840248649208991), (Int.negOfNat 1136861455810675386866434212929), (Int.ofNat 192510673154049807258573921133), (Int.ofNat 14871705078983131166893444633), (Int.negOfNat 1455641749415332048210835983), (Int.negOfNat 118098607487953259358643336), (Int.ofNat 7861158978824428030169965), (Int.ofNat 642230262816112875806875), (Int.negOfNat 31873911275313542307161), (Int.negOfNat 2556430822687494858264), (Int.ofNat 98511676223793552759), (Int.ofNat 9053002802463791806), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-24024465681487412439176145396813517/28147497671065600000000000000000000), (-754093617917948032739847716079841/3518437208883200000000000000000000), (777678954757209189121428891994881/56294995342131200000000000000000000), (105172819567190556938112626441207/7036874417766400000000000000000000), (18392681081296212006339034112751/28147497671065600000000000000000000), (-16853679533948566840248649208991/56294995342131200000000000000000000), (-1136861455810675386866434212929/56294995342131200000000000000000000), (192510673154049807258573921133/56294995342131200000000000000000000), (14871705078983131166893444633/56294995342131200000000000000000000), (-1455641749415332048210835983/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial146.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial146.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial146.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial146 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 62334061216566285029130997253946886), (Int.ofNat 849985751502135389179712725850883), (Int.ofNat 5235889879366695032244440171071117), (Int.ofNat 404830363407676714826300833119109), (Int.negOfNat 136460731067499265172985212418638), (Int.negOfNat 11264721934836652391725090355512), (Int.ofNat 1994462744127678415071093693602), (Int.ofNat 160836380767879156886598046791), (Int.negOfNat 18823704650460202541439625956), (Int.negOfNat 1444575930354436651295503068), (Int.ofNat 123377705812519055490906161), (Int.ofNat 8907605141508190059533246), (Int.negOfNat 592158552771172385186523), (Int.negOfNat 39905445446825984809883), (Int.ofNat 2164897732337467589565), (Int.ofNat 134099867040255878065), (Int.negOfNat 6304659361997691316), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-31167030608283142514565498626973443/28147497671065600000000000000000000), (849985751502135389179712725850883/56294995342131200000000000000000000), (5235889879366695032244440171071117/56294995342131200000000000000000000), (404830363407676714826300833119109/56294995342131200000000000000000000), (-68230365533749632586492606209319/28147497671065600000000000000000000), (-1408090241854581548965636294439/7036874417766400000000000000000000), (997231372063839207535546846801/28147497671065600000000000000000000), (160836380767879156886598046791/56294995342131200000000000000000000), (-4705926162615050635359906489/14073748835532800000000000000000000), (-361143982588609162823875767/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial146.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial146.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial146.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial146.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial146 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial146 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial146 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 70383300943321655609647312433794547), (Int.negOfNat 1257809974305134043600212733955287), (Int.ofNat 5570300514111663678610083507193920), (Int.negOfNat 539052850675150957477625459934101), (Int.negOfNat 143899869562485520970983793385933), (Int.ofNat 15273123799129268534655743020001), (Int.ofNat 2097737650788716692800692102641), (Int.negOfNat 211741097828529155997858625041), (Int.negOfNat 19684613891940099933641662206), (Int.ofNat 1812354296201828539129069068), (Int.ofNat 128056539767061599481722661), (Int.negOfNat 10629838771682339377376496), (Int.negOfNat 609897710802159896070023), (Int.ofNat 45571304762073786973133), (Int.ofNat 2213605165507287142065), (Int.negOfNat 148712096991201743815), (Int.negOfNat 6304659361997691316), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-70383300943321655609647312433794547/56294995342131200000000000000000000), (-1257809974305134043600212733955287/56294995342131200000000000000000000), (17407189106598948995656510959981/175921860444160000000000000000000), (-539052850675150957477625459934101/56294995342131200000000000000000000), (-143899869562485520970983793385933/56294995342131200000000000000000000), (15273123799129268534655743020001/56294995342131200000000000000000000), (2097737650788716692800692102641/56294995342131200000000000000000000), (-211741097828529155997858625041/56294995342131200000000000000000000), (-9842306945970049966820831103/28147497671065600000000000000000000), (453088574050457134782267267/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial146.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial146.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial146.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 56640651312667272343566039548436681), (Int.ofNat 11464259756383869760583724466224426), (Int.ofNat 439622586679049263399632831113069), (Int.negOfNat 886331515330894488397982807138669), (Int.ofNat 61882053467036119438573306794675), (Int.ofNat 18168020430480436896539072326130), (Int.negOfNat 1605070767426826786872441009429), (Int.negOfNat 208660395066122604315600365133), (Int.ofNat 19290453987752907012244119883), (Int.ofNat 1570410157403212469491452733), (Int.negOfNat 143562128739408557771527086), (Int.negOfNat 8394474875908257006049215), (Int.ofNat 741469751551563028669375), (Int.ofNat 33622508126110064241911), (Int.negOfNat 2837310353966787611014), (Int.negOfNat 103382419540775508009), (Int.ofNat 9053002802463791806), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-56640651312667272343566039548436681/56294995342131200000000000000000000), (5732129878191934880291862233112213/28147497671065600000000000000000000), (439622586679049263399632831113069/56294995342131200000000000000000000), (-886331515330894488397982807138669/56294995342131200000000000000000000), (2475282138681444777542932271787/2251799813685248000000000000000000), (1816802043048043689653907232613/5629499534213120000000000000000000), (-1605070767426826786872441009429/56294995342131200000000000000000000), (-208660395066122604315600365133/56294995342131200000000000000000000), (19290453987752907012244119883/56294995342131200000000000000000000), (1570410157403212469491452733/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial146.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial146.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial146.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 37596655656322242165672437529989704), (Int.ofNat 5641347543206131939314507832578685), (Int.negOfNat 2425223284482309432980040024355586), (Int.ofNat 2327005661011249844467529784123), (Int.ofNat 114589381014583001660259975235520), (Int.negOfNat 8135027897051212173349243154964), (Int.negOfNat 1868084412634067756887387375602), (Int.ofNat 165102430422724166829661095661), (Int.ofNat 17291683195277919267291677254), (Int.negOfNat 1659863848702897120009778379), (Int.negOfNat 106347851610419537509783286), (Int.ofNat 10635239631777340121811149), (Int.ofNat 472171466535144316888680), (Int.negOfNat 48225695382999095476950), (Int.negOfNat 1596289854773003609985), (Int.ofNat 163982863741479019221), (Int.ofNat 3728671943777520977), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-4699581957040280270709054691248713/7036874417766400000000000000000000), (1128269508641226387862901566515737/11258999068426240000000000000000000), (-1212611642241154716490020012177793/28147497671065600000000000000000000), (2327005661011249844467529784123/56294995342131200000000000000000000), (358091815670571880188312422611/175921860444160000000000000000000), (-2033756974262803043337310788741/14073748835532800000000000000000000), (-934042206317033878443693687801/28147497671065600000000000000000000), (165102430422724166829661095661/56294995342131200000000000000000000), (8645841597638959633645838627/28147497671065600000000000000000000), (-1659863848702897120009778379/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial146.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial146.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial146.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 34518061530485401732245630172501513), (Int.negOfNat 1286803337207338022886468028370472), (Int.negOfNat 626873597498298391509960601004732), (Int.ofNat 408121985437516427906205826039176), (Int.negOfNat 20882222927156855030138416478123), (Int.negOfNat 12795298768522167690372090504050), (Int.ofNat 1081040549105727932493127189049), (Int.ofNat 163065426957685295540261772474), (Int.negOfNat 16099373577102224372872389704), (Int.negOfNat 1213937222896487296637240932), (Int.ofNat 133213675269876875498801737), (Int.ofNat 6093100262774848063545409), (Int.negOfNat 731729682140219852435746), (Int.negOfNat 22310411081988291989828), (Int.ofNat 2909498451184197180486), (Int.ofNat 59873386373259722874), (Int.negOfNat 9074124981641047189), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-34518061530485401732245630172501513/56294995342131200000000000000000000), (-160850417150917252860808503546309/7036874417766400000000000000000000), (-156718399374574597877490150251183/14073748835532800000000000000000000), (51015248179689553488275728254897/7036874417766400000000000000000000), (-20882222927156855030138416478123/56294995342131200000000000000000000), (-255905975370443353807441810081/1125899906842624000000000000000000), (1081040549105727932493127189049/56294995342131200000000000000000000), (81532713478842647770130886237/28147497671065600000000000000000000), (-2012421697137778046609048713/7036874417766400000000000000000000), (-303484305724121824159310233/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial146.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial146.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial146.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 36992290085811396253306096745273663), (Int.negOfNat 326626649973735233254705082707904), (Int.ofNat 633301169374171693938709829725981), (Int.negOfNat 39624001359952648669653474317252), (Int.negOfNat 59290387339569087989177304801682), (Int.ofNat 5390827999527666410128080350865), (Int.ofNat 1236891429507035329344973706742), (Int.negOfNat 128941083003682260263716543786), (Int.negOfNat 12061831995129011005106494542), (Int.ofNat 1441024242816406904697541794), (Int.ofNat 71044532465036518355685053), (Int.negOfNat 9842829884683777801368355), (Int.negOfNat 283726631157201967415513), (Int.ofNat 46444581917287791518945), (Int.ofNat 815958542108962111192), (Int.negOfNat 164263443311546447193), (Int.negOfNat 1145643799164932177), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-36992290085811396253306096745273663/56294995342131200000000000000000000), (-5103541405839613019604766917311/879609302220800000000000000000000), (633301169374171693938709829725981/56294995342131200000000000000000000), (-9906000339988162167413368579313/14073748835532800000000000000000000), (-29645193669784543994588652400841/28147497671065600000000000000000000), (1078165599905533282025616070173/11258999068426240000000000000000000), (618445714753517664672486853371/28147497671065600000000000000000000), (-64470541501841130131858271893/28147497671065600000000000000000000), (-6030915997564505502553247271/28147497671065600000000000000000000), (720512121408203452348770897/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial146.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial146.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial146.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 36145112034499576361029026022257521), (Int.ofNat 435998641313677521332376763571360), (Int.negOfNat 400385257019243784701487094334728), (Int.negOfNat 185828785705926325044558959078561), (Int.ofNat 25549337790891782666173653682621), (Int.ofNat 7172621277604830299724482103375), (Int.negOfNat 864015516613014203381212669591), (Int.negOfNat 100190278395360156088658303938), (Int.ofNat 13360806722956820820896504705), (Int.ofNat 728986302451295634137698414), (Int.negOfNat 116457457641007676943626755), (Int.negOfNat 3229332622844671236112823), (Int.ofNat 663864417584103624315168), (Int.ofNat 9191920846722279407954), (Int.negOfNat 2702971525367033851543), (Int.negOfNat 16125101020481161069), (Int.ofNat 9095247160818302572), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-36145112034499576361029026022257521/56294995342131200000000000000000000), (2724991508210484508327354772321/351843720888320000000000000000000), (-50048157127405473087685886791841/7036874417766400000000000000000000), (-185828785705926325044558959078561/56294995342131200000000000000000000), (25549337790891782666173653682621/56294995342131200000000000000000000), (57380970220838642397795856827/450359962737049600000000000000000), (-864015516613014203381212669591/56294995342131200000000000000000000), (-50095139197680078044329151969/28147497671065600000000000000000000), (2672161344591364164179300941/11258999068426240000000000000000000), (364493151225647817068849207/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial146.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial146.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial146.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 37787423637108601435711325909039358), (Int.negOfNat 2200130619333728750636043647995845), (Int.negOfNat 577141216129954400211369144265682), (Int.ofNat 137133595019121214243095296758744), (Int.ofNat 33667859311887865500376741214908), (Int.negOfNat 5123285816680763679934278066860), (Int.negOfNat 680204145453402907284629392803), (Int.ofNat 106375090034960076729221403454), (Int.ofNat 6387867051205648803409870139), (Int.negOfNat 1203594122472736802157512730), (Int.negOfNat 31971636718604248132927830), (Int.ofNat 8442537440320543936854756), (Int.ofNat 82374562798712844831705), (Int.negOfNat 40656618812217585281961), (Int.negOfNat 11614068027762471893), (Int.ofNat 145686172692417794493), (Int.negOfNat 1437384345447656623), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-18893711818554300717855662954519679/28147497671065600000000000000000000), (-440026123866745750127208729599169/11258999068426240000000000000000000), (-288570608064977200105684572132841/28147497671065600000000000000000000), (17141699377390151780386912094843/7036874417766400000000000000000000), (8416964827971966375094185303727/14073748835532800000000000000000000), (-256164290834038183996713903343/2814749767106560000000000000000000), (-680204145453402907284629392803/56294995342131200000000000000000000), (53187545017480038364610701727/28147497671065600000000000000000000), (6387867051205648803409870139/56294995342131200000000000000000000), (-120359412247273680215751273/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial146.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial146.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial146.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 43053353817277533879175786506237208), (Int.negOfNat 2274827477623369855812813923311211), (Int.ofNat 557830688712640283115168417142197), (Int.ofNat 157122107044061238017147667658613), (Int.negOfNat 26367862848088701885016996214662), (Int.negOfNat 3927735882706525253218107447712), (Int.ofNat 729343611242347125304964721073), (Int.ofNat 46987535729642083265104494477), (Int.negOfNat 10801391437109104014358190425), (Int.negOfNat 264165451756268017325945435), (Int.ofNat 94765310683798727351544433), (Int.ofNat 443335732080995553823881), (Int.negOfNat 547183447302930155453792), (Int.ofNat 3311049549221970336529), (Int.ofNat 2244788541604239735728), (Int.negOfNat 28612108786607224106), (Int.negOfNat 8255359958458028355), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-5381669227159691734896973313279651/7036874417766400000000000000000000), (-2274827477623369855812813923311211/56294995342131200000000000000000000), (557830688712640283115168417142197/56294995342131200000000000000000000), (157122107044061238017147667658613/56294995342131200000000000000000000), (-13183931424044350942508498107331/28147497671065600000000000000000000), (-122741746334578914163065857741/1759218604441600000000000000000000), (729343611242347125304964721073/56294995342131200000000000000000000), (46987535729642083265104494477/56294995342131200000000000000000000), (-432055657484364160574327617/2251799813685248000000000000000000), (-52833090351253603465189087/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial146.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial146.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial146.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 44612394759431689740249953824671889), (Int.ofNat 833862375502049395265898938034043), (Int.ofNat 740629004316254258064155078709564), (Int.negOfNat 87283229918264857782265885253781), (Int.negOfNat 20664345195163828533143201753295), (Int.ofNat 4124836482333921271702446840551), (Int.ofNat 294833674055287098484153742173), (Int.negOfNat 83158325999586615856360884277), (Int.negOfNat 1722083093601035739658226025), (Int.ofNat 929641646124844082408841785), (Int.negOfNat 2111427326185558653342517), (Int.negOfNat 6533350188427282627683081), (Int.ofNat 93649715632053471842308), (Int.ofNat 31558347159214440364171), (Int.negOfNat 672870386486198546922), (Int.negOfNat 112874113378730547044), (Int.ofNat 3173484561307552745), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-44612394759431689740249953824671889/56294995342131200000000000000000000), (833862375502049395265898938034043/56294995342131200000000000000000000), (185157251079063564516038769677391/14073748835532800000000000000000000), (-87283229918264857782265885253781/56294995342131200000000000000000000), (-4132869039032765706628640350659/11258999068426240000000000000000000), (4124836482333921271702446840551/56294995342131200000000000000000000), (294833674055287098484153742173/56294995342131200000000000000000000), (-83158325999586615856360884277/56294995342131200000000000000000000), (-68883323744041429586329041/2251799813685248000000000000000000), (185928329224968816481768357/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial146.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial146.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial146.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 40870809288297395853039686049825522), (Int.ofNat 2437358599631730820617901269100337), (Int.ofNat 66850488753404194102804491926587), (Int.negOfNat 85377329200723735012257713336370), (Int.ofNat 16527389541943387493133926353986), (Int.ofNat 1588891911089463467543814476510), (Int.negOfNat 529523513297225472175562136353), (Int.negOfNat 7984255056506458122759047304), (Int.ofNat 7840305338149692654555975889), (Int.negOfNat 97111275049894396162804920), (Int.negOfNat 68318905581863735337701130), (Int.ofNat 1757407420004098166829194), (Int.ofNat 392469620625275845384105), (Int.negOfNat 13079683455419511693639), (Int.negOfNat 1602404270066604285393), (Int.ofNat 61506276531863297707), (Int.ofNat 6547422648167806077), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-20435404644148697926519843024912761/28147497671065600000000000000000000), (2437358599631730820617901269100337/56294995342131200000000000000000000), (66850488753404194102804491926587/56294995342131200000000000000000000), (-8537732920072373501225771333637/5629499534213120000000000000000000), (8263694770971693746566963176993/28147497671065600000000000000000000), (158889191108946346754381447651/5629499534213120000000000000000000), (-529523513297225472175562136353/56294995342131200000000000000000000), (-998031882063307265344880913/7036874417766400000000000000000000), (7840305338149692654555975889/56294995342131200000000000000000000), (-2427781876247359904070123/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial146.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial146.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial146.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 36129444969094927826145955020894971), (Int.ofNat 2238458474697658544543689818330480), (Int.negOfNat 41207155642309408662726497024977), (Int.ofNat 33794444981428543372492393478956), (Int.ofNat 5998426558277155928693486545815), (Int.negOfNat 2584288536057254654505107395025), (Int.negOfNat 12723632877215966632113817541), (Int.ofNat 55100061578263423482025815588), (Int.negOfNat 1560292378743675486110811595), (Int.negOfNat 613206471391569900872926214), (Int.ofNat 26130235603324168418002545), (Int.ofNat 4251070482783015849419373), (Int.negOfNat 215968939863896938216432), (Int.negOfNat 20188681641262448554204), (Int.ofNat 1143472981422535599507), (Int.ofNat 67993708758653597269), (Int.negOfNat 4055616122022337728), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-36129444969094927826145955020894971/56294995342131200000000000000000000), (27980730933720731806796122729131/703687441776640000000000000000000), (-41207155642309408662726497024977/56294995342131200000000000000000000), (8448611245357135843123098369739/14073748835532800000000000000000000), (1199685311655431185738697309163/11258999068426240000000000000000000), (-103371541442290186180204295801/2251799813685248000000000000000000), (-12723632877215966632113817541/56294995342131200000000000000000000), (13775015394565855870506453897/14073748835532800000000000000000000), (-312058475748735097222162319/11258999068426240000000000000000000), (-306603235695784950436463107/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial146.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial146.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial146.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 31528163957566528536997659313601648), (Int.ofNat 2483776515718293321004824442520386), (Int.ofNat 127533924568297950093107644054115), (Int.ofNat 1689572872748146612231143217400), (Int.negOfNat 8902508723942732120049833837471), (Int.ofNat 265403586253535358895673061624), (Int.ofNat 306305951932838522653959229892), (Int.negOfNat 17738363760899478613852573864), (Int.negOfNat 4564230268875627360245641692), (Int.ofNat 321904867304437031923581506), (Int.ofNat 38919931726534196427423503), (Int.negOfNat 3073301944509309657001545), (Int.negOfNat 216280272014859527462013), (Int.ofNat 18653625397402219531905), (Int.ofNat 844722943967032389942), (Int.negOfNat 79164038684573144757), (Int.negOfNat 3964394503555217277), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-1970510247347908033562353707100103/3518437208883200000000000000000000), (1241888257859146660502412221260193/28147497671065600000000000000000000), (25506784913659590018621528810823/11258999068426240000000000000000000), (8447864363740733061155716087/281474976710656000000000000000000), (-8902508723942732120049833837471/56294995342131200000000000000000000), (33175448281691919861959132703/7036874417766400000000000000000000), (76576487983209630663489807473/14073748835532800000000000000000000), (-2217295470112434826731571733/7036874417766400000000000000000000), (-1141057567218906840061410423/14073748835532800000000000000000000), (160952433652218515961790753/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial146.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial146.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial146.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 26154543588995215795003564165923479), (Int.ofNat 2797631356245965933194204429646776), (Int.ofNat 491345034484886570077543831339), (Int.negOfNat 25837853270417958399376363270348), (Int.ofNat 3722449234077867447123360574633), (Int.ofNat 1263047214612870206465537367000), (Int.negOfNat 159826838774080412128766522240), (Int.negOfNat 26475640074980214211630043574), (Int.ofNat 3327014279121714747959387646), (Int.ofNat 283874333654851489345765182), (Int.negOfNat 37759741161279786778681813), (Int.negOfNat 1843265164190512034905059), (Int.ofNat 268884270679412068081604), (Int.ofNat 7990063013751836255678), (Int.negOfNat 1312860350501270152464), (Int.negOfNat 22197018431529080674), (Int.ofNat 4076738301199593111), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-26154543588995215795003564165923479/56294995342131200000000000000000000), (349703919530745741649275553705847/7036874417766400000000000000000000), (491345034484886570077543831339/56294995342131200000000000000000000), (-6459463317604489599844090817587/14073748835532800000000000000000000), (3722449234077867447123360574633/56294995342131200000000000000000000), (1263047214612870206465537367/56294995342131200000000000000000), (-249729435584500643951197691/87960930222080000000000000000000), (-13237820037490107105815021787/28147497671065600000000000000000000), (1663507139560857373979693823/28147497671065600000000000000000000), (141937166827425744672882591/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial146.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial146.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial146.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 20676703660495426374280045154387798), (Int.ofNat 2671010505412396861851349469073028), (Int.negOfNat 13501138004845173036472432215584), (Int.ofNat 20926865532777140361825770558090), (Int.ofNat 3671232025579528870653039688442), (Int.negOfNat 1146525119417991134547266490125), (Int.negOfNat 104601705704701869616077971402), (Int.ofNat 28753248959912113538897837489), (Int.ofNat 1407677281176562224817541404), (Int.negOfNat 397536184356913954842266771), (Int.negOfNat 10090267290744946057940736), (Int.ofNat 3382639916376837572002101), (Int.ofNat 41237961969572275893680), (Int.negOfNat 19370872465220853270450), (Int.negOfNat 90019534347491688335), (Int.ofNat 81239275764977888479), (Int.ofNat 1381366358942628477), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-10338351830247713187140022577193899/28147497671065600000000000000000000), (667752626353099215462837367268257/14073748835532800000000000000000000), (-421910562651411657389763506737/1759218604441600000000000000000000), (2092686553277714036182577055809/5629499534213120000000000000000000), (1835616012789764435326519844221/28147497671065600000000000000000000), (-9172200955343929076378131921/450359962737049600000000000000000), (-52300852852350934808038985701/28147497671065600000000000000000000), (28753248959912113538897837489/56294995342131200000000000000000000), (351919320294140556204385351/14073748835532800000000000000000000), (-397536184356913954842266771/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial146.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial146.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial146.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 15202082028632108031358203245198202), (Int.ofNat 2887195652786833765713612034500159), (Int.ofNat 103334842821612892878815927899225), (Int.ofNat 4173616931581394819824180777018), (Int.negOfNat 6039945187440954933211429435031), (Int.negOfNat 140667206459641346800127667930), (Int.ofNat 202880554036197242246203811721), (Int.ofNat 1210784593675109618341594433), (Int.negOfNat 3524297737038434209824778967), (Int.ofNat 14304071439971152042188367), (Int.ofNat 36575416040214037750079964), (Int.negOfNat 367544609048025448948685), (Int.negOfNat 248823149605846862897675), (Int.ofNat 3351001001769445919839), (Int.ofNat 1187750790113930667786), (Int.negOfNat 20394886554708094191), (Int.negOfNat 4097860480376848494), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-7601041014316054015679101622599101/28147497671065600000000000000000000), (2887195652786833765713612034500159/56294995342131200000000000000000000), (4133393712864515715152637115969/2251799813685248000000000000000000), (2086808465790697409912090388509/28147497671065600000000000000000000), (-6039945187440954933211429435031/56294995342131200000000000000000000), (-14066720645964134680012766793/5629499534213120000000000000000000), (202880554036197242246203811721/56294995342131200000000000000000000), (1210784593675109618341594433/56294995342131200000000000000000000), (-3524297737038434209824778967/56294995342131200000000000000000000), (14304071439971152042188367/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial146.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial146.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial146.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 9069822723177827590993398998479986), (Int.ofNat 3182183697647352658248181682306510), (Int.ofNat 15814972762958605050866620769638), (Int.negOfNat 22352285672366384724860200539645), (Int.ofNat 1622579644974554855693380384034), (Int.ofNat 1106641140301060552499601882438), (Int.negOfNat 60960379532441768914126500509), (Int.negOfNat 25414650055640378594851811509), (Int.ofNat 1199975761074202299903777344), (Int.ofNat 330246528090317245965746432), (Int.negOfNat 14104899404507778996840889), (Int.negOfNat 2720970082373356998959304), (Int.ofNat 107628378603314427093427), (Int.ofNat 15357021511651656575617), (Int.negOfNat 562442672249593885685), (Int.negOfNat 63864324764091295635), (Int.ofNat 1208702512062378784), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-4534911361588913795496699499239993/28147497671065600000000000000000000), (318218369764735265824818168230651/5629499534213120000000000000000000), (7907486381479302525433310384819/28147497671065600000000000000000000), (-4470457134473276944972040107929/11258999068426240000000000000000000), (811289822487277427846690192017/28147497671065600000000000000000000), (553320570150530276249800941219/28147497671065600000000000000000000), (-60960379532441768914126500509/56294995342131200000000000000000000), (-25414650055640378594851811509/56294995342131200000000000000000000), (18749621266784410935996521/879609302220800000000000000000000), (1290025500352801742053697/219902325555200000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial146.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial146.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial146.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 2766337651439214043531613956056992), (Int.ofNat 3096470024759071578480261867737914), (Int.negOfNat 19092187251632943925565231015591), (Int.ofNat 14518399992221642854145834466997), (Int.ofNat 4304810179604677007492931209961), (Int.negOfNat 735325713259653597895702340501), (Int.negOfNat 138900256971225325263185291091), (Int.ofNat 17510075081379672883614334891), (Int.ofNat 2346946979190832079590961156), (Int.negOfNat 237688689586861615950239818), (Int.negOfNat 24041838440125337080804711), (Int.ofNat 2052693360376663641324896), (Int.ofNat 163544627587180963219973), (Int.negOfNat 12133204312879049239083), (Int.negOfNat 788172694702055146665), (Int.ofNat 54228058009858776915), (Int.ofNat 2389923170086626216), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-86448051607475438860362936126781/1759218604441600000000000000000000), (1548235012379535789240130933868957/28147497671065600000000000000000000), (-19092187251632943925565231015591/56294995342131200000000000000000000), (14518399992221642854145834466997/56294995342131200000000000000000000), (4304810179604677007492931209961/56294995342131200000000000000000000), (-735325713259653597895702340501/56294995342131200000000000000000000), (-138900256971225325263185291091/56294995342131200000000000000000000), (17510075081379672883614334891/56294995342131200000000000000000000), (586736744797708019897740289/14073748835532800000000000000000000), (-118844344793430807975119909/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial146.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial146.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial146.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 3505538328545001545013908283492949), (Int.ofNat 3256184571830235406122285557055639), (Int.ofNat 93838480816282249761984282992487), (Int.ofNat 9785180732426200036846330091731), (Int.negOfNat 5030199515611422404947853411992), (Int.negOfNat 480254499869387991226432164080), (Int.ofNat 165491254316410400555819882379), (Int.ofNat 11156988785398438491416855483), (Int.negOfNat 2855465704577592514730102833), (Int.negOfNat 148783734446527975229336633), (Int.ofNat 29866766191347393918081036), (Int.ofNat 1269792661336708473441515), (Int.negOfNat 207190660511327693505825), (Int.negOfNat 7451927223516467622611), (Int.ofNat 1014267256264208971564), (Int.ofNat 34252316047555859409), (Int.negOfNat 2944802727922274906), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(3505538328545001545013908283492949/56294995342131200000000000000000000), (3256184571830235406122285557055639/56294995342131200000000000000000000), (93838480816282249761984282992487/56294995342131200000000000000000000), (9785180732426200036846330091731/56294995342131200000000000000000000), (-628774939451427800618481676499/7036874417766400000000000000000000), (-6003181248367349890330402051/703687441776640000000000000000000), (165491254316410400555819882379/56294995342131200000000000000000000), (11156988785398438491416855483/56294995342131200000000000000000000), (-2855465704577592514730102833/56294995342131200000000000000000000), (-148783734446527975229336633/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial146.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial146.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial146.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 10386936155199050748527040417724849), (Int.ofNat 3583241630537411644758625811938463), (Int.ofNat 35182250905905501740821525275749), (Int.negOfNat 22369270929108679573521434372736), (Int.negOfNat 150169085173085443940304507709), (Int.ofNat 1119664447780974926732894406514), (Int.ofNat 7958912044866864736252100602), (Int.negOfNat 26173236489601591292019624611), (Int.negOfNat 221103599744455574387352904), (Int.ofNat 347401569552249177576233279), (Int.ofNat 3334372569500047496974236), (Int.negOfNat 2930756681450345226946499), (Int.negOfNat 30404878090417701428530), (Int.ofNat 16934061187569708923350), (Int.ofNat 180884690984654558435), (Int.negOfNat 71122405865796704071), (Int.ofNat 186064248133544123), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(10386936155199050748527040417724849/56294995342131200000000000000000000), (3583241630537411644758625811938463/56294995342131200000000000000000000), (35182250905905501740821525275749/56294995342131200000000000000000000), (-174759929133661559168136206037/439804651110400000000000000000000), (-150169085173085443940304507709/56294995342131200000000000000000000), (559832223890487463366447203257/28147497671065600000000000000000000), (3979456022433432368126050301/28147497671065600000000000000000000), (-26173236489601591292019624611/56294995342131200000000000000000000), (-27637949968056946798419113/7036874417766400000000000000000000), (347401569552249177576233279/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial146.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial146.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial146.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 17545898699649780190921944806249197), (Int.ofNat 3530667850157389458822901127735529), (Int.negOfNat 27581405571561521506500233004697), (Int.ofNat 9232739160995272257936668923696), (Int.ofNat 5271943586923503862903417272329), (Int.negOfNat 439376667262835021397820115300), (Int.negOfNat 180021324732536483056086032599), (Int.ofNat 9094188258949727862313197226), (Int.ofNat 3197336921519360990551678254), (Int.negOfNat 101177537935348808321981518), (Int.negOfNat 34140215598717579897125537), (Int.ofNat 677158889596511720520691), (Int.ofNat 239808192055998096401496), (Int.negOfNat 2929698657563556979322), (Int.negOfNat 1178410084510214690686), (Int.ofNat 7633136014299273976), (Int.ofNat 2965924907099530289), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(17545898699649780190921944806249197/56294995342131200000000000000000000), (3530667850157389458822901127735529/56294995342131200000000000000000000), (-27581405571561521506500233004697/56294995342131200000000000000000000), (577046197562204516121041807731/3518437208883200000000000000000000), (5271943586923503862903417272329/56294995342131200000000000000000000), (-4393766672628350213978201153/562949953421312000000000000000000), (-180021324732536483056086032599/56294995342131200000000000000000000), (4547094129474863931156598613/28147497671065600000000000000000000), (1598668460759680495275839127/28147497671065600000000000000000000), (-50588768967674404160990759/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial146.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial146.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial146.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 24631438508432051284963089447556128), (Int.ofNat 3637076657513316804640397227734472), (Int.ofNat 87002209460245999558845359432053), (Int.ofNat 14837771885207161675483194118504), (Int.negOfNat 4605739195805583582017292084718), (Int.negOfNat 840372072155904692185131893804), (Int.ofNat 145394431123017748523709342208), (Int.ofNat 21758528804442408358675864436), (Int.negOfNat 2303007285564594728328491508), (Int.negOfNat 313460743014726922988300644), (Int.ofNat 21301374555040130786617097), (Int.ofNat 2805808630040741091026755), (Int.negOfNat 127009968923402442349537), (Int.negOfNat 16846956452845245768195), (Int.ofNat 524017277604257528108), (Int.ofNat 73026566541524783793), (Int.negOfNat 2769092392746132923), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(769732453388501602655096545236129/1759218604441600000000000000000000), (454634582189164600580049653466809/7036874417766400000000000000000000), (87002209460245999558845359432053/56294995342131200000000000000000000), (1854721485650895209435399264813/7036874417766400000000000000000000), (-2302869597902791791008646042359/28147497671065600000000000000000000), (-210093018038976173046282973451/14073748835532800000000000000000000), (283973498287144040085369809/109951162777600000000000000000000), (5439632201110602089668966109/14073748835532800000000000000000000), (-575751821391148682082122877/14073748835532800000000000000000000), (-78365185753681730747075161/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial146.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial146.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial146.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 32283086287939405969266057953129421), (Int.ofNat 3983245122617943872133463598210250), (Int.ofNat 42519694771730305556422007641790), (Int.negOfNat 25560311604466208104192908425784), (Int.negOfNat 1653378986049531486474620764288), (Int.ofNat 1305443071356425705788302557214), (Int.ofNat 83843296011171200082238179941), (Int.negOfNat 29697473007748842388977990462), (Int.negOfNat 1954804680914612126834862955), (Int.ofNat 366652117295708924603402486), (Int.ofNat 24958825974132616250788405), (Int.negOfNat 2776476313606742303658827), (Int.negOfNat 195960778017909430928318), (Int.ofNat 14094635861419876604046), (Int.ofNat 1034322028446158544243), (Int.negOfNat 49757840261417184031), (Int.negOfNat 2987047086276785672), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(32283086287939405969266057953129421/56294995342131200000000000000000000), (15932980490471775488533854392841/225179981368524800000000000000000), (4251969477173030555642200764179/5629499534213120000000000000000000), (-3195038950558276013024113553223/7036874417766400000000000000000000), (-12917023328511964738082974721/439804651110400000000000000000000), (652721535678212852894151278607/28147497671065600000000000000000000), (83843296011171200082238179941/56294995342131200000000000000000000), (-14848736503874421194488995231/28147497671065600000000000000000000), (-390960936182922425366972591/11258999068426240000000000000000000), (183326058647854462301701243/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial146.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial146.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial146.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 40231764123598224483651899428043744), (Int.ofNat 3899856525212936529489011930840953), (Int.negOfNat 47536931946146607046392668497160), (Int.ofNat 8931633960688875726085581298432), (Int.ofNat 7604699854896121475944824864220), (Int.negOfNat 214787972114092810113932226201), (Int.negOfNat 269514438856726494877358729347), (Int.negOfNat 1945493261152801074855916154), (Int.ofNat 4646177186764257307130758761), (Int.ofNat 116348517173778457553154930), (Int.negOfNat 45574987901082422396350670), (Int.negOfNat 1597064960406106463931306), (Int.ofNat 283912479898819429927895), (Int.ofNat 11645910830686609391311), (Int.negOfNat 1227314601369813964807), (Int.negOfNat 56072877028056782843), (Int.ofNat 5352120537358721723), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(1257242628862444515114121857126367/1759218604441600000000000000000000), (3899856525212936529489011930840953/56294995342131200000000000000000000), (-1188423298653665176159816712429/1407374883553280000000000000000000), (34889195158940920805021801947/219902325555200000000000000000000), (380234992744806073797241243211/2814749767106560000000000000000000), (-214787972114092810113932226201/56294995342131200000000000000000000), (-269514438856726494877358729347/56294995342131200000000000000000000), (-972746630576400537427958077/28147497671065600000000000000000000), (4646177186764257307130758761/56294995342131200000000000000000000), (11634851717377845755315493/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial146.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial146.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial146.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 48011286842129390653027342774712277), (Int.ofNat 3995219273731972054292590931945118), (Int.ofNat 113704431404587002971676474266170), (Int.ofNat 25184266695752300634794072356316), (Int.negOfNat 6227076421553164951816306810321), (Int.negOfNat 1679845671650831487305602433838), (Int.ofNat 143362028742711821638436411277), (Int.ofNat 44833314573165743534709977773), (Int.negOfNat 1109570647319457488395277025), (Int.negOfNat 603265429716564750531798115), (Int.negOfNat 1719461487893096137378433), (Int.ofNat 4722139138708073480693219), (Int.ofNat 76792663679228728620292), (Int.negOfNat 24421343166034834216729), (Int.negOfNat 578103269243229851578), (Int.ofNat 91247887857184265706), (Int.ofNat 2147159883916511455), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(48011286842129390653027342774712277/56294995342131200000000000000000000), (1997609636865986027146295465972559/28147497671065600000000000000000000), (11370443140458700297167647426617/5629499534213120000000000000000000), (6296066673938075158698518089079/14073748835532800000000000000000000), (-6227076421553164951816306810321/56294995342131200000000000000000000), (-839922835825415743652801216919/28147497671065600000000000000000000), (143362028742711821638436411277/56294995342131200000000000000000000), (44833314573165743534709977773/56294995342131200000000000000000000), (-44382825892778299535811081/2251799813685248000000000000000000), (-120653085943312950106359623/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial146.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial146.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial146.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 56518957894954156287838041974574470), (Int.ofNat 4463723741288200812166976440020175), (Int.ofNat 40853542335376474351669272216169), (Int.negOfNat 48838799932487692755821671018090), (Int.negOfNat 5368749454740703028366076829272), (Int.ofNat 2218426156287113104370933150299), (Int.ofNat 304376441537680993425343494127), (Int.negOfNat 37338320086119158491825593973), (Int.negOfNat 6473416082482902882472070525), (Int.ofNat 251096117459936652931002665), (Int.ofNat 66654915637738541989885017), (Int.negOfNat 619264223670212866334319), (Int.negOfNat 419785622231095077721558), (Int.negOfNat 1887077552155101746621), (Int.ofNat 1819665491868519023022), (Int.ofNat 23260817714369535394), (Int.negOfNat 7088220753218617845), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(5651895789495415628783804197457447/5629499534213120000000000000000000), (178548949651528032486679057600807/2251799813685248000000000000000000), (40853542335376474351669272216169/56294995342131200000000000000000000), (-4883879993248769275582167101809/5629499534213120000000000000000000), (-671093681842587878545759603659/7036874417766400000000000000000000), (2218426156287113104370933150299/56294995342131200000000000000000000), (304376441537680993425343494127/56294995342131200000000000000000000), (-37338320086119158491825593973/56294995342131200000000000000000000), (-258936643299316115298882821/2251799813685248000000000000000000), (50219223491987330586200533/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial146.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial146.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial146.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 65217436228815299234435947051143686), (Int.ofNat 4082732970318340567051762936274721), (Int.negOfNat 165317026281672443962177836341756), (Int.ofNat 15439751614665126950383982316596), (Int.ofNat 19203248246856182557307669594636), (Int.ofNat 818545422613768239707104958029), (Int.negOfNat 583669657806858151042916022247), (Int.negOfNat 54079798263843327518319321146), (Int.ofNat 6173323359439467299744724961), (Int.ofNat 802664936900440825192714370), (Int.negOfNat 33856114408573004440820870), (Int.negOfNat 6326078017415629819708994), (Int.ofNat 102990930983365756946295), (Int.ofNat 32588610499524502460739), (Int.negOfNat 113228769280477835407), (Int.negOfNat 124142055602440339307), (Int.negOfNat 439222573626289177), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(32608718114407649617217973525571843/28147497671065600000000000000000000), (4082732970318340567051762936274721/56294995342131200000000000000000000), (-41329256570418110990544459085439/14073748835532800000000000000000000), (3859937903666281737595995579149/14073748835532800000000000000000000), (4800812061714045639326917398659/14073748835532800000000000000000000), (818545422613768239707104958029/56294995342131200000000000000000000), (-583669657806858151042916022247/56294995342131200000000000000000000), (-27039899131921663759159660573/28147497671065600000000000000000000), (6173323359439467299744724961/56294995342131200000000000000000000), (80266493690044082519271437/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial146.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial146.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial146.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 73136264824078176009008446389301571), (Int.ofNat 4158367584153890738222755641678830), (Int.ofNat 291465861441207447895020493611865), (Int.ofNat 92747032235524980718639668144149), (Int.negOfNat 13321070223938403038033652813309), (Int.negOfNat 6783749940228043833676369945925), (Int.negOfNat 304413689814732957527554189309), (Int.ofNat 100315177732864750970683128512), (Int.ofNat 8214820520688961278398758095), (Int.negOfNat 757005584521518173029187636), (Int.negOfNat 84178516313573280183274195), (Int.ofNat 3534340661450735463202477), (Int.ofNat 520756599869166503748082), (Int.negOfNat 10944630729115945047296), (Int.negOfNat 2239630474113400800957), (Int.ofNat 21619586905707414381), (Int.ofNat 7970352313933402828), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(73136264824078176009008446389301571/56294995342131200000000000000000000), (415836758415389073822275564167883/5629499534213120000000000000000000), (58293172288241489579004098722373/11258999068426240000000000000000000), (92747032235524980718639668144149/56294995342131200000000000000000000), (-13321070223938403038033652813309/56294995342131200000000000000000000), (-271349997609121753347054797837/2251799813685248000000000000000000), (-304413689814732957527554189309/56294995342131200000000000000000000), (1567424652076011733916923883/879609302220800000000000000000000), (1642964104137792255679751619/11258999068426240000000000000000000), (-189251396130379543257296909/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial146.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial146.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial146.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 82925618895558130141148367622549722), (Int.ofNat 5461003565424648063858473801779132), (Int.negOfNat 9709999717256610602130693837799), (Int.negOfNat 268139755597189479968329602405848), (Int.negOfNat 66109054084877252460142542260079), (Int.negOfNat 383412579172270000881383271413), (Int.ofNat 1307547457958436814349964907119), (Int.ofNat 71683347386020855491218554014), (Int.negOfNat 12613678259954911087266892758), (Int.negOfNat 998008257851239710154218356), (Int.ofNat 75739696705943602890918097), (Int.ofNat 7502259534895207750966445), (Int.negOfNat 313208663679067783409437), (Int.negOfNat 37609564221948851774405), (Int.ofNat 941758272035057407758), (Int.ofNat 138552655543828882857), (Int.negOfNat 2143805570986299623), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(41462809447779065070574183811274861/28147497671065600000000000000000000), (1365250891356162015964618450444783/14073748835532800000000000000000000), (-9709999717256610602130693837799/56294995342131200000000000000000000), (-33517469449648684996041200300731/7036874417766400000000000000000000), (-66109054084877252460142542260079/56294995342131200000000000000000000), (-383412579172270000881383271413/56294995342131200000000000000000000), (1307547457958436814349964907119/56294995342131200000000000000000000), (35841673693010427745609277007/28147497671065600000000000000000000), (-6306839129977455543633446379/28147497671065600000000000000000000), (-249502064462809927538554589/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial146.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial146.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial146.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 90682863689685106800960699635553695), (Int.ofNat 326733929749171230408776352504681), (Int.negOfNat 2900001697755185496970908772729299), (Int.negOfNat 589532517538309576769731150854130), (Int.ofNat 11712424907648678968640216110411), (Int.ofNat 14455456931474270263766073296100), (Int.ofNat 567388443019550941082124478640), (Int.negOfNat 172973513918051902547128101726), (Int.negOfNat 10788083668101218000256312446), (Int.ofNat 1284927947434810814777453118), (Int.ofNat 98400627635367159702124113), (Int.negOfNat 6572865612163927728869091), (Int.negOfNat 576459855690217322447104), (Int.ofNat 24642373350468262858172), (Int.ofNat 2406515294195553482164), (Int.negOfNat 69039858338492582726), (Int.negOfNat 7991474493110658211), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(18136572737937021360192139927110739/11258999068426240000000000000000000), (326733929749171230408776352504681/56294995342131200000000000000000000), (-2900001697755185496970908772729299/56294995342131200000000000000000000), (-58953251753830957676973115085413/5629499534213120000000000000000000), (11712424907648678968640216110411/56294995342131200000000000000000000), (144554569314742702637660732961/562949953421312000000000000000000), (7092355537744386763526555983/703687441776640000000000000000000), (-86486756959025951273564050863/28147497671065600000000000000000000), (-5394041834050609000128156223/28147497671065600000000000000000000), (642463973717405407388726559/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial146.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial146.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial146.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 75682191600794956035821266147783203), (Int.negOfNat 16792651822607382963734645602445080), (Int.negOfNat 4992224041074621719392513370529968), (Int.ofNat 65055378916288688387260985814758), (Int.ofNat 135958948303591772422881582892447), (Int.ofNat 5042719529579946017828765286364), (Int.negOfNat 1992646063908195169264200163598), (Int.negOfNat 111795946394941794251720948189), (Int.ofNat 18208056612331228484888282496), (Int.ofNat 1196142002304293708412094671), (Int.negOfNat 113542787688087024557755714), (Int.negOfNat 8118934756831638485105201), (Int.ofNat 513244954344410094290170), (Int.ofNat 38747839074777127956350), (Int.negOfNat 1755653389196383988365), (Int.negOfNat 139004311518572974829), (Int.ofNat 4726833715598888423), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(75682191600794956035821266147783203/56294995342131200000000000000000000), (-419816295565184574093366140061127/1407374883553280000000000000000000), (-312014002567163857462032085658123/3518437208883200000000000000000000), (32527689458144344193630492907379/28147497671065600000000000000000000), (135958948303591772422881582892447/56294995342131200000000000000000000), (1260679882394986504457191321591/14073748835532800000000000000000000), (-996323031954097584632100081799/28147497671065600000000000000000000), (-111795946394941794251720948189/56294995342131200000000000000000000), (142250442283837722538189707/439804651110400000000000000000000), (1196142002304293708412094671/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial146.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial146.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial146.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 24848448969713792797657522672812634), (Int.negOfNat 31638709545489196078022607263522444), (Int.negOfNat 1452177245430893932409350118242881), (Int.ofNat 1010046600427205512962687103563844), (Int.ofNat 58948502138374842712984167197698), (Int.negOfNat 18784308328965444767814316831809), (Int.negOfNat 1179008705214403114271109249671), (Int.ofNat 216206539657021676798673556167), (Int.ofNat 13812893748034217529530165667), (Int.negOfNat 1662129651101157134647578517), (Int.negOfNat 106198243408058989803350164), (Int.ofNat 9062638846460823144355735), (Int.ofNat 574893599447955453258125), (Int.negOfNat 36746751128566648752039), (Int.negOfNat 2306144572157806567836), (Int.ofNat 113255344430390409341), (Int.ofNat 8012596672287913594), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(12424224484856896398828761336406317/28147497671065600000000000000000000), (-7909677386372299019505651815880611/14073748835532800000000000000000000), (-1452177245430893932409350118242881/56294995342131200000000000000000000), (252511650106801378240671775890961/14073748835532800000000000000000000), (29474251069187421356492083598849/28147497671065600000000000000000000), (-18784308328965444767814316831809/56294995342131200000000000000000000), (-1179008705214403114271109249671/56294995342131200000000000000000000), (216206539657021676798673556167/56294995342131200000000000000000000), (13812893748034217529530165667/56294995342131200000000000000000000), (-1662129651101157134647578517/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial146.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial146.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial146.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 35860413328045574769892951206800814), (Int.negOfNat 25062875919226370972418378366911783), (Int.ofNat 4398608096133858424489333792763583), (Int.ofNat 677317771166647585386180857107891), (Int.negOfNat 131315632030110456364984482084962), (Int.negOfNat 12477938532819155786288762194888), (Int.ofNat 2079630502526861259179191436498), (Int.ofNat 153513183020351569620523938109), (Int.negOfNat 20547597526539738891578518544), (Int.negOfNat 1303399341114052787353734432), (Int.ofNat 137792838203004238792163439), (Int.ofNat 7907129664625864918629454), (Int.negOfNat 666254159861150396277377), (Int.negOfNat 35493402321628511438817), (Int.ofNat 2429562793621262806535), (Int.ofNat 120005779412025730235), (Int.negOfNat 7316902586603895684), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-17930206664022787384946475603400407/28147497671065600000000000000000000), (-25062875919226370972418378366911783/56294995342131200000000000000000000), (4398608096133858424489333792763583/56294995342131200000000000000000000), (677317771166647585386180857107891/56294995342131200000000000000000000), (-65657816015055228182492241042481/28147497671065600000000000000000000), (-1559742316602394473286095274361/7036874417766400000000000000000000), (1039815251263430629589595718249/28147497671065600000000000000000000), (153513183020351569620523938109/56294995342131200000000000000000000), (-1284224845408733680723657409/3518437208883200000000000000000000), (-40731229409814149604804201/1759218604441600000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial146.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial146.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial146.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial146.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial146.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial146.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial146.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial146.reflect := by
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

end Bin146
end
end ErdosOverlap.OuterNumerics
