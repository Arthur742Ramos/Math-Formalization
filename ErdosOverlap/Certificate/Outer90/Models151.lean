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

/-! # Exact integer weighted outer models for source bin 151

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin151

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 2182314359285539900)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 2190127608912219600)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 2067754491864540700)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 1492056270276566000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 941720720481480100)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 609548257265905500)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 331572622368776100)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 120432171592243400)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial151.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial151.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9614092561462305000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 2562665717901362000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1575157736137574600)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 987955786808082800)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 448940157492406440)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 244288266347479500)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 65193419580174760)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 24238350530583180)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 19362627306760073)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial151.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial151.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9614092561462305000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 2562665717901362000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1575157736137574600)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 987955786808082800)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 448940157492406440)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 244288266347479500)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 65193419580174760)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 24238350530583180)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 19362627306760073)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial151.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial151.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial151.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 7134360709986344997313294065825859), (Int.ofNat 4909500681898080618603920412035461), (Int.ofNat 728673320748751736035462904025200), (Int.negOfNat 150396758498200537348657573517707), (Int.negOfNat 19080565866246034794500698248801), (Int.ofNat 2839638286143376397865794882567), (Int.ofNat 272300959330032717760469548117), (Int.negOfNat 33603952081983522083962313397), (Int.negOfNat 2500240068828627129881235752), (Int.ofNat 268417280389781569306337316), (Int.ofNat 15997068273637583776396917), (Int.negOfNat 1532760514801809331788662), (Int.negOfNat 75220523480167042185451), (Int.ofNat 6537435794963188726351), (Int.ofNat 269992455852836733575), (Int.negOfNat 21213228086749828805), (Int.negOfNat 793319365958849482), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-7134360709986344997313294065825859/11258999068426240000000000000000000), (4909500681898080618603920412035461/11258999068426240000000000000000000), (1821683301871879340088657260063/28147497671065600000000000000000), (-150396758498200537348657573517707/11258999068426240000000000000000000), (-19080565866246034794500698248801/11258999068426240000000000000000000), (2839638286143376397865794882567/11258999068426240000000000000000000), (272300959330032717760469548117/11258999068426240000000000000000000), (-33603952081983522083962313397/11258999068426240000000000000000000), (-312530008603578391235154469/1407374883553280000000000000000000), (67104320097445392326584329/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial151.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial151.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial151.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial151 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 4194375554876895274008556944624253), (Int.ofNat 5671374384194881232842119897432462), (Int.negOfNat 364805771674628462690734048482067), (Int.negOfNat 167568660925268589238938405941303), (Int.ofNat 14670088230061396924308385967235), (Int.ofNat 2783953301888391119215900500280), (Int.negOfNat 269579319269483117519120917673), (Int.negOfNat 28799857421821266113081807251), (Int.ofNat 2893462266868254790054451731), (Int.ofNat 203236076957559742674736961), (Int.negOfNat 20602465482123520066385732), (Int.negOfNat 1039353723394027820062105), (Int.ofNat 104832842775727434876635), (Int.ofNat 4024247262693894377847), (Int.negOfNat 401269387132615843788), (Int.negOfNat 11963873862435513973), (Int.ofNat 1276286683272103372), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(4194375554876895274008556944624253/11258999068426240000000000000000000), (2835687192097440616421059948716231/5629499534213120000000000000000000), (-364805771674628462690734048482067/11258999068426240000000000000000000), (-167568660925268589238938405941303/11258999068426240000000000000000000), (2934017646012279384861677193447/2251799813685248000000000000000000), (69598832547209777980397512507/281474976710656000000000000000000), (-269579319269483117519120917673/11258999068426240000000000000000000), (-28799857421821266113081807251/11258999068426240000000000000000000), (2893462266868254790054451731/11258999068426240000000000000000000), (203236076957559742674736961/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial151.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial151.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial151.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial151 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 13041042421502666256615659292477692), (Int.ofNat 2832141600274751968313942422100385), (Int.negOfNat 873609338090499684890927065034392), (Int.ofNat 7819562646403682521553508682961), (Int.ofNat 22024550684375554446175172129800), (Int.negOfNat 1349544684361120492091450401708), (Int.negOfNat 289970455116544300439248808024), (Int.ofNat 24405593274424621991120547337), (Int.ofNat 2384478338861469318526534648), (Int.negOfNat 234637860863949382503854283), (Int.negOfNat 13520933606868623303392222), (Int.ofNat 1477233186567126089292993), (Int.ofNat 56263222257605401464160), (Int.negOfNat 6669508923017441127920), (Int.negOfNat 179151923997453581995), (Int.ofNat 22788996682759219707), (Int.ofNat 412660223875359209), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(3260260605375666564153914823119423/2814749767106560000000000000000000), (566428320054950393662788484420077/2251799813685248000000000000000000), (-109201167261312460611365883129299/1407374883553280000000000000000000), (7819562646403682521553508682961/11258999068426240000000000000000000), (110122753421877772230875860649/56294995342131200000000000000000), (-337386171090280123022862600427/2814749767106560000000000000000000), (-36246306889568037554906101003/1407374883553280000000000000000000), (24405593274424621991120547337/11258999068426240000000000000000000), (298059792357683664815816831/1407374883553280000000000000000000), (-234637860863949382503854283/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial151.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial151.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial151.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial151 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 15567697604179266544619011535755249), (Int.negOfNat 14530049426588373656245139229354), (Int.negOfNat 456178369007290622683908145288784), (Int.ofNat 100176623307353962836584255993962), (Int.negOfNat 425754487193467308940826946261), (Int.negOfNat 2245863051259550375944081930320), (Int.ofNat 139286608576162837995030729303), (Int.ofNat 24242627296115726583205586738), (Int.negOfNat 2166921307661884768909814908), (Int.negOfNat 161271451449139003262796744), (Int.ofNat 17962143873422422404677119), (Int.ofNat 735294521217090061416443), (Int.negOfNat 98682155083067898645712), (Int.negOfNat 2443305046293840792266), (Int.ofNat 393346399598055555472), (Int.ofNat 5717019292802117638), (Int.negOfNat 1218198801351823153), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(15567697604179266544619011535755249/11258999068426240000000000000000000), (-7265024713294186828122569614677/5629499534213120000000000000000000), (-28511148062955663917744259080549/703687441776640000000000000000000), (50088311653676981418292127996981/5629499534213120000000000000000000), (-425754487193467308940826946261/11258999068426240000000000000000000), (-28073288140744379699301024129/140737488355328000000000000000000), (139286608576162837995030729303/11258999068426240000000000000000000), (12121313648057863291602793369/5629499534213120000000000000000000), (-541730326915471192227453727/2814749767106560000000000000000000), (-20158931431142375407849593/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial151.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial151.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial151.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial151 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 14448056904201913755083538088128669), (Int.negOfNat 795306265153789189081028770788408), (Int.ofNat 308508690207837358061183381097), (Int.ofNat 38343101484893815610751975803946), (Int.negOfNat 10556968743001441018199175244294), (Int.ofNat 322243599020113311238452978995), (Int.ofNat 192773401836462917442562897434), (Int.negOfNat 15118507587238589520153478152), (Int.negOfNat 1671463816240047475681971334), (Int.ofNat 183533308864424408721823478), (Int.ofNat 8778778851814548706042211), (Int.negOfNat 1280534545865601529578405), (Int.negOfNat 30516769358200605150331), (Int.ofNat 6095760937318213887595), (Int.ofNat 71526856669945972904), (Int.negOfNat 21774752663503007411), (Int.negOfNat 51363709098629009), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(14448056904201913755083538088128669/11258999068426240000000000000000000), (-99413283144223648635128596348551/1407374883553280000000000000000000), (308508690207837358061183381097/11258999068426240000000000000000000), (19171550742446907805375987901973/5629499534213120000000000000000000), (-5278484371500720509099587622147/5629499534213120000000000000000000), (64448719804022662247690595799/2251799813685248000000000000000000), (96386700918231458721281448717/5629499534213120000000000000000000), (-1889813448404823690019184769/1407374883553280000000000000000000), (-835731908120023737840985667/5629499534213120000000000000000000), (91766654432212204360911739/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial151.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial151.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial151.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial151 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 13016898211217227753720596141807643), (Int.negOfNat 617017739957983702225750737249710), (Int.ofNat 36799784526417178055789053673994), (Int.negOfNat 12774999099562327669785319085587), (Int.negOfNat 1071068945433196186581870057223), (Int.ofNat 1018608842225386555839313506325), (Int.negOfNat 72655159244403135887455497827), (Int.negOfNat 13874092416804706158169700106), (Int.ofNat 1527806207348345897839927635), (Int.ofNat 91329742806434068219626428), (Int.negOfNat 14330527003512745223286715), (Int.negOfNat 341447127308916055068701), (Int.ofNat 83790142642894674048496), (Int.ofNat 657325193799464749858), (Int.negOfNat 345609692519707645001), (Int.ofNat 383447073880564037), (Int.ofNat 1160110919431542934), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(13016898211217227753720596141807643/11258999068426240000000000000000000), (-61701773995798370222575073724971/1125899906842624000000000000000000), (18399892263208589027894526836997/5629499534213120000000000000000000), (-12774999099562327669785319085587/11258999068426240000000000000000000), (-1071068945433196186581870057223/11258999068426240000000000000000000), (40744353689015462233572540253/450359962737049600000000000000000), (-72655159244403135887455497827/11258999068426240000000000000000000), (-6937046208402353079084850053/5629499534213120000000000000000000), (305561241469669179567985527/2251799813685248000000000000000000), (22832435701608517054906607/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial151.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial151.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial151.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial151 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 11837317290899062925709582348199184), (Int.negOfNat 594369739725959652688702925795065), (Int.negOfNat 7838170877971519953377488720044), (Int.ofNat 3010142102966794808597977885348), (Int.ofNat 2753836577677055375347007232286), (Int.negOfNat 267389178403033802177818146000), (Int.negOfNat 82760069201561550863809512951), (Int.ofNat 10212619579730751808424664338), (Int.ofNat 769403526001411938073803303), (Int.negOfNat 135984571450626924676738650), (Int.negOfNat 3219115410973314917015680), (Int.ofNat 1009262658756388996410792), (Int.ofNat 3219918926884946219865), (Int.negOfNat 4975925847650578593817), (Int.ofNat 36050467849861888029), (Int.ofNat 18390590467015447261), (Int.negOfNat 309932805678101191), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(739832330681191432856848896762449/703687441776640000000000000000000), (-118873947945191930537740585159013/2251799813685248000000000000000000), (-1959542719492879988344372180011/2814749767106560000000000000000000), (752535525741698702149494471337/2814749767106560000000000000000000), (1376918288838527687673503616143/5629499534213120000000000000000000), (-133694589201516901088909073/5629499534213120000000000000000), (-82760069201561550863809512951/11258999068426240000000000000000000), (5106309789865375904212332169/5629499534213120000000000000000000), (769403526001411938073803303/11258999068426240000000000000000000), (-2719691429012538493534773/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial151.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial151.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial151.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial151 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 10672947854537406085615230870423854), (Int.negOfNat 533714491833218849040434459504217), (Int.ofNat 42667030554146734211165004997409), (Int.ofNat 7462590694276720502371887069201), (Int.negOfNat 1714647375108347319462099871884), (Int.negOfNat 329444235676848738212284089394), (Int.ofNat 58280204443902327080255018391), (Int.ofNat 4757647570744242274098394949), (Int.negOfNat 1084795662958826851296974845), (Int.negOfNat 22225006380663055923447845), (Int.ofNat 10502152590803916233673611), (Int.negOfNat 39686577714095248614593), (Int.negOfNat 63263475328547630132094), (Int.ofNat 982560405220888675633), (Int.ofNat 263988444608404857976), (Int.negOfNat 5983616122140489352), (Int.negOfNat 981590865919019315), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(5336473927268703042807615435211927/5629499534213120000000000000000000), (-533714491833218849040434459504217/11258999068426240000000000000000000), (42667030554146734211165004997409/11258999068426240000000000000000000), (7462590694276720502371887069201/11258999068426240000000000000000000), (-428661843777086829865524967971/2814749767106560000000000000000000), (-164722117838424369106142044697/5629499534213120000000000000000000), (58280204443902327080255018391/11258999068426240000000000000000000), (4757647570744242274098394949/11258999068426240000000000000000000), (-216959132591765370259394969/2251799813685248000000000000000000), (-4445001276132611184689569/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial151.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial151.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial151.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial151 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 9801971396121108859199097881022847), (Int.negOfNat 342508497882327828145476116081699), (Int.ofNat 35189361187499522643794549916738), (Int.negOfNat 9353696329633114933296559783317), (Int.negOfNat 1352653435895577142658871863605), (Int.ofNat 316439682623559364108277080207), (Int.ofNat 19812786060614443330681272811), (Int.negOfNat 7319893591126980576823977129), (Int.negOfNat 63669931928155361564062065), (Int.ofNat 93062090563954434755178485), (Int.negOfNat 1490847230068930996440249), (Int.negOfNat 698784210578660147133607), (Int.ofNat 19602538718921725153546), (Int.ofNat 3482686084456909636087), (Int.negOfNat 121789442185528206624), (Int.negOfNat 12827287236455928408), (Int.ofNat 512071894249067845), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(9801971396121108859199097881022847/11258999068426240000000000000000000), (-342508497882327828145476116081699/11258999068426240000000000000000000), (17594680593749761321897274958369/5629499534213120000000000000000000), (-9353696329633114933296559783317/11258999068426240000000000000000000), (-270530687179115428531774372721/2251799813685248000000000000000000), (316439682623559364108277080207/11258999068426240000000000000000000), (19812786060614443330681272811/11258999068426240000000000000000000), (-7319893591126980576823977129/11258999068426240000000000000000000), (-12733986385631072312812413/2251799813685248000000000000000000), (18612418112790886951035697/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial151.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial151.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial151.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial151 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 9171725458277496684581972417248906), (Int.negOfNat 331306038531684128349664898695881), (Int.negOfNat 27965516945992371125016100357421), (Int.negOfNat 8109525141153810295074677264860), (Int.ofNat 1208906595260163262018613706372), (Int.ofNat 68704209422591708035796809660), (Int.negOfNat 40795508592027912300473085031), (Int.ofNat 750353541595769046163731842), (Int.ofNat 687724203033711476310124883), (Int.negOfNat 27036826053353262220101190), (Int.negOfNat 6548868577177117612905540), (Int.ofNat 320267002011108791776408), (Int.ofNat 39402433383657850673105), (Int.negOfNat 2161583016114581744503), (Int.negOfNat 164077052152692280371), (Int.ofNat 9828797074385332699), (Int.ofNat 702001268121012369), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(4585862729138748342290986208624453/5629499534213120000000000000000000), (-331306038531684128349664898695881/11258999068426240000000000000000000), (-27965516945992371125016100357421/11258999068426240000000000000000000), (-405476257057690514753733863243/562949953421312000000000000000000), (302226648815040815504653426593/2814749767106560000000000000000000), (3435210471129585401789840483/562949953421312000000000000000000), (-40795508592027912300473085031/11258999068426240000000000000000000), (375176770797884523081865921/5629499534213120000000000000000000), (687724203033711476310124883/11258999068426240000000000000000000), (-2703682605335326222010119/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial151.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial151.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial151.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial151 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 8351557590986269538130187792456553), (Int.negOfNat 503184788366352163049384321639410), (Int.negOfNat 50355599599739309106359188086179), (Int.negOfNat 793495040193676495241654148768), (Int.ofNat 249131037554715822588901919025), (Int.negOfNat 144410723468345453117668440005), (Int.ofNat 13053795729287126647139991553), (Int.ofNat 3972145556308673296910433086), (Int.negOfNat 354247154242106297846122045), (Int.negOfNat 49817760502935128997489268), (Int.ofNat 4428953747706404721324245), (Int.ofNat 368031533084610003741301), (Int.negOfNat 33600515983091317366344), (Int.negOfNat 1794966082645921356378), (Int.ofNat 172301897442111282599), (Int.ofNat 6128599983697649923), (Int.negOfNat 574416183921031026), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(8351557590986269538130187792456553/11258999068426240000000000000000000), (-50318478836635216304938432163941/1125899906842624000000000000000000), (-50355599599739309106359188086179/11258999068426240000000000000000000), (-24796720006052390476301692149/351843720888320000000000000000000), (9965241502188632903556076761/450359962737049600000000000000000), (-28882144693669090623533688001/2251799813685248000000000000000000), (13053795729287126647139991553/11258999068426240000000000000000000), (1986072778154336648455216543/5629499534213120000000000000000000), (-70849430848421259569224409/2251799813685248000000000000000000), (-12454440125733782249372317/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial151.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial151.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial151.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial151 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 7138015432200958632611879019297634), (Int.negOfNat 713875549825040047993443172564958), (Int.negOfNat 55693565307541670351688755060705), (Int.negOfNat 1087097407003974108621107848420), (Int.ofNat 173174679592462569006255065813), (Int.ofNat 129548344657874706927201330218), (Int.ofNat 13594128976487977364035243414), (Int.negOfNat 3641492935656856441871795628), (Int.negOfNat 272073248591479043354937814), (Int.ofNat 52068187900680989652401462), (Int.ofNat 2552320313039741370073271), (Int.negOfNat 456174162845187659270795), (Int.negOfNat 14537360298869213471571), (Int.ofNat 2680562496360910822725), (Int.ofNat 55408744669736537704), (Int.negOfNat 11276696540196885549), (Int.negOfNat 340704753344282169), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(3569007716100479316305939509648817/5629499534213120000000000000000000), (-356937774912520023996721586282479/5629499534213120000000000000000000), (-11138713061508334070337751012141/2251799813685248000000000000000000), (-54354870350198705431055392421/562949953421312000000000000000000), (173174679592462569006255065813/11258999068426240000000000000000000), (64774172328937353463600665109/5629499534213120000000000000000000), (6797064488243988682017621707/5629499534213120000000000000000000), (-910373233914214110467948907/2814749767106560000000000000000000), (-136036624295739521677468907/5629499534213120000000000000000000), (26034093950340494826200731/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial151.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial151.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial151.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial151 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 5486072197586705260622245352305177), (Int.negOfNat 932961757915757061089490264523928), (Int.negOfNat 47112193433520974786205399006577), (Int.ofNat 5427524820187785006980292843764), (Int.ofNat 1184103971471690089505431052351), (Int.negOfNat 23601208823873093117076196260), (Int.negOfNat 31294427664624382575101672450), (Int.negOfNat 523389566264352374785550918), (Int.ofNat 519101615406273677306259572), (Int.ofNat 7807790829528526654674084), (Int.negOfNat 5366151820766031689114441), (Int.negOfNat 45745452695798709425843), (Int.ofNat 36872062804273607205528), (Int.ofNat 117793784893600095186), (Int.negOfNat 177894764236094283728), (Int.ofNat 295879495212982002), (Int.ofNat 516328302000750807), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(5486072197586705260622245352305177/11258999068426240000000000000000000), (-116620219739469632636186283065491/1407374883553280000000000000000000), (-47112193433520974786205399006577/11258999068426240000000000000000000), (1356881205046946251745073210941/2814749767106560000000000000000000), (1184103971471690089505431052351/11258999068426240000000000000000000), (-1180060441193654655853809813/562949953421312000000000000000000), (-625888553292487651502033449/225179981368524800000000000000000), (-261694783132176187392775459/5629499534213120000000000000000000), (129775403851568419326564893/2814749767106560000000000000000000), (1951947707382131663668521/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial151.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial151.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial151.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial151 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 3491372142282480786906094284250594), (Int.negOfNat 1025997560604793566237267582942554), (Int.ofNat 5026521106559908944181152841542), (Int.ofNat 9548007367539820834123546400300), (Int.negOfNat 532764403024946008836977257746), (Int.negOfNat 235827062222702802615940503005), (Int.ofNat 8131939271220540137874576196), (Int.ofNat 4386164827877971394229447343), (Int.negOfNat 102030240371340791266773572), (Int.negOfNat 53868569942639754798918257), (Int.ofNat 1084111829814688747557118), (Int.ofNat 439170559964043038062207), (Int.negOfNat 8395914455552777206600), (Int.negOfNat 2484153027868709454800), (Int.ofNat 45731784714857227805), (Int.ofNat 10277227319550050253), (Int.negOfNat 20591761432448031), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(1745686071141240393453047142125297/5629499534213120000000000000000000), (-512998780302396783118633791471277/5629499534213120000000000000000000), (2513260553279954472090576420771/5629499534213120000000000000000000), (95480073675398208341235464003/112589990684262400000000000000000), (-266382201512473004418488628873/5629499534213120000000000000000000), (-47165412444540560523188100601/2251799813685248000000000000000000), (2032984817805135034468644049/2814749767106560000000000000000000), (4386164827877971394229447343/11258999068426240000000000000000000), (-25507560092835197816693393/2814749767106560000000000000000000), (-53868569942639754798918257/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial151.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial151.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial151.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial151 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 1520826596643968467557796925782246), (Int.negOfNat 923922105107823084759945417182317), (Int.ofNat 35154075469248397787017100589595), (Int.negOfNat 828681940184595208757005798614), (Int.negOfNat 1475242982540284250639812402177), (Int.ofNat 96019745425250287834111764040), (Int.ofNat 31063677291236536353722517407), (Int.negOfNat 2094029118164103560067960069), (Int.negOfNat 449320820241889462963638949), (Int.ofNat 27012460207849898212592199), (Int.ofNat 4401240266285946563201828), (Int.negOfNat 227421182371614895356095), (Int.negOfNat 29586430967155102957605), (Int.ofNat 1327135949816931509433), (Int.ofNat 141538013753295280212), (Int.negOfNat 6092242084803925667), (Int.negOfNat 458240420080470588), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(760413298321984233778898462891123/5629499534213120000000000000000000), (-923922105107823084759945417182317/11258999068426240000000000000000000), (7030815093849679557403420117919/2251799813685248000000000000000000), (-414340970092297604378502899307/5629499534213120000000000000000000), (-1475242982540284250639812402177/11258999068426240000000000000000000), (2400493635631257195852794101/281474976710656000000000000000000), (31063677291236536353722517407/11258999068426240000000000000000000), (-2094029118164103560067960069/11258999068426240000000000000000000), (-449320820241889462963638949/11258999068426240000000000000000000), (27012460207849898212592199/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial151.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial151.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial151.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial151 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 211939246302787237165013685737812), (Int.negOfNat 828128618234203314092925704269890), (Int.ofNat 7867675133623182521025353656446), (Int.negOfNat 5597121663351900383076692567715), (Int.ofNat 414531468504323362548967105098), (Int.ofNat 172376274280027417901939083186), (Int.negOfNat 20365239815433685407795167503), (Int.negOfNat 2922439162205909647017649483), (Int.ofNat 370538422734410690274463168), (Int.ofNat 34811667009236361374097624), (Int.negOfNat 3844365786970125096332323), (Int.negOfNat 284803705832495076374338), (Int.ofNat 26208129934007945032109), (Int.ofNat 1635324896039990049569), (Int.negOfNat 125190048374212917225), (Int.negOfNat 7050483850479082155), (Int.ofNat 362525648902418158), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-52984811575696809291253421434453/2814749767106560000000000000000000), (-82812861823420331409292570426989/1125899906842624000000000000000000), (3933837566811591260512676828223/5629499534213120000000000000000000), (-1119424332670380076615338513543/2251799813685248000000000000000000), (207265734252161681274483552549/5629499534213120000000000000000000), (86188137140013708950969541593/5629499534213120000000000000000000), (-20365239815433685407795167503/11258999068426240000000000000000000), (-2922439162205909647017649483/11258999068426240000000000000000000), (5789662855225167035538487/175921860444160000000000000000000), (4351458376154545171762203/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial151.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial151.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial151.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial151 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 1870923378863157088150154848774794), (Int.negOfNat 841550186116708916374454028272552), (Int.negOfNat 8053644305762334745176393299007), (Int.ofNat 502575373468750225220647841569), (Int.ofNat 593536320163478421384756432367), (Int.negOfNat 117682979835117086502396878247), (Int.negOfNat 11715118650173131781103248497), (Int.ofNat 3604537703514783159769943017), (Int.ofNat 175846334080493218661811132), (Int.negOfNat 49441027643963024598180376), (Int.negOfNat 1864230333639671746135077), (Int.ofNat 411211081381962171584062), (Int.ofNat 13557206244819555699091), (Int.negOfNat 2326059335703604809231), (Int.negOfNat 69707479627472803775), (Int.ofNat 9827276953970331845), (Int.ofNat 178650822282463642), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-935461689431578544075077424387397/5629499534213120000000000000000000), (-105193773264588614546806753534069/1407374883553280000000000000000000), (-8053644305762334745176393299007/11258999068426240000000000000000000), (502575373468750225220647841569/11258999068426240000000000000000000), (593536320163478421384756432367/11258999068426240000000000000000000), (-117682979835117086502396878247/11258999068426240000000000000000000), (-11715118650173131781103248497/11258999068426240000000000000000000), (3604537703514783159769943017/11258999068426240000000000000000000), (43961583520123304665452783/2814749767106560000000000000000000), (-6180128455495378074772547/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial151.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial151.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial151.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial151 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 3576756714630191573565643103621807), (Int.negOfNat 858728359577276116386626022808027), (Int.negOfNat 519414485714997726094553277191), (Int.ofNat 726538083124835686899092656147), (Int.negOfNat 286190969194648093210107505274), (Int.ofNat 21315918725608013409518430280), (Int.ofNat 25297502229623741434584612793), (Int.negOfNat 245672083680823357454908369), (Int.negOfNat 500305933862126125027447651), (Int.negOfNat 217107507508933631704601), (Int.ofNat 5298954382386577050997372), (Int.ofNat 28391465502217626072705), (Int.negOfNat 36135728864440474532195), (Int.negOfNat 294567783014158597167), (Int.ofNat 172991088791527497788), (Int.ofNat 2129177163613340533), (Int.negOfNat 564664737473384812), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-3576756714630191573565643103621807/11258999068426240000000000000000000), (-858728359577276116386626022808027/11258999068426240000000000000000000), (-519414485714997726094553277191/11258999068426240000000000000000000), (726538083124835686899092656147/11258999068426240000000000000000000), (-143095484597324046605053752637/5629499534213120000000000000000000), (532897968140200335237960757/281474976710656000000000000000000), (25297502229623741434584612793/11258999068426240000000000000000000), (-245672083680823357454908369/11258999068426240000000000000000000), (-500305933862126125027447651/11258999068426240000000000000000000), (-217107507508933631704601/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial151.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial151.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial151.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial151 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 5292910991826133082533739027110657), (Int.negOfNat 855279585531928229327963098498889), (Int.ofNat 3744683515585061429161024682373), (Int.ofNat 2380519720057138930739709321058), (Int.ofNat 882720038309465061762899301287), (Int.ofNat 119661806396806597134875747908), (Int.negOfNat 18167099766309537158945746096), (Int.negOfNat 3917885309207958030666980757), (Int.ofNat 221377772495083096856863172), (Int.ofNat 55769891391457376782527843), (Int.negOfNat 1668640992486050460246218), (Int.negOfNat 474232762515003561523593), (Int.ofNat 8133447481466232735400), (Int.ofNat 2714342734496566598600), (Int.negOfNat 27440009135319628005), (Int.negOfNat 11403045549979722747), (Int.ofNat 202008319801026631), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-5292910991826133082533739027110657/11258999068426240000000000000000000), (-855279585531928229327963098498889/11258999068426240000000000000000000), (3744683515585061429161024682373/11258999068426240000000000000000000), (1190259860028569465369854660529/5629499534213120000000000000000000), (882720038309465061762899301287/11258999068426240000000000000000000), (29915451599201649283718936977/2814749767106560000000000000000000), (-1135443735394346072434109131/703687441776640000000000000000000), (-3917885309207958030666980757/11258999068426240000000000000000000), (55344443123770774214215793/2814749767106560000000000000000000), (55769891391457376782527843/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial151.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial151.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial151.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial151 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 6953076154628954605051207429788241), (Int.negOfNat 778816286754633853164864585410377), (Int.ofNat 42415187773822566479789130404831), (Int.ofNat 9780537369579053015879636436112), (Int.ofNat 324620058318696328673213489353), (Int.negOfNat 241656101588473598454413885000), (Int.negOfNat 22334234097171482098882035623), (Int.ofNat 4024253824202783378630350882), (Int.ofNat 461360258377870832632205728), (Int.negOfNat 41567230888037602934545216), (Int.negOfNat 5134174001819477577190459), (Int.ofNat 279816896272151677426157), (Int.ofNat 36279243921865161818472), (Int.negOfNat 1302766111384658014214), (Int.negOfNat 176857326435439929672), (Int.ofNat 4117677406020055802), (Int.ofNat 506576855553104593), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-6953076154628954605051207429788241/11258999068426240000000000000000000), (-778816286754633853164864585410377/11258999068426240000000000000000000), (42415187773822566479789130404831/11258999068426240000000000000000000), (611283585598690813492477277257/703687441776640000000000000000000), (324620058318696328673213489353/11258999068426240000000000000000000), (-48331220317694719690882777/2251799813685248000000000000000), (-22334234097171482098882035623/11258999068426240000000000000000000), (2012126912101391689315175441/5629499534213120000000000000000000), (14417508074308463519756429/351843720888320000000000000000000), (-649487982625587545852269/175921860444160000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial151.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial151.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial151.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial151 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 8266164762211169428100219941339404), (Int.negOfNat 502864710514643109241340023298186), (Int.ofNat 87487020100167682634894239200881), (Int.ofNat 1931192930740735109826885344188), (Int.negOfNat 2009307965006795392450337892446), (Int.negOfNat 78782432460913234317029767568), (Int.ofNat 46369448028323806541007322786), (Int.ofNat 2678051783846390755535588272), (Int.negOfNat 636561973897837606467127686), (Int.negOfNat 42882048369891277368728238), (Int.ofNat 5479203460100417950417129), (Int.ofNat 396968749613574516791005), (Int.negOfNat 31682626032316562916829), (Int.negOfNat 2402654285214997033275), (Int.ofNat 129974193362450191296), (Int.ofNat 10388801530723510451), (Int.negOfNat 563304834577756831), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-2066541190552792357025054985334851/2814749767106560000000000000000000), (-251432355257321554620670011649093/5629499534213120000000000000000000), (87487020100167682634894239200881/11258999068426240000000000000000000), (482798232685183777456721336047/2814749767106560000000000000000000), (-1004653982503397696225168946223/5629499534213120000000000000000000), (-4923902028807077144814360473/703687441776640000000000000000000), (23184724014161903270503661393/5629499534213120000000000000000000), (167378236490399422220974267/703687441776640000000000000000000), (-318280986948918803233563843/5629499534213120000000000000000000), (-21441024184945638684364119/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial151.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial151.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial151.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial151 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 8938034728156560324131076437703773), (Int.negOfNat 190959067242800227112955574898210), (Int.ofNat 56210021277370157995762381113880), (Int.negOfNat 9650230001218987978419560917038), (Int.negOfNat 65287838394590510826813731636), (Int.ofNat 383056653686276140646657714768), (Int.ofNat 5750635813797040671158929147), (Int.negOfNat 7321467079079002924499782214), (Int.negOfNat 216208007699036534944431355), (Int.ofNat 81673174814222701638268032), (Int.ofNat 3154178168426649132820555), (Int.negOfNat 585626784516309968375499), (Int.negOfNat 25872835617097799442856), (Int.ofNat 2897102557929998306822), (Int.ofNat 139097267784418655001), (Int.negOfNat 10218143772702737477), (Int.negOfNat 448488973632824374), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-8938034728156560324131076437703773/11258999068426240000000000000000000), (-19095906724280022711295557489821/1125899906842624000000000000000000), (1405250531934253949894059527847/281474976710656000000000000000000), (-4825115000609493989209780458519/5629499534213120000000000000000000), (-16321959598647627706703432909/2814749767106560000000000000000000), (23941040855392258790416107173/703687441776640000000000000000000), (5750635813797040671158929147/11258999068426240000000000000000000), (-3660733539539501462249891107/5629499534213120000000000000000000), (-43241601539807306988886271/2251799813685248000000000000000000), (638071678236114856548969/87960930222080000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial151.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial151.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial151.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial151 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 9161682099558388135389194515155482), (Int.negOfNat 55566453547397752616369044855069), (Int.ofNat 23853898026192355057585764442120), (Int.ofNat 2043170614467162561833676502004), (Int.ofNat 2163005540795192254566332543880), (Int.negOfNat 88590432710874784432815587527), (Int.negOfNat 64958490580320932719154359769), (Int.ofNat 619517523974361029195578842), (Int.ofNat 979654054703496380629219517), (Int.ofNat 8467447579677845031351010), (Int.negOfNat 8907359789402236585554560), (Int.negOfNat 174518998522552605605792), (Int.ofNat 53413454301121480951695), (Int.ofNat 1398456944481168850897), (Int.negOfNat 226739445769175250029), (Int.negOfNat 7004639334235950301), (Int.ofNat 924601349354487031), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-4580841049779194067694597257577741/5629499534213120000000000000000000), (-55566453547397752616369044855069/11258999068426240000000000000000000), (596347450654808876439644111053/281474976710656000000000000000000), (510792653616790640458419125501/2814749767106560000000000000000000), (54075138519879806364158313597/281474976710656000000000000000000), (-88590432710874784432815587527/11258999068426240000000000000000000), (-64958490580320932719154359769/11258999068426240000000000000000000), (309758761987180514597789421/5629499534213120000000000000000000), (979654054703496380629219517/11258999068426240000000000000000000), (846744757967784503135101/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial151.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial151.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial151.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial151 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 9133113025405323063073153225415021), (Int.ofNat 115278105474146166986782199513706), (Int.ofNat 67454873432268866942750194747100), (Int.ofNat 7420289231946071649987503712862), (Int.negOfNat 1435641765473020217000924737017), (Int.negOfNat 431457414201930363602368549906), (Int.ofNat 29897721988879447226617330989), (Int.ofNat 9441773910616060434209127671), (Int.negOfNat 267621029100086108597852035), (Int.negOfNat 113632387619356703962889515), (Int.ofNat 670433611047783989957249), (Int.ofNat 845087177073890745369993), (Int.ofNat 5548005314077822037654), (Int.negOfNat 4261173715143296155313), (Int.negOfNat 58524037628322661776), (Int.ofNat 15818312820962662792), (Int.ofNat 269968920120300755), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-9133113025405323063073153225415021/11258999068426240000000000000000000), (57639052737073083493391099756853/5629499534213120000000000000000000), (674548734322688669427501947471/112589990684262400000000000000000), (3710144615973035824993751856431/5629499534213120000000000000000000), (-1435641765473020217000924737017/11258999068426240000000000000000000), (-215728707100965181801184274953/5629499534213120000000000000000000), (29897721988879447226617330989/11258999068426240000000000000000000), (9441773910616060434209127671/11258999068426240000000000000000000), (-53524205820017221719570407/2251799813685248000000000000000000), (-22726477523871340792577903/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial151.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial151.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial151.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial151 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 8607154197242178569467305651222300), (Int.ofNat 403131222996244690371460502516915), (Int.ofNat 55552950748466026627624364066253), (Int.negOfNat 12297220040088013077819633750360), (Int.negOfNat 2026722711930431444531141590054), (Int.ofNat 400988436963032803144654670933), (Int.ofNat 69882429909460692202671649009), (Int.negOfNat 6424334684136599500980552051), (Int.negOfNat 1206454042588265461309532855), (Int.ofNat 48073955452061913039681555), (Int.ofNat 11567154214063557742474389), (Int.negOfNat 178127303481234881369393), (Int.negOfNat 70615601210908265523506), (Int.ofNat 186258600288314057833), (Int.ofNat 301106906769246931624), (Int.ofNat 1441336103676431448), (Int.negOfNat 1126740437925453685), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-86071541972421785694673056512223/112589990684262400000000000000000), (80626244599248938074292100503383/2251799813685248000000000000000000), (55552950748466026627624364066253/11258999068426240000000000000000000), (-307430501002200326945490843759/281474976710656000000000000000000), (-1013361355965215722265570795027/5629499534213120000000000000000000), (400988436963032803144654670933/11258999068426240000000000000000000), (69882429909460692202671649009/11258999068426240000000000000000000), (-6424334684136599500980552051/11258999068426240000000000000000000), (-241290808517653092261906571/2251799813685248000000000000000000), (9614791090412382607936311/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial151.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial151.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial151.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial151 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 7693276522497240045346735118634188), (Int.ofNat 454470538120832925008162963811967), (Int.negOfNat 24154843443045901942953220454982), (Int.negOfNat 6628951753878879074280147631848), (Int.ofNat 3359263966886484368092200141922), (Int.ofNat 337577704235681081855599292213), (Int.negOfNat 90550400067007910042562800949), (Int.negOfNat 10280919381017226962160155562), (Int.ofNat 1010241769138029696747581797), (Int.ofNat 136462332480932167829944450), (Int.negOfNat 6086481176592556716916720), (Int.negOfNat 1036794417637669644401408), (Int.ofNat 22303833695646159691335), (Int.ofNat 5237883209097283928383), (Int.negOfNat 48850255901424880829), (Int.negOfNat 19663493773207506139), (Int.ofNat 9620677677706191), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-1923319130624310011336683779658547/2814749767106560000000000000000000), (454470538120832925008162963811967/11258999068426240000000000000000000), (-12077421721522950971476610227491/5629499534213120000000000000000000), (-828618969234859884285018453981/1407374883553280000000000000000000), (1679631983443242184046100070961/5629499534213120000000000000000000), (337577704235681081855599292213/11258999068426240000000000000000000), (-90550400067007910042562800949/11258999068426240000000000000000000), (-5140459690508613481080077781/5629499534213120000000000000000000), (1010241769138029696747581797/11258999068426240000000000000000000), (2729246649618643356598889/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial151.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial151.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial151.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial151 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 6876226639814692389531583879506063), (Int.ofNat 392121750122440201955679663217630), (Int.ofNat 17401292342934621434774722012185), (Int.ofNat 15913555625690434309125914993823), (Int.negOfNat 15909586478138793379048538493), (Int.negOfNat 960786826553134271453794817595), (Int.negOfNat 63028375883565874297421473773), (Int.ofNat 15304563785378671209503896594), (Int.ofNat 1370221981180816365909149865), (Int.negOfNat 123127290247014819580360572), (Int.negOfNat 13510645779203954198747985), (Int.ofNat 616263217956167227460899), (Int.ofNat 81979230340997828266704), (Int.negOfNat 2117966031723321231342), (Int.negOfNat 346804461388697293399), (Int.ofNat 5257351149081847037), (Int.ofNat 1189084727597416866), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-6876226639814692389531583879506063/11258999068426240000000000000000000), (39212175012244020195567966321763/1125899906842624000000000000000000), (3480258468586924286954944402437/2251799813685248000000000000000000), (15913555625690434309125914993823/11258999068426240000000000000000000), (-15909586478138793379048538493/11258999068426240000000000000000000), (-192157365310626854290758963519/2251799813685248000000000000000000), (-63028375883565874297421473773/11258999068426240000000000000000000), (7652281892689335604751948297/5629499534213120000000000000000000), (274044396236163273181829973/2251799813685248000000000000000000), (-30781822561753704895090143/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial151.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial151.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial151.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial151 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 5927868613069683285243625554308846), (Int.ofNat 571131583580588984848381996823784), (Int.ofNat 32550564366963771733471434572747), (Int.negOfNat 22538796152353114183575140122246), (Int.negOfNat 8228275830564455764435347360253), (Int.negOfNat 149354999672979556151078189531), (Int.ofNat 189811569759339867039008555893), (Int.ofNat 11488643730336450762812309648), (Int.negOfNat 1961509259077353567902375866), (Int.negOfNat 156787479767554339026765722), (Int.ofNat 12298473695323027555404689), (Int.ofNat 1162525899425645961225795), (Int.negOfNat 53161969532305982629269), (Int.negOfNat 5740627985335453847205), (Int.ofNat 169307788562853343696), (Int.ofNat 21111393239019058989), (Int.negOfNat 370917192454436391), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-2963934306534841642621812777154423/5629499534213120000000000000000000), (71391447947573623106047749602973/1407374883553280000000000000000000), (32550564366963771733471434572747/11258999068426240000000000000000000), (-11269398076176557091787570061123/5629499534213120000000000000000000), (-8228275830564455764435347360253/11258999068426240000000000000000000), (-149354999672979556151078189531/11258999068426240000000000000000000), (189811569759339867039008555893/11258999068426240000000000000000000), (718040233146028172675769353/703687441776640000000000000000000), (-980754629538676783951187933/5629499534213120000000000000000000), (-78393739883777169513382861/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial151.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial151.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial151.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial151 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 4959094552491512500543680420883885), (Int.ofNat 194910445643773823762145581465597), (Int.negOfNat 262901603008440343466658131102763), (Int.negOfNat 61663121995963427583642994223250), (Int.ofNat 2260417641341221248909979528197), (Int.ofNat 2025090919054938142613618156900), (Int.ofNat 79886366564311567500655325370), (Int.negOfNat 26400708748503988008007502262), (Int.negOfNat 1645189368329684150411523092), (Int.ofNat 202284862422950584445468756), (Int.ofNat 15073486372423065683550581), (Int.negOfNat 1056026395177040715441157), (Int.negOfNat 87122329819160784497088), (Int.ofNat 4060025004443249433134), (Int.ofNat 357488211283057340328), (Int.negOfNat 11681830627992478962), (Int.negOfNat 1130996845677136647), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-991818910498302500108736084176777/2251799813685248000000000000000000), (194910445643773823762145581465597/11258999068426240000000000000000000), (-262901603008440343466658131102763/11258999068426240000000000000000000), (-246652487983853710334571976893/45035996273704960000000000000000), (2260417641341221248909979528197/11258999068426240000000000000000000), (20250909190549381426136181569/112589990684262400000000000000000), (7988636656431156750065532537/1125899906842624000000000000000000), (-13200354374251994004003751131/5629499534213120000000000000000000), (-411297342082421037602880773/2814749767106560000000000000000000), (50571215605737646111367189/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial151.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial151.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial151.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial151 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 6011786665116144522292621542145749), (Int.negOfNat 1359957343297685837958049498616730), (Int.negOfNat 417068846877372393292789131571276), (Int.ofNat 33739118833703031345013315275766), (Int.ofNat 19034063292231956838717626602519), (Int.ofNat 519983184342301791589454570098), (Int.negOfNat 307039202756120447982361054576), (Int.negOfNat 16330678956156905158114153563), (Int.ofNat 2848014469610678361526376452), (Int.ofNat 182200516240296695199417317), (Int.negOfNat 17772139668960993578924278), (Int.negOfNat 1225150077388910154093607), (Int.ofNat 80766239901620629745440), (Int.ofNat 5725131137947874301080), (Int.negOfNat 280424966374773745005), (Int.negOfNat 20111924018372223693), (Int.ofNat 732213707231166591), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-6011786665116144522292621542145749/11258999068426240000000000000000000), (-135995734329768583795804949861673/1125899906842624000000000000000000), (-104267211719343098323197282892819/2814749767106560000000000000000000), (16869559416851515672506657637883/5629499534213120000000000000000000), (19034063292231956838717626602519/11258999068426240000000000000000000), (259991592171150895794727285049/5629499534213120000000000000000000), (-19189950172257527998897565911/703687441776640000000000000000000), (-16330678956156905158114153563/11258999068426240000000000000000000), (712003617402669590381594113/2814749767106560000000000000000000), (182200516240296695199417317/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial151.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial151.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial151.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial151 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 9829818106754446835952292054934852), (Int.negOfNat 2035708679372231339645257743874808), (Int.ofNat 204828654450717978801070552201863), (Int.ofNat 154308452958954124266047606751018), (Int.ofNat 4884747095996501131625219618956), (Int.negOfNat 3062844503341838504222958116513), (Int.negOfNat 166305168509387892971834522127), (Int.ofNat 34469300081262467020670613249), (Int.ofNat 2119615712393918543312577869), (Int.negOfNat 258093817845826528489176739), (Int.negOfNat 16211007797970602364359568), (Int.ofNat 1388220054411429263437495), (Int.ofNat 85360413913179412409165), (Int.negOfNat 5628339160391448945153), (Int.negOfNat 331943532913341139012), (Int.ofNat 17478193217583422627), (Int.ofNat 1072908963756856428), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-2457454526688611708988073013733713/2814749767106560000000000000000000), (-254463584921528917455657217984351/1407374883553280000000000000000000), (204828654450717978801070552201863/11258999068426240000000000000000000), (77154226479477062133023803375509/5629499534213120000000000000000000), (1221186773999125282906304904739/2814749767106560000000000000000000), (-3062844503341838504222958116513/11258999068426240000000000000000000), (-166305168509387892971834522127/11258999068426240000000000000000000), (34469300081262467020670613249/11258999068426240000000000000000000), (2119615712393918543312577869/11258999068426240000000000000000000), (-258093817845826528489176739/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial151.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial151.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial151.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial151 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 11873142735648189653829086898467028), (Int.ofNat 531613614602880010100312455886459), (Int.ofNat 988602031222046521029299381275961), (Int.ofNat 65794863490889016872034602469317), (Int.negOfNat 24888033673463508258425888974164), (Int.negOfNat 1816971903979412846437104607306), (Int.ofNat 349886440367082225065123992656), (Int.ofNat 24418492918839621559756273603), (Int.negOfNat 3213826439235865848090677348), (Int.negOfNat 205487009185028162187509384), (Int.ofNat 20759785864572364379910083), (Int.ofNat 1199158956661899009309338), (Int.negOfNat 99014289857453456392949), (Int.negOfNat 5153452530205883172449), (Int.ofNat 360931247789336228225), (Int.ofNat 16885180549301255595), (Int.negOfNat 1074147594701136718), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-2968285683912047413457271724616757/2814749767106560000000000000000000), (531613614602880010100312455886459/11258999068426240000000000000000000), (988602031222046521029299381275961/11258999068426240000000000000000000), (65794863490889016872034602469317/11258999068426240000000000000000000), (-6222008418365877064606472243541/2814749767106560000000000000000000), (-908485951989706423218552303653/5629499534213120000000000000000000), (21867902522942639066570249541/703687441776640000000000000000000), (24418492918839621559756273603/11258999068426240000000000000000000), (-803456609808966462022669337/2814749767106560000000000000000000), (-25685876148128520273438673/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial151.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial151.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial151.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial151.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial151 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial151 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial151 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 13210681962142748187741669540233141), (Int.negOfNat 963540782901928999772474118364061), (Int.ofNat 1028387455471312345823905779505200), (Int.negOfNat 59070065582751512580187674281893), (Int.negOfNat 25344161842026237057940481783999), (Int.ofNat 1754345407686604262654163328433), (Int.ofNat 353134922215323917294831820083), (Int.negOfNat 24077320918633648873365249803), (Int.negOfNat 3227417570623342316041848848), (Int.ofNat 204365092727375557619835884), (Int.ofNat 20795663515027157910091483), (Int.negOfNat 1196732873166429312993338), (Int.negOfNat 99079940333345625296949), (Int.ofNat 5150468417665330040449), (Int.ofNat 360931247789336228225), (Int.negOfNat 16885180549301255595), (Int.negOfNat 1074147594701136718), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-13210681962142748187741669540233141/11258999068426240000000000000000000), (-963540782901928999772474118364061/11258999068426240000000000000000000), (2570968638678280864559764448763/28147497671065600000000000000000), (-59070065582751512580187674281893/11258999068426240000000000000000000), (-25344161842026237057940481783999/11258999068426240000000000000000000), (1754345407686604262654163328433/11258999068426240000000000000000000), (353134922215323917294831820083/11258999068426240000000000000000000), (-24077320918633648873365249803/11258999068426240000000000000000000), (-201713598163958894752615553/703687441776640000000000000000000), (51091273181843889404958971/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial151.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial151.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial151.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 11827326127644617628926963493629253), (Int.ofNat 1824774822481258956022036333189538), (Int.ofNat 269985525252316574927175568871467), (Int.negOfNat 153056668274348950562013387880497), (Int.ofNat 4073620651724075645805614862765), (Int.ofNat 3059861021446417173928543708720), (Int.negOfNat 160404550305542726439104309127), (Int.negOfNat 34461888917399390492472457349), (Int.ofNat 2094845895875587610978419469), (Int.ofNat 258073728609385415148789839), (Int.negOfNat 16145589838758876630154468), (Int.negOfNat 1388178276835861519589495), (Int.ofNat 85242541467827563695165), (Int.ofNat 5628339160391448945153), (Int.negOfNat 331943532913341139012), (Int.negOfNat 17478193217583422627), (Int.ofNat 1072908963756856428), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-11827326127644617628926963493629253/11258999068426240000000000000000000), (912387411240629478011018166594769/5629499534213120000000000000000000), (269985525252316574927175568871467/11258999068426240000000000000000000), (-153056668274348950562013387880497/11258999068426240000000000000000000), (814724130344815129161122972553/2251799813685248000000000000000000), (38248262768080214674106796359/140737488355328000000000000000000), (-160404550305542726439104309127/11258999068426240000000000000000000), (-34461888917399390492472457349/11258999068426240000000000000000000), (2094845895875587610978419469/11258999068426240000000000000000000), (258073728609385415148789839/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial151.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial151.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial151.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 8173221830205589982438229285168892), (Int.ofNat 1399588821909099260844492672029615), (Int.negOfNat 362729585716038384561945518273808), (Int.negOfNat 38190937915075406177362238840961), (Int.ofNat 18522257238056334398163073673400), (Int.negOfNat 462157132548724977920584563692), (Int.negOfNat 303608992195160642695021115176), (Int.ofNat 15998974315908401784421913263), (Int.ofNat 2833806173208266712670163752), (Int.negOfNat 181101657069852471863109917), (Int.negOfNat 17734684447850613226743378), (Int.ofNat 1222771739694089307889607), (Int.ofNat 80697605313187907709440), (Int.negOfNat 5722147025407321169080), (Int.negOfNat 280424966374773745005), (Int.ofNat 20111924018372223693), (Int.ofNat 732213707231166591), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-2043305457551397495609557321292223/2814749767106560000000000000000000), (279917764381819852168898534405923/2251799813685248000000000000000000), (-22670599107252399035121594892113/703687441776640000000000000000000), (-38190937915075406177362238840961/11258999068426240000000000000000000), (92611286190281671990815368367/56294995342131200000000000000000), (-115539283137181244480146140923/2814749767106560000000000000000000), (-37951124024395080336877639397/1407374883553280000000000000000000), (15998974315908401784421913263/11258999068426240000000000000000000), (354225771651033339083770469/1407374883553280000000000000000000), (-181101657069852471863109917/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial151.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial151.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial151.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 6865688697765472750151510278604049), (Int.negOfNat 2597318226189255395039483038846), (Int.negOfNat 242350209695819939442710298415816), (Int.ofNat 55773890135600394493975135611238), (Int.ofNat 2428720464399767104258220780661), (Int.negOfNat 1957889450246152953106941197880), (Int.ofNat 77907343157092544486321291897), (Int.ofNat 26022017931443330046643902662), (Int.negOfNat 1636389337191131311355229692), (Int.negOfNat 201033472632190148770758856), (Int.ofNat 15050059729481081036667481), (Int.ofNat 1053318313046488748151157), (Int.negOfNat 87079060187322764083088), (Int.negOfNat 4055548835632419735134), (Int.ofNat 357488211283057340328), (Int.ofNat 11681830627992478962), (Int.negOfNat 1130996845677136647), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-6865688697765472750151510278604049/11258999068426240000000000000000000), (-1298659113094627697519741519423/5629499534213120000000000000000000), (-30293776211977492430338787301977/1407374883553280000000000000000000), (27886945067800197246987567805619/5629499534213120000000000000000000), (2428720464399767104258220780661/11258999068426240000000000000000000), (-48947236256153823827673529947/281474976710656000000000000000000), (77907343157092544486321291897/11258999068426240000000000000000000), (13011008965721665023321951331/5629499534213120000000000000000000), (-409097334297782827838807423/2814749767106560000000000000000000), (-25129184079023768596344857/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial151.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial151.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial151.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 7410073758703564067233246804982869), (Int.negOfNat 357059738144293849997466510267392), (Int.ofNat 26473699329553502122547444847703), (Int.ofNat 20177363827472373769529243252454), (Int.negOfNat 7598253982387804534575825832106), (Int.ofNat 167199949031601480554321398005), (Int.ofNat 184242007859719655883539922166), (Int.negOfNat 11581631326624551683569029848), (Int.negOfNat 1937485552166052309249642266), (Int.ofNat 157091216632824049350643122), (Int.ofNat 12234781041355181480497789), (Int.negOfNat 1163182404184567650265795), (Int.negOfNat 53047081199494687047269), (Int.ofNat 5742120041605730413205), (Int.ofNat 169307788562853343696), (Int.negOfNat 21111393239019058989), (Int.negOfNat 370917192454436391), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-7410073758703564067233246804982869/11258999068426240000000000000000000), (-348691150531536962888150888933/10995116277760000000000000000000), (26473699329553502122547444847703/11258999068426240000000000000000000), (10088681913736186884764621626227/5629499534213120000000000000000000), (-3799126991193902267287912916053/5629499534213120000000000000000000), (33439989806320296110864279601/2251799813685248000000000000000000), (92121003929859827941769961083/5629499534213120000000000000000000), (-1447703915828068960446128731/1407374883553280000000000000000000), (-968742776083026154624821133/5629499534213120000000000000000000), (78545608316412024675321561/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial151.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial151.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial151.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 7963197740253374567946023284258043), (Int.negOfNat 210192302517090747937366242575690), (Int.ofNat 12348476909721756967011648113806), (Int.negOfNat 13420527670074499332705952520013), (Int.ofNat 459613775189165496606071261623), (Int.ofNat 914839842272670311973338634075), (Int.negOfNat 67221804047025764356873871973), (Int.negOfNat 15031087166806147681733673294), (Int.ofNat 1388304338684843798314417965), (Int.ofNat 122216769033199370539033372), (Int.negOfNat 13558583699473857754642685), (Int.negOfNat 614289227510591330642899), (Int.ofNat 82065769604673869094704), (Int.ofNat 2114981919182768099342), (Int.negOfNat 346804461388697293399), (Int.negOfNat 5257351149081847037), (Int.ofNat 1189084727597416866), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-7963197740253374567946023284258043/11258999068426240000000000000000000), (-21019230251709074793736624257569/1125899906842624000000000000000000), (6174238454860878483505824056903/5629499534213120000000000000000000), (-13420527670074499332705952520013/11258999068426240000000000000000000), (459613775189165496606071261623/11258999068426240000000000000000000), (36593593690906812478933545363/450359962737049600000000000000000), (-67221804047025764356873871973/11258999068426240000000000000000000), (-7515543583403073840866836647/5629499534213120000000000000000000), (277660867736968759662883593/2251799813685248000000000000000000), (30554192258299842634758343/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial151.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial151.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial151.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 8410746951741341014116106749827984), (Int.negOfNat 251961451401012206911532783728735), (Int.negOfNat 7307619126165480080372271691556), (Int.ofNat 10597350060253415827613279934052), (Int.ofNat 3216315082526642079877506334914), (Int.negOfNat 404929062337787599209967301600), (Int.negOfNat 89629326343029081262690336449), (Int.ofNat 10678814137135527714531642062), (Int.ofNat 1006452785446766271058579497), (Int.negOfNat 137785775044519565273600350), (Int.negOfNat 6076502527337131560745120), (Int.ofNat 1039662149789141204253408), (Int.ofNat 22285929020402840899335), (Int.negOfNat 5242359377908113626383), (Int.negOfNat 48850255901424880829), (Int.ofNat 19663493773207506139), (Int.ofNat 9620677677706191), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-525671684483833813382256671864249/703687441776640000000000000000000), (-50392290280202441382306556745747/2251799813685248000000000000000000), (-1826904781541370020093067922889/2814749767106560000000000000000000), (2649337515063353956903319983513/2814749767106560000000000000000000), (1608157541263321039938753167457/5629499534213120000000000000000000), (-506161327922234499012459127/14073748835532800000000000000000), (-89629326343029081262690336449/11258999068426240000000000000000000), (5339407068567763857265821031/5629499534213120000000000000000000), (1006452785446766271058579497/11258999068426240000000000000000000), (-2755715500890391305472007/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial151.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial151.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial151.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 8824804547292316113602155039457254), (Int.negOfNat 95226675694213619424848610035383), (Int.ofNat 87867431502291934303625474630191), (Int.ofNat 12784532211844551673344159601399), (Int.negOfNat 2685838632455648333719823675716), (Int.negOfNat 428067261139784587600567530206), (Int.ofNat 75134231552712534712198191609), (Int.ofNat 6594829676319334954968386251), (Int.negOfNat 1228798419113878260967992155), (Int.negOfNat 48645735478361580022472755), (Int.ofNat 11626279927885807223356389), (Int.ofNat 179368694298104984281393), (Int.negOfNat 70721537206097901709506), (Int.negOfNat 187750656558590623833), (Int.ofNat 301106906769246931624), (Int.negOfNat 1441336103676431448), (Int.negOfNat 1126740437925453685), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-4412402273646158056801077519728627/5629499534213120000000000000000000), (-95226675694213619424848610035383/11258999068426240000000000000000000), (87867431502291934303625474630191/11258999068426240000000000000000000), (12784532211844551673344159601399/11258999068426240000000000000000000), (-671459658113912083429955918929/2814749767106560000000000000000000), (-214033630569892293800283765103/5629499534213120000000000000000000), (75134231552712534712198191609/11258999068426240000000000000000000), (6594829676319334954968386251/11258999068426240000000000000000000), (-245759683822775652193598431/2251799813685248000000000000000000), (-9729147095672316004494551/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial151.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial151.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial151.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 8612858249177470051454558842747047), (Int.ofNat 305534939148345141272218439448499), (Int.ofNat 86041176924558993336480596112862), (Int.negOfNat 12395458855197315235659869185083), (Int.negOfNat 2029197380890708122385014384795), (Int.ofNat 471060968340587833607695312593), (Int.ofNat 34860031531303004435291032589), (Int.negOfNat 9650663898292631695772587871), (Int.negOfNat 288872459504439646731030735), (Int.ofNat 114315984526714293816868915), (Int.ofNat 726718672811611406411649), (Int.negOfNat 846564312781464545709993), (Int.ofNat 5446545487699015549654), (Int.ofNat 4264157827683849287313), (Int.negOfNat 58524037628322661776), (Int.negOfNat 15818312820962662792), (Int.ofNat 269968920120300755), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-8612858249177470051454558842747047/11258999068426240000000000000000000), (305534939148345141272218439448499/11258999068426240000000000000000000), (43020588462279496668240298056431/5629499534213120000000000000000000), (-12395458855197315235659869185083/11258999068426240000000000000000000), (-405839476178141624477002876959/2251799813685248000000000000000000), (471060968340587833607695312593/11258999068426240000000000000000000), (34860031531303004435291032589/11258999068426240000000000000000000), (-9650663898292631695772587871/11258999068426240000000000000000000), (-57774491900887929346206147/2251799813685248000000000000000000), (22863196905342858763373783/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial151.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial151.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial151.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 7773201139474628602536268965854306), (Int.ofNat 476036444732261114408988446904081), (Int.ofNat 2528381347476646933873961817421), (Int.negOfNat 9539267969695000292986900786340), (Int.ofNat 2184371644053944555263396270828), (Int.ofNat 162453199873834732913182290140), (Int.negOfNat 64679567239210345033650247969), (Int.negOfNat 1026033455546127166771228442), (Int.ofNat 978199773312501994022272517), (Int.negOfNat 7128652342050966256977810), (Int.negOfNat 8903410672092626748471860), (Int.ofNat 171621425245675514433792), (Int.ofNat 53407486076040374687695), (Int.negOfNat 1393980775670339152897), (Int.negOfNat 226739445769175250029), (Int.ofNat 7004639334235950301), (Int.ofNat 924601349354487031), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-3886600569737314301268134482927153/5629499534213120000000000000000000), (476036444732261114408988446904081/11258999068426240000000000000000000), (2528381347476646933873961817421/11258999068426240000000000000000000), (-476963398484750014649345039317/562949953421312000000000000000000), (546092911013486138815849067707/2814749767106560000000000000000000), (8122659993691736645659114507/562949953421312000000000000000000), (-64679567239210345033650247969/11258999068426240000000000000000000), (-513016727773063583385614221/5629499534213120000000000000000000), (978199773312501994022272517/11258999068426240000000000000000000), (-712865234205096625697781/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial151.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial151.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial151.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 6851213036719730462443816725067753), (Int.ofNat 442639577315397012439604250736610), (Int.negOfNat 3872981558853841178867839634621), (Int.ofNat 5101081033558867654608435031368), (Int.ofNat 601317516869179513278151909775), (Int.negOfNat 337999736842475368572781425995), (Int.ofNat 1046111388105790030564100447), (Int.ofNat 7073265486799558756264082514), (Int.negOfNat 196553647924021313380952355), (Int.negOfNat 80855656230237490342769332), (Int.ofNat 3102304405778405055789555), (Int.ofNat 583857205779761961099499), (Int.negOfNat 25780328128340652350856), (Int.negOfNat 2894118445389445174822), (Int.ofNat 139097267784418655001), (Int.ofNat 10218143772702737477), (Int.negOfNat 448488973632824374), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-6851213036719730462443816725067753/11258999068426240000000000000000000), (44263957731539701243960425073661/1125899906842624000000000000000000), (-3872981558853841178867839634621/11258999068426240000000000000000000), (637635129194858456826054378921/1407374883553280000000000000000000), (24052700674767180531126076391/450359962737049600000000000000000), (-67599947368495073714556285199/2251799813685248000000000000000000), (1046111388105790030564100447/11258999068426240000000000000000000), (3536632743399779378132041257/5629499534213120000000000000000000), (-39310729584804262676190471/2251799813685248000000000000000000), (-20213914057559372585692333/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial151.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial151.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial151.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 5940927212310684999732559711083834), (Int.ofNat 483566609885833973564849027047558), (Int.ofNat 18454675059237113402674062099305), (Int.negOfNat 198183838572109915763633748180), (Int.negOfNat 1219351409511868369646084887013), (Int.ofNat 56529030501883272779609685582), (Int.ofNat 40746343899002278834163299186), (Int.negOfNat 2550588687673386800892142172), (Int.negOfNat 613037702063864080033224186), (Int.ofNat 42459879728986474274363738), (Int.ofNat 5417106127888238843154129), (Int.negOfNat 396054119119894981833005), (Int.negOfNat 31570721812045820466829), (Int.ofNat 2401162228944720467275), (Int.ofNat 129974193362450191296), (Int.negOfNat 10388801530723510451), (Int.negOfNat 563304834577756831), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-2970463606155342499866279855541917/5629499534213120000000000000000000), (241783304942916986782424513523779/5629499534213120000000000000000000), (3690935011847422680534812419861/2251799813685248000000000000000000), (-9909191928605495788181687409/562949953421312000000000000000000), (-1219351409511868369646084887013/11258999068426240000000000000000000), (28264515250941636389804842791/5629499534213120000000000000000000), (20373171949501139417081649593/5629499534213120000000000000000000), (-637647171918346700223035543/2814749767106560000000000000000000), (-306518851031932040016612093/5629499534213120000000000000000000), (21229939864493237137181869/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial151.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial151.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial151.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 4917110735985039975404317487832577), (Int.ofNat 526683531347700738274244161605128), (Int.negOfNat 264779538478090538154199716023), (Int.negOfNat 3407346455061316554728846885964), (Int.ofNat 614208548660213726350903378249), (Int.ofNat 171857142573674590897845603460), (Int.negOfNat 24010763534059120845789640750), (Int.negOfNat 3633359069843359505322017082), (Int.ofNat 468117413943335898253680228), (Int.ofNat 40276651178877331526782116), (Int.negOfNat 5151914683430693662813359), (Int.negOfNat 277023766934193945874157), (Int.ofNat 36312069159811246270472), (Int.ofNat 1298289942573828316214), (Int.negOfNat 176857326435439929672), (Int.negOfNat 4117677406020055802), (Int.ofNat 506576855553104593), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-4917110735985039975404317487832577/11258999068426240000000000000000000), (65835441418462592284280520200641/1407374883553280000000000000000000), (-264779538478090538154199716023/11258999068426240000000000000000000), (-851836613765329138682211721491/2814749767106560000000000000000000), (614208548660213726350903378249/11258999068426240000000000000000000), (8592857128683729544892280173/562949953421312000000000000000000), (-96043054136236483383158563/45035996273704960000000000000000), (-1816679534921679752661008541/5629499534213120000000000000000000), (117029353485833974563420057/2814749767106560000000000000000000), (10069162794719332881695529/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial151.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial151.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial151.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 3878601783423067213681280919698794), (Int.ofNat 512445281034716865563735715198754), (Int.ofNat 536420531023711275187626735058), (Int.ofNat 3473095594241550926911387451100), (Int.ofNat 485424112639960066914894041146), (Int.negOfNat 176377224368709097486857570995), (Int.negOfNat 14498949730935131249528553996), (Int.ofNat 4229100047369677474511077657), (Int.ofNat 205471868797474000398512172), (Int.negOfNat 56794381998090371348163743), (Int.negOfNat 1626442901147808595135318), (Int.ofNat 476448466076364262033593), (Int.ofNat 8057352611682127869400), (Int.negOfNat 2717326847037119730600), (Int.negOfNat 27440009135319628005), (Int.ofNat 11403045549979722747), (Int.ofNat 202008319801026631), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-1939300891711533606840640459849397/5629499534213120000000000000000000), (256222640517358432781867857599377/5629499534213120000000000000000000), (268210265511855637593813367529/5629499534213120000000000000000000), (34730955942415509269113874511/112589990684262400000000000000000), (242712056319980033457447020573/5629499534213120000000000000000000), (-35275444873741819497371514199/2251799813685248000000000000000000), (-3624737432733782812382138499/2814749767106560000000000000000000), (4229100047369677474511077657/11258999068426240000000000000000000), (51367967199368500099628043/2814749767106560000000000000000000), (-56794381998090371348163743/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial151.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial151.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial151.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 2822021824778776660283138293793046), (Int.ofNat 556878983782197298501402488944117), (Int.ofNat 18378489752195140753525464240205), (Int.ofNat 407998648068003526351620314014), (Int.negOfNat 964707294233641898844305476623), (Int.negOfNat 16665604409128207008581864640), (Int.ofNat 31022137125744086642501097393), (Int.ofNat 204827877529501776935223469), (Int.negOfNat 524851612462251963688550651), (Int.ofNat 358930199145375700169001), (Int.ofNat 5363974053096695743433972), (Int.negOfNat 28701813206435151800705), (Int.negOfNat 36253601309792323246195), (Int.ofNat 294567783014158597167), (Int.ofNat 172991088791527497788), (Int.negOfNat 2129177163613340533), (Int.negOfNat 564664737473384812), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-1411010912389388330141569146896523/5629499534213120000000000000000000), (556878983782197298501402488944117/11258999068426240000000000000000000), (3675697950439028150705092848041/2251799813685248000000000000000000), (203999324034001763175810157007/5629499534213120000000000000000000), (-964707294233641898844305476623/11258999068426240000000000000000000), (-52080013778525646901818327/35184372088832000000000000000000), (31022137125744086642501097393/11258999068426240000000000000000000), (204827877529501776935223469/11258999068426240000000000000000000), (-524851612462251963688550651/11258999068426240000000000000000000), (358930199145375700169001/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial151.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial151.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial151.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 1645571777975934055565389908611388), (Int.ofNat 608622721050618681264926879524090), (Int.ofNat 3042978923187623713760157338154), (Int.negOfNat 3759338571178067847710178436885), (Int.ofNat 267491799794611280969822305702), (Int.ofNat 177391051636458853464669938414), (Int.negOfNat 9008933156662182918977774097), (Int.negOfNat 3959758266154618690159268517), (Int.ofNat 164268063229589775214121432), (Int.ofNat 50623637044938213089488576), (Int.negOfNat 1833569957801666332782877), (Int.negOfNat 413772941998027035406062), (Int.ofNat 13500508106549046191091), (Int.ofNat 2330535504514434507231), (Int.negOfNat 68215423357196237775), (Int.negOfNat 9827276953970331845), (Int.ofNat 178650822282463642), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-411392944493983513891347477152847/2814749767106560000000000000000000), (60862272105061868126492687952409/1125899906842624000000000000000000), (1521489461593811856880078669077/5629499534213120000000000000000000), (-751867714235613569542035687377/2251799813685248000000000000000000), (133745899897305640484911152851/5629499534213120000000000000000000), (88695525818229426732334969207/5629499534213120000000000000000000), (-9008933156662182918977774097/11258999068426240000000000000000000), (-3959758266154618690159268517/11258999068426240000000000000000000), (20533507903698721901765179/1407374883553280000000000000000000), (790994328827159579523259/175921860444160000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial151.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial151.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial151.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 437290847187677841483066470269006), (Int.ofNat 595201153168330218141261365304752), (Int.negOfNat 3228948095213214955322277676993), (Int.ofNat 2340358465643032678764663200631), (Int.ofNat 740575988875475020221893172033), (Int.negOfNat 112668202478825789225274018753), (Int.negOfNat 23071425308944634269920641903), (Int.ofNat 2567218599566074116628323983), (Int.ofNat 382116693585314133722152868), (Int.negOfNat 33629057608261172882789424), (Int.negOfNat 3875026162808130509684523), (Int.ofNat 282241845216430212552338), (Int.ofNat 26264828072278454540109), (Int.negOfNat 1630848727229160351569), (Int.negOfNat 126682104644489483225), (Int.ofNat 7050483850479082155), (Int.ofNat 362525648902418158), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-218645423593838920741533235134503/5629499534213120000000000000000000), (37200072073020638633828835331547/703687441776640000000000000000000), (-3228948095213214955322277676993/11258999068426240000000000000000000), (2340358465643032678764663200631/11258999068426240000000000000000000), (740575988875475020221893172033/11258999068426240000000000000000000), (-112668202478825789225274018753/11258999068426240000000000000000000), (-23071425308944634269920641903/11258999068426240000000000000000000), (2567218599566074116628323983/11258999068426240000000000000000000), (95529173396328533430538217/2814749767106560000000000000000000), (-2101816100516323305174339/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial151.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial151.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial151.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 766091706795727162471456206847407), (Int.ofNat 622072729313355668558985358324027), (Int.ofNat 16256171231434399005431812333391), (Int.ofNat 1963218671374645807151160436053), (Int.negOfNat 796726657501488629356816726126), (Int.negOfNat 91369431108460768440701755280), (Int.ofNat 25339042395116191145806032807), (Int.ofNat 2053184912012781979548275169), (Int.negOfNat 424775141641763624302535949), (Int.negOfNat 26870637516213456144127799), (Int.ofNat 4336220595575827870765228), (Int.ofNat 227110834667397369628095), (Int.negOfNat 29468558521803254243605), (Int.negOfNat 1327135949816931509433), (Int.ofNat 141538013753295280212), (Int.ofNat 6092242084803925667), (Int.negOfNat 458240420080470588), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(766091706795727162471456206847407/11258999068426240000000000000000000), (622072729313355668558985358324027/11258999068426240000000000000000000), (16256171231434399005431812333391/11258999068426240000000000000000000), (1963218671374645807151160436053/11258999068426240000000000000000000), (-398363328750744314678408363063/5629499534213120000000000000000000), (-1142117888855759605508771941/140737488355328000000000000000000), (25339042395116191145806032807/11258999068426240000000000000000000), (2053184912012781979548275169/11258999068426240000000000000000000), (-424775141641763624302535949/11258999068426240000000000000000000), (-26870637516213456144127799/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial151.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial151.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial151.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 2077062933884166448085919732034257), (Int.ofNat 683163256108515134819748404028089), (Int.ofNat 8234784091167109800735873919427), (Int.negOfNat 3694392053251273962930110428658), (Int.negOfNat 135468477355957457021735162087), (Int.ofNat 179111644250858530411467492492), (Int.ofNat 4463789235846134228457384096), (Int.negOfNat 4074950089716251950385350443), (Int.negOfNat 86124336673731694808422572), (Int.ofNat 52844079336006760233282357), (Int.ofNat 1041913738476446882446218), (Int.negOfNat 436954856402682337552207), (Int.negOfNat 8319819585768672340600), (Int.ofNat 2481168915328156322800), (Int.ofNat 45731784714857227805), (Int.negOfNat 10277227319550050253), (Int.negOfNat 20591761432448031), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(2077062933884166448085919732034257/11258999068426240000000000000000000), (683163256108515134819748404028089/11258999068426240000000000000000000), (8234784091167109800735873919427/11258999068426240000000000000000000), (-1847196026625636981465055214329/5629499534213120000000000000000000), (-135468477355957457021735162087/11258999068426240000000000000000000), (44777911062714632602866873123/2814749767106560000000000000000000), (139493413620191694639293253/351843720888320000000000000000000), (-4074950089716251950385350443/11258999068426240000000000000000000), (-21531084168432923702105643/2814749767106560000000000000000000), (52844079336006760233282357/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial151.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial151.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial151.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3450106778949449114745121145809241), (Int.ofNat 680829002509763840916491932482177), (Int.negOfNat 4432226121266854952299126019631), (Int.ofNat 945666094316559940457422808888), (Int.ofNat 894515481131406720004933767047), (Int.negOfNat 46197750190747050899270569400), (Int.negOfNat 29617898227698018573580547177), (Int.ofNat 914284320623776248093884718), (Int.ofNat 512344459840808611684785072), (Int.negOfNat 9098370538688798062437184), (Int.negOfNat 5348411139154815603491541), (Int.ofNat 48538582033756440977843), (Int.ofNat 36839237566327522753528), (Int.negOfNat 122269953704429793186), (Int.negOfNat 177894764236094283728), (Int.negOfNat 295879495212982002), (Int.ofNat 516328302000750807), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(3450106778949449114745121145809241/11258999068426240000000000000000000), (680829002509763840916491932482177/11258999068426240000000000000000000), (-4432226121266854952299126019631/11258999068426240000000000000000000), (118208261789569992557177851111/1407374883553280000000000000000000), (894515481131406720004933767047/11258999068426240000000000000000000), (-230988750953735254496352847/56294995342131200000000000000000), (-29617898227698018573580547177/11258999068426240000000000000000000), (457142160311888124046942359/5629499534213120000000000000000000), (32021528740050538230299067/703687441776640000000000000000000), (-142162039667012469725581/175921860444160000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial151.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial151.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial151.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4812777882308732024972859191377404), (Int.ofNat 694577449196846548789425402773386), (Int.ofNat 13338779733292176996142063344719), (Int.ofNat 2820106499168016039748984178212), (Int.negOfNat 616781875903280444787701901154), (Int.negOfNat 151801746616924171357516704632), (Int.ofNat 19217233105809505070879267014), (Int.ofNat 3768956031829860396515241728), (Int.negOfNat 295597520425452569788841314), (Int.negOfNat 52490356541585792746765962), (Int.ofNat 2614417645251920477336271), (Int.ofNat 457088793338867194228795), (Int.negOfNat 14649264519139955921571), (Int.negOfNat 2682054552631187388725), (Int.ofNat 55408744669736537704), (Int.ofNat 11276696540196885549), (Int.negOfNat 340704753344282169), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(1203194470577183006243214797844351/2814749767106560000000000000000000), (347288724598423274394712701386693/5629499534213120000000000000000000), (13338779733292176996142063344719/11258999068426240000000000000000000), (705026624792004009937246044553/2814749767106560000000000000000000), (-308390937951640222393850950577/5629499534213120000000000000000000), (-18975218327115521419689588079/1407374883553280000000000000000000), (9608616552904752535439633507/5629499534213120000000000000000000), (14722484499335392173887663/43980465111040000000000000000000), (-147798760212726284894420657/5629499534213120000000000000000000), (-26245178270792896373382981/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial151.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial151.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial151.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 6264735899558512955538950429201373), (Int.ofNat 754865298439107662677773071548810), (Int.ofNat 9727403236358734029966999329120), (Int.negOfNat 3755653927473385476797567763362), (Int.negOfNat 417474317707274055490808607364), (Int.ofNat 189467640311798249557549343232), (Int.ofNat 17758320154978377287734820253), (Int.negOfNat 4220347148588117465146132786), (Int.negOfNat 373901514017121519409601045), (Int.ofNat 50635279086920340292987968), (Int.ofNat 4480827510354648798355245), (Int.negOfNat 369801111821158011017301), (Int.negOfNat 33693023471848464458344), (Int.ofNat 1797950195186474488378), (Int.ofNat 172301897442111282599), (Int.negOfNat 6128599983697649923), (Int.negOfNat 574416183921031026), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(6264735899558512955538950429201373/11258999068426240000000000000000000), (75486529843910766267777307154881/1125899906842624000000000000000000), (60796270227242087687293745807/70368744177664000000000000000000), (-1877826963736692738398783881681/5629499534213120000000000000000000), (-104368579426818513872702151841/2814749767106560000000000000000000), (370053984983980956167088561/21990232555520000000000000000000), (17758320154978377287734820253/11258999068426240000000000000000000), (-2110173574294058732573066393/5629499534213120000000000000000000), (-74780302803424303881920209/2251799813685248000000000000000000), (791176235733130317077937/175921860444160000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial151.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial151.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial151.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 7783244498202545445458459662033482), (Int.ofNat 751776029716121072941932545933269), (Int.negOfNat 6640000267445659283867978133720), (Int.ofNat 613427785918920865716063413396), (Int.ofNat 1187540491999157711908407296920), (Int.ofNat 5158557740915045124773664527), (Int.negOfNat 41074431933138499985977196831), (Int.negOfNat 1156869473167535183739381442), (Int.ofNat 689178484424705862917071883), (Int.ofNat 28375621290980140994474390), (Int.negOfNat 6552817694486727449988240), (Int.negOfNat 323164575287985882948408), (Int.ofNat 39408401608738956937105), (Int.ofNat 2166059184925411442503), (Int.negOfNat 164077052152692280371), (Int.negOfNat 9828797074385332699), (Int.ofNat 702001268121012369), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(3891622249101272722729229831016741/5629499534213120000000000000000000), (751776029716121072941932545933269/11258999068426240000000000000000000), (-166000006686141482096699453343/281474976710656000000000000000000), (153356946479730216429015853349/2814749767106560000000000000000000), (29688512299978942797710182423/281474976710656000000000000000000), (5158557740915045124773664527/11258999068426240000000000000000000), (-41074431933138499985977196831/11258999068426240000000000000000000), (-578434736583767591869690721/5629499534213120000000000000000000), (689178484424705862917071883/11258999068426240000000000000000000), (2837562129098014099447439/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial151.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial151.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial151.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 9281716619900476969791690095674421), (Int.ofNat 763321542503643003802609816552094), (Int.ofNat 16603057695008335416995142491700), (Int.ofNat 4378526706378032998406560836538), (Int.negOfNat 759097820477490466462485018583), (Int.negOfNat 276836128484684305308115281494), (Int.ofNat 14850476518190886122007571211), (Int.ofNat 7111003603450409315260516929), (Int.negOfNat 42418501523801823430883365), (Int.negOfNat 92378493656596844901199085), (Int.negOfNat 1547132291832758412894649), (Int.ofNat 697307074871086346793607), (Int.ofNat 19703998545300531641546), (Int.negOfNat 3479701971916356504087), (Int.negOfNat 121789442185528206624), (Int.ofNat 12827287236455928408), (Int.ofNat 512071894249067845), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(9281716619900476969791690095674421/11258999068426240000000000000000000), (381660771251821501901304908276047/5629499534213120000000000000000000), (166030576950083354169951424917/112589990684262400000000000000000), (2189263353189016499203280418269/5629499534213120000000000000000000), (-759097820477490466462485018583/11258999068426240000000000000000000), (-138418064242342152654057640747/5629499534213120000000000000000000), (14850476518190886122007571211/11258999068426240000000000000000000), (7111003603450409315260516929/11258999068426240000000000000000000), (-8483700304760364686176673/2251799813685248000000000000000000), (-18475698731319368980239817/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial151.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial151.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial151.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 10890598204591600387970280534687500), (Int.ofNat 841619039133265344820427939054085), (Int.ofNat 10352549800146936772771472626947), (Int.negOfNat 6975278522507205356469139525440), (Int.negOfNat 1055531454578286302930584194746), (Int.ofNat 302365411500169112448022767067), (Int.ofNat 53028402800650484570728475791), (Int.negOfNat 4587152578561506820110560749), (Int.negOfNat 1062451286433214051638515545), (Int.ofNat 21653226354363388940656645), (Int.ofNat 10443026876981666752791611), (Int.ofNat 40927968530965351526593), (Int.negOfNat 63157539333357993946094), (Int.negOfNat 984052461491165241633), (Int.ofNat 263988444608404857976), (Int.ofNat 5983616122140489352), (Int.negOfNat 981590865919019315), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(34849914254693121241504897711/36028797018963968000000000000), (168323807826653068964085587810817/2251799813685248000000000000000000), (10352549800146936772771472626947/11258999068426240000000000000000000), (-21797745382835016738966061017/35184372088832000000000000000000), (-527765727289143151465292097373/5629499534213120000000000000000000), (302365411500169112448022767067/11258999068426240000000000000000000), (53028402800650484570728475791/11258999068426240000000000000000000), (-4587152578561506820110560749/11258999068426240000000000000000000), (-212490257286642810327703109/2251799813685248000000000000000000), (4330645270872677788131329/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial151.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial151.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial151.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 12554787720142725742243678569354388), (Int.ofNat 796878826443404426311380365031633), (Int.negOfNat 24685395194845967777414760143418), (Int.ofNat 958256203436294422277379989448), (Int.ofNat 2896785462037349655991413975678), (Int.ofNat 200037820300221119495920141587), (Int.negOfNat 83681142925540379643681977451), (Int.negOfNat 9814724823612451056053177838), (Int.ofNat 773192509692675363762805603), (Int.ofNat 134661128887039527233082750), (Int.negOfNat 3229094060228740073187280), (Int.negOfNat 1006394926604917436558792), (Int.ofNat 3237823602128265011865), (Int.ofNat 4971449678839748895817), (Int.ofNat 36050467849861888029), (Int.negOfNat 18390590467015447261), (Int.negOfNat 309932805678101191), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(3138696930035681435560919642338597/2814749767106560000000000000000000), (796878826443404426311380365031633/11258999068426240000000000000000000), (-12342697597422983888707380071709/5629499534213120000000000000000000), (119782025429536802784672498681/1407374883553280000000000000000000), (1448392731018674827995706987839/5629499534213120000000000000000000), (200037820300221119495920141587/11258999068426240000000000000000000), (-83681142925540379643681977451/11258999068426240000000000000000000), (-4907362411806225528026588919/5629499534213120000000000000000000), (773192509692675363762805603/11258999068426240000000000000000000), (538644515548158108932331/45035996273704960000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial151.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial151.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial151.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 14103869311650979771247307252424263), (Int.ofNat 798947187561333198980061828618570), (Int.ofNat 41852599959814032910839570327815), (Int.ofNat 15268027055194917954980814900977), (Int.negOfNat 1546592307106253774501289590507), (Int.negOfNat 1064555826505932425457868873005), (Int.negOfNat 68461731080943245828003099627), (Int.ofNat 14147569035377229685939923406), (Int.ofNat 1509723849844318465434659535), (Int.negOfNat 92240264020249517260953628), (Int.negOfNat 14282589083242841667392015), (Int.ofNat 343421117754491951886701), (Int.ofNat 83703603379218633220496), (Int.negOfNat 660309306340017881858), (Int.negOfNat 345609692519707645001), (Int.negOfNat 383447073880564037), (Int.ofNat 1160110919431542934), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(14103869311650979771247307252424263/11258999068426240000000000000000000), (79894718756133319898006182861857/1125899906842624000000000000000000), (8370519991962806582167914065563/2251799813685248000000000000000000), (15268027055194917954980814900977/11258999068426240000000000000000000), (-1546592307106253774501289590507/11258999068426240000000000000000000), (-212911165301186485091573774601/2251799813685248000000000000000000), (-68461731080943245828003099627/11258999068426240000000000000000000), (7073784517688614842969961703/5629499534213120000000000000000000), (301944769968863693086931907/2251799813685248000000000000000000), (-23060066005062379315238407/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial151.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial151.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial151.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 15930262049827718668874207580608646), (Int.ofNat 1009378110588949427911954132419416), (Int.ofNat 6385373727845591121516000197453), (Int.negOfNat 40704533809784445577323458862154), (Int.negOfNat 11186990591179487127928058249547), (Int.negOfNat 304398649661365459624921563869), (Int.ofNat 198342963736121853852645051307), (Int.ofNat 15025519990950488599396757952), (Int.negOfNat 1695487523151348734334704934), (Int.negOfNat 183229571999154698397946078), (Int.ofNat 8842471505782394780949111), (Int.ofNat 1279878041106679840538405), (Int.negOfNat 30631657691011900732331), (Int.negOfNat 6094268881047937321595), (Int.ofNat 71526856669945972904), (Int.ofNat 21774752663503007411), (Int.negOfNat 51363709098629009), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(7965131024913859334437103790304323/5629499534213120000000000000000000), (126172263823618678488994266552427/1407374883553280000000000000000000), (6385373727845591121516000197453/11258999068426240000000000000000000), (-20352266904892222788661729431077/5629499534213120000000000000000000), (-11186990591179487127928058249547/11258999068426240000000000000000000), (-304398649661365459624921563869/11258999068426240000000000000000000), (198342963736121853852645051307/11258999068426240000000000000000000), (234773749858601384365574343/175921860444160000000000000000000), (-847743761575674367167352467/5629499534213120000000000000000000), (-91614785999577349198973039/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial151.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial151.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial151.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 17474291749443629423403426053710485), (Int.ofNat 206843176843721037625543662247403), (Int.negOfNat 476729762319783322222688499551637), (Int.negOfNat 106065855167736229413470703591150), (Int.negOfNat 594057310252933270523752262797), (Int.ofNat 2313064520068417475588858072500), (Int.ofNat 141265631983343135754751242630), (Int.negOfNat 24621318113176384544569186338), (Int.negOfNat 2175721338800437607966108308), (Int.ofNat 162522841239899438937506644), (Int.ofNat 17985570516364407051560219), (Int.negOfNat 738002603347642028706443), (Int.negOfNat 98725424714905919059712), (Int.ofNat 2447781215104670490266), (Int.ofNat 393346399598055555472), (Int.negOfNat 5717019292802117638), (Int.negOfNat 1218198801351823153), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(3494858349888725884680685210742097/2251799813685248000000000000000000), (206843176843721037625543662247403/11258999068426240000000000000000000), (-476729762319783322222688499551637/11258999068426240000000000000000000), (-2121317103354724588269414071823/225179981368524800000000000000000), (-594057310252933270523752262797/11258999068426240000000000000000000), (925225808027366990235543229/4503599627370496000000000000000), (14126563198334313575475124263/1125899906842624000000000000000000), (-12310659056588192272284593169/5629499534213120000000000000000000), (-543930334700109401991527077/2814749767106560000000000000000000), (40630710309974859734376661/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial151.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial151.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial151.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 15202477586581932142473843745912149), (Int.negOfNat 2792510121663506964788275682167270), (Int.negOfNat 927948599251806177425941029249324), (Int.negOfNat 12271381727787003711332609685966), (Int.ofNat 22536356738553312108507923190281), (Int.ofNat 1407370736154522901848971035102), (Int.negOfNat 293400665677504105726588747424), (Int.negOfNat 24737297914673125364812787637), (Int.ofNat 2398686635263880967382747348), (Int.ofNat 235736720034393605840161683), (Int.negOfNat 13558388827979003655573122), (Int.negOfNat 1479611524261946935496993), (Int.ofNat 56331856846038123500160), (Int.ofNat 6672493035557994259920), (Int.negOfNat 179151923997453581995), (Int.negOfNat 22788996682759219707), (Int.ofNat 412660223875359209), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(15202477586581932142473843745912149/11258999068426240000000000000000000), (-279251012166350696478827568216727/1125899906842624000000000000000000), (-231987149812951544356485257312331/2814749767106560000000000000000000), (-6135690863893501855666304842983/5629499534213120000000000000000000), (22536356738553312108507923190281/11258999068426240000000000000000000), (703685368077261450924485517551/5629499534213120000000000000000000), (-9168770802422003303955898357/351843720888320000000000000000000), (-24737297914673125364812787637/11258999068426240000000000000000000), (599671658815970241845686837/2814749767106560000000000000000000), (235736720034393605840161683/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial151.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial151.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial151.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 6191883575756614448500407914440852), (Int.negOfNat 5882308241085968032078299461692392), (Int.negOfNat 429962642476196763029686181853263), (Int.ofNat 168820445609874644727004145948982), (Int.ofNat 15481214674336101078499098107844), (Int.negOfNat 2786936783783855634393800571087), (Int.negOfNat 275479937473328284051851130673), (Int.ofNat 28807268585684342641279963151), (Int.ofNat 2918232083386585722388610131), (Int.negOfNat 203256166194000856015123861), (Int.negOfNat 20667883441335245800590832), (Int.ofNat 1039395500969595563910105), (Int.ofNat 104950715221079283590635), (Int.negOfNat 4024247262693894377847), (Int.negOfNat 401269387132615843788), (Int.ofNat 11963873862435513973), (Int.ofNat 1276286683272103372), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(1547970893939153612125101978610213/2814749767106560000000000000000000), (-735288530135746004009787432711549/1407374883553280000000000000000000), (-429962642476196763029686181853263/11258999068426240000000000000000000), (84410222804937322363502072974491/5629499534213120000000000000000000), (3870303668584025269624774526961/2814749767106560000000000000000000), (-2786936783783855634393800571087/11258999068426240000000000000000000), (-275479937473328284051851130673/11258999068426240000000000000000000), (28807268585684342641279963151/11258999068426240000000000000000000), (2918232083386585722388610131/11258999068426240000000000000000000), (-203256166194000856015123861/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial151.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial151.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial151.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 5796821483502434527514269765845372), (Int.negOfNat 5341427850197189674664464397669059), (Int.ofNat 688887896499509097318045871473439), (Int.ofNat 157121556406340533893027982101483), (Int.negOfNat 18624437697684565939342999705636), (Int.negOfNat 2902264782436179689831160658094), (Int.ofNat 269052477481752300276148200544), (Int.ofNat 33945124082189494770353337197), (Int.negOfNat 2486648937441150661930064252), (Int.negOfNat 269539196847434173874010816), (Int.ofNat 15961190623182790246215517), (Int.ofNat 1535186598297279028104662), (Int.negOfNat 75154873004274873281451), (Int.negOfNat 6540419907503741858351), (Int.ofNat 269992455852836733575), (Int.ofNat 21213228086749828805), (Int.negOfNat 793319365958849482), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-1449205370875608631878567441461343/2814749767106560000000000000000000), (-5341427850197189674664464397669059/11258999068426240000000000000000000), (688887896499509097318045871473439/11258999068426240000000000000000000), (157121556406340533893027982101483/11258999068426240000000000000000000), (-4656109424421141484835749926409/2814749767106560000000000000000000), (-1451132391218089844915580329047/5629499534213120000000000000000000), (8407889921304759383629631267/351843720888320000000000000000000), (33945124082189494770353337197/11258999068426240000000000000000000), (-621662234360287665482516063/2814749767106560000000000000000000), (-4211549950741158966781419/175921860444160000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial151.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial151.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial151.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial151.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial151.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial151.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial151.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial151.reflect := by
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

end Bin151
end
end ErdosOverlap.OuterNumerics
