/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.IntegerOuterBindings
public import ErdosOverlap.Numerics.OuterTruncation
public import ErdosOverlap.Certificate.OuterData14
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

/-! # Exact integer weighted outer models for source bin 173

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin173

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 435872886230395700)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 1704262359685536000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 1160060365180978100)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 478302912229174660)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 846338827069995400)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 697902960216375400)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 499391460646128530)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 348106856080174500)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 187738482924256070)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 106013136214423470)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial173.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial173.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 8771334032222847000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 3393181717956676000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1125677792386475700)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 898627044122145100)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 450425154243825300)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 168902463747119740)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 3309180469017277)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 41135196604378844)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 43564858123936060)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial173.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial173.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 8771334032222847000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 3393181717956676000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1125677792386475700)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 898627044122145100)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 450425154243825300)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 168902463747119740)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 3309180469017277)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 41135196604378844)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 43564858123936060)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial173.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial173.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial173.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 3979918720912151304296533412500501), (Int.ofNat 3766557689633482909627912353236960), (Int.ofNat 393752076659670831926705317739668), (Int.negOfNat 88543713136713933179677473779508), (Int.negOfNat 12360183745261985143204305724365), (Int.ofNat 1491872471639813806704276479775), (Int.ofNat 212278431379790464170477553365), (Int.negOfNat 16750047395412037705827624242), (Int.negOfNat 2253960242105991545644286359), (Int.ofNat 130707397997402160305450644), (Int.ofNat 16159218658022965041276759), (Int.negOfNat 741324252289757333557826), (Int.negOfNat 83262858982984263870388), (Int.ofNat 3167481225300140286390), (Int.ofNat 323111721087196766861), (Int.negOfNat 10357601158105825842), (Int.negOfNat 1020328509344368624), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-3979918720912151304296533412500501/11258999068426240000000000000000000), (23540985560209268185174452207731/70368744177664000000000000000000), (98438019164917707981676329434917/2814749767106560000000000000000000), (-22135928284178483294919368444877/2814749767106560000000000000000000), (-2472036749052397028640861144873/2251799813685248000000000000000000), (59674898865592552268171059191/450359962737049600000000000000000), (42455686275958092834095510673/2251799813685248000000000000000000), (-8375023697706018852913812121/5629499534213120000000000000000000), (-2253960242105991545644286359/11258999068426240000000000000000000), (32676849499350540076362661/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial173.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial173.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial173.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial173 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 4280778679567657336154155898727132), (Int.ofNat 4034184429926002859687423675910527), (Int.negOfNat 278390552973431394163626118461293), (Int.negOfNat 106293517674894671780334468363536), (Int.ofNat 8784579995610993358795837213124), (Int.ofNat 1987223425686372384163767545252), (Int.negOfNat 147509223722984920041821585634), (Int.negOfNat 24035794484784402282838437495), (Int.ofNat 1550488390397859768669637576), (Int.ofNat 196599120235748607569715742), (Int.negOfNat 11132974654154181786804307), (Int.negOfNat 1147256164290997266594116), (Int.ofNat 57726349461869277299320), (Int.ofNat 4987390920656515712948), (Int.negOfNat 225716970969378772270), (Int.negOfNat 16572654319424769151), (Int.ofNat 714435807325097276), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(1070194669891914334038538974681783/2814749767106560000000000000000000), (4034184429926002859687423675910527/11258999068426240000000000000000000), (-278390552973431394163626118461293/11258999068426240000000000000000000), (-6643344854680916986270904272721/703687441776640000000000000000000), (2196144998902748339698959303281/2814749767106560000000000000000000), (496805856421593096040941886313/2814749767106560000000000000000000), (-73754611861492460020910792817/5629499534213120000000000000000000), (-4807158896956880456567687499/2251799813685248000000000000000000), (193811048799732471083704697/1407374883553280000000000000000000), (98299560117874303784857871/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial173.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial173.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial173.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial173 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 10577348550812716534548278470128618), (Int.ofNat 2048067028641434255822401004190249), (Int.negOfNat 594369686033829426745769799147488), (Int.ofNat 10034235561741443334590177934371), (Int.ofNat 15416254926915430014842280975415), (Int.negOfNat 827409592268268743322409553378), (Int.negOfNat 228309060205763147439585513740), (Int.ofNat 14226174629120212834466848868), (Int.ofNat 2179218963486462840844622992), (Int.negOfNat 138356978862914334664170663), (Int.negOfNat 14496801121960838918928264), (Int.ofNat 895703341132486562862207), (Int.ofNat 70796004095498008211913), (Int.negOfNat 4168089411374156956149), (Int.negOfNat 263452830832094830810), (Int.ofNat 14660497000618279575), (Int.ofNat 745853958825034274), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(5288674275406358267274139235064309/5629499534213120000000000000000000), (2048067028641434255822401004190249/11258999068426240000000000000000000), (-18574052688557169585805306223359/351843720888320000000000000000000), (10034235561741443334590177934371/11258999068426240000000000000000000), (3083250985383086002968456195083/2251799813685248000000000000000000), (-413704796134134371661204776689/5629499534213120000000000000000000), (-11415453010288157371979275687/562949953421312000000000000000000), (3556543657280053208616712217/2814749767106560000000000000000000), (136201185217903927552788937/703687441776640000000000000000000), (-138356978862914334664170663/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial173.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial173.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial173.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial173 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 12584144173822747341474453902558334), (Int.ofNat 182514591134797097608192503576787), (Int.negOfNat 272471241249735162268866682655254), (Int.ofNat 74688203695397711953342076148219), (Int.negOfNat 839967605083411558034422415366), (Int.negOfNat 1759591221813406766740717499449), (Int.ofNat 89597785341454125213495635773), (Int.ofNat 21230993782919342262694901127), (Int.negOfNat 1385922694985033465063334795), (Int.negOfNat 165685161915211556469305093), (Int.ofNat 11824734170530740709888924), (Int.ofNat 916731526262904499189640), (Int.negOfNat 67257829262852580798292), (Int.negOfNat 3795090871316758887243), (Int.ofNat 277252217363136399061), (Int.ofNat 11922161200093619274), (Int.negOfNat 845130381696905456), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(6292072086911373670737226951279167/5629499534213120000000000000000000), (182514591134797097608192503576787/11258999068426240000000000000000000), (-136235620624867581134433341327627/5629499534213120000000000000000000), (74688203695397711953342076148219/11258999068426240000000000000000000), (-419983802541705779017211207683/5629499534213120000000000000000000), (-1759591221813406766740717499449/11258999068426240000000000000000000), (89597785341454125213495635773/11258999068426240000000000000000000), (21230993782919342262694901127/11258999068426240000000000000000000), (-277184538997006693012666959/2251799813685248000000000000000000), (-165685161915211556469305093/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial173.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial173.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial173.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial173 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 12395073502633983049436287426216688), (Int.negOfNat 153775806039591612092350596888929), (Int.ofNat 47412102686841727912850082280513), (Int.ofNat 20647407895742484731426182513864), (Int.negOfNat 9147563911737790084232116994244), (Int.ofNat 258776415568791903115720145556), (Int.ofNat 168977851238964581540757481993), (Int.negOfNat 10595325606269705273565518031), (Int.negOfNat 1658490975358479475677013048), (Int.ofNat 130965273683485030772055626), (Int.ofNat 10669586166489509698901792), (Int.negOfNat 944508033214778499373611), (Int.negOfNat 49331579058248017685734), (Int.ofNat 4655149232470198716118), (Int.ofNat 173113559136575442541), (Int.negOfNat 17107828448054897545), (Int.negOfNat 427814550181763864), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(774692093914623940589767964138543/703687441776640000000000000000000), (-153775806039591612092350596888929/11258999068426240000000000000000000), (47412102686841727912850082280513/11258999068426240000000000000000000), (2580925986967810591428272814233/1407374883553280000000000000000000), (-2286890977934447521058029248561/2814749767106560000000000000000000), (64694103892197975778930036389/2814749767106560000000000000000000), (168977851238964581540757481993/11258999068426240000000000000000000), (-10595325606269705273565518031/11258999068426240000000000000000000), (-207311371919809934459626631/1407374883553280000000000000000000), (65482636841742515386027813/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial173.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial173.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial173.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial173 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 12313379078145765710007332065127638), (Int.ofNat 37965098682600445102452325571503), (Int.ofNat 3617002248461576566109841691869), (Int.negOfNat 23227028046460805215996294192976), (Int.negOfNat 618194039948306142227907459484), (Int.ofNat 972292834864744630382533069391), (Int.negOfNat 57020477285725332596563354095), (Int.negOfNat 13708992592149097335352723329), (Int.ofNat 1192065077244092290176355511), (Int.ofNat 108282716654005424624104686), (Int.negOfNat 11454709303118373271395719), (Int.negOfNat 568357442685469402738462), (Int.ofNat 69172595569098118007971), (Int.ofNat 2162528475357063567248), (Int.negOfNat 295134661714082428025), (Int.negOfNat 6188344645854901257), (Int.ofNat 975824956068713636), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(6156689539072882855003666032563819/5629499534213120000000000000000000), (37965098682600445102452325571503/11258999068426240000000000000000000), (3617002248461576566109841691869/11258999068426240000000000000000000), (-1451689252903800325999768387061/703687441776640000000000000000000), (-154548509987076535556976864871/2814749767106560000000000000000000), (972292834864744630382533069391/11258999068426240000000000000000000), (-11404095457145066519312670819/2251799813685248000000000000000000), (-13708992592149097335352723329/11258999068426240000000000000000000), (1192065077244092290176355511/11258999068426240000000000000000000), (54141358327002712312052343/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial173.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial173.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial173.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial173 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 12234127276478220970276069551645311), (Int.negOfNat 183972683476052235524828687931491), (Int.negOfNat 93203662587488205454719330097429), (Int.negOfNat 3554624612649542322266056044089), (Int.ofNat 3447982410827070324513704230734), (Int.negOfNat 212929149067975955857607732968), (Int.negOfNat 85228820267153045606499712207), (Int.ofNat 8815679948128705281366632746), (Int.ofNat 907312596262132919433464695), (Int.negOfNat 118859439252924500695272817), (Int.negOfNat 5582984730810867246585220), (Int.ofNat 904224791074760538793529), (Int.ofNat 22718142953231147740411), (Int.negOfNat 4600288985018679767330), (Int.negOfNat 65011816908910700996), (Int.ofNat 17347767454955173995), (Int.ofNat 109775141538493454), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(12234127276478220970276069551645311/11258999068426240000000000000000000), (-183972683476052235524828687931491/11258999068426240000000000000000000), (-93203662587488205454719330097429/11258999068426240000000000000000000), (-3554624612649542322266056044089/11258999068426240000000000000000000), (1723991205413535162256852115367/5629499534213120000000000000000000), (-26616143633496994482200966621/1407374883553280000000000000000000), (-85228820267153045606499712207/11258999068426240000000000000000000), (4407839974064352640683316373/5629499534213120000000000000000000), (181462519252426583886692939/2251799813685248000000000000000000), (-118859439252924500695272817/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial173.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial173.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial173.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial173 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 11509125616342603684034893904656394), (Int.negOfNat 517919086481211134623973584308993), (Int.negOfNat 62304806481940436069010704992780), (Int.ofNat 7752788823186396662809894489427), (Int.negOfNat 825364298553799221130267050035), (Int.negOfNat 345814608524888240783891494278), (Int.ofNat 54871798591927322588864489485), (Int.ofNat 5701339440948052927953923122), (Int.negOfNat 1051713289808205694076829452), (Int.negOfNat 43057647155580754428589999), (Int.ofNat 10324829128450961918292620), (Int.ofNat 177888773370777342830066), (Int.negOfNat 63835276618361411918830), (Int.negOfNat 379521120867418994053), (Int.ofNat 275879671311487173616), (Int.negOfNat 128797109656171640), (Int.negOfNat 1000506394226098346), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(5754562808171301842017446952328197/5629499534213120000000000000000000), (-517919086481211134623973584308993/11258999068426240000000000000000000), (-3115240324097021803450535249639/562949953421312000000000000000000), (7752788823186396662809894489427/11258999068426240000000000000000000), (-165072859710759844226053410007/2251799813685248000000000000000000), (-172907304262444120391945747139/5629499534213120000000000000000000), (10974359718385464517772897897/2251799813685248000000000000000000), (2850669720474026463976961561/5629499534213120000000000000000000), (-262928322452051423519207363/2814749767106560000000000000000000), (-43057647155580754428589999/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial173.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial173.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial173.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial173 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 10265779591065523773957814924910820), (Int.negOfNat 716214937498555998021155172081169), (Int.negOfNat 48224855611984388987644095756560), (Int.negOfNat 2667616185749858545799422082226), (Int.negOfNat 608026205255588419765049463070), (Int.ofNat 315786219189393319238258314156), (Int.ofNat 21632412900333748243946656889), (Int.negOfNat 8018381952152722744962393358), (Int.negOfNat 204350418876142133900038956), (Int.ofNat 102355655495376484815597747), (Int.ofNat 517608479417533313579968), (Int.negOfNat 781810312260784899641526), (Int.ofNat 3892888813820860401638), (Int.ofNat 4017978941031518595017), (Int.negOfNat 41554468297840827284), (Int.negOfNat 15184682331134997252), (Int.ofNat 189380847138225606), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(513288979553276188697890746245541/562949953421312000000000000000000), (-716214937498555998021155172081169/11258999068426240000000000000000000), (-602810695149804862345551196957/140737488355328000000000000000000), (-1333808092874929272899711041113/5629499534213120000000000000000000), (-60802620525558841976504946307/1125899906842624000000000000000000), (78946554797348329809564578539/2814749767106560000000000000000000), (21632412900333748243946656889/11258999068426240000000000000000000), (-4009190976076361372481196679/5629499534213120000000000000000000), (-51087604719035533475009739/2814749767106560000000000000000000), (102355655495376484815597747/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial173.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial173.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial173.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial173 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 8619843294388417035199502362087753), (Int.negOfNat 934737789215713945355288620863175), (Int.negOfNat 53666574374292710185507573627298), (Int.ofNat 4231068022030232038730003793588), (Int.ofNat 1762274838692206979047469811997), (Int.negOfNat 678403123933127659739791850), (Int.negOfNat 53502904798003020647823768243), (Int.ofNat 319305171277816978513471390), (Int.ofNat 876431372827739693110167551), (Int.negOfNat 13379044256444360919852011), (Int.negOfNat 8364679906907847289603972), (Int.ofNat 175087025406735258595931), (Int.ofNat 51694373608922587675719), (Int.negOfNat 1240949814368233962714), (Int.negOfNat 224568807918493020116), (Int.ofNat 5870818960577139857), (Int.ofNat 875609838045123526), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(8619843294388417035199502362087753/11258999068426240000000000000000000), (-37389511568628557814211544834527/450359962737049600000000000000000), (-26833287187146355092753786813649/5629499534213120000000000000000000), (1057767005507558009682500948397/2814749767106560000000000000000000), (1762274838692206979047469811997/11258999068426240000000000000000000), (-13568062478662553194795837/225179981368524800000000000000000), (-53502904798003020647823768243/11258999068426240000000000000000000), (31930517127781697851347139/1125899906842624000000000000000000), (876431372827739693110167551/11258999068426240000000000000000000), (-13379044256444360919852011/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial173.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial173.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial173.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial173 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 6594550843942810923014465378151445), (Int.negOfNat 1051595291078070475455595983602864), (Int.ofNat 2754735266380013126400589491983), (Int.ofNat 11303335872023448477596311131746), (Int.negOfNat 536757767006287340051484649827), (Int.negOfNat 307873459276800866074363277078), (Int.ofNat 17251809394721634016479161541), (Int.ofNat 6398327273188711003654401525), (Int.negOfNat 316995679483080591490611265), (Int.negOfNat 77023274913896191167073234), (Int.ofNat 3554674408058557467338833), (Int.ofNat 579823620798838174228102), (Int.negOfNat 25815609005426762656117), (Int.negOfNat 2972043614451282751272), (Int.ofNat 129390257260014751555), (Int.ofNat 11052401842758761909), (Int.negOfNat 426088557724457256), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(1318910168788562184602893075630289/2251799813685248000000000000000000), (-65724705692379404715974748975179/703687441776640000000000000000000), (2754735266380013126400589491983/11258999068426240000000000000000000), (5651667936011724238798155565873/5629499534213120000000000000000000), (-536757767006287340051484649827/11258999068426240000000000000000000), (-153936729638400433037181638539/5629499534213120000000000000000000), (17251809394721634016479161541/11258999068426240000000000000000000), (255933090927548440146176061/450359962737049600000000000000000), (-63399135896616118298122253/2251799813685248000000000000000000), (-38511637456948095583536617/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial173.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial173.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial173.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial173 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 4576173029560439394490259928342201), (Int.negOfNat 941041756411092415276155784520559), (Int.ofNat 40634932762964956740168252971021), (Int.ofNat 130982337809294856694995085580), (Int.negOfNat 1386378854167406625354003828183), (Int.ofNat 181688928137534582923230091412), (Int.ofNat 38024600495770098769098059919), (Int.negOfNat 4200051462587915340598961865), (Int.negOfNat 593025482379655731374905224), (Int.ofNat 53162388555247169928614702), (Int.ofNat 5524532788289088742464764), (Int.negOfNat 433518254639539279458349), (Int.negOfNat 33801963079046346483702), (Int.ofNat 2437531808847244397626), (Int.ofNat 146092669058719214461), (Int.negOfNat 9987365766070469407), (Int.negOfNat 557570429401853116), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(4576173029560439394490259928342201/11258999068426240000000000000000000), (-941041756411092415276155784520559/11258999068426240000000000000000000), (40634932762964956740168252971021/11258999068426240000000000000000000), (6549116890464742834749754279/562949953421312000000000000000000), (-1386378854167406625354003828183/11258999068426240000000000000000000), (45422232034383645730807522853/2814749767106560000000000000000000), (38024600495770098769098059919/11258999068426240000000000000000000), (-840010292517583068119792373/2251799813685248000000000000000000), (-74128185297456966421863153/1407374883553280000000000000000000), (26581194277623584964307351/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial173.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial173.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial173.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial173 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 2843085115834567660546094442394985), (Int.negOfNat 801802202396062424341573107726953), (Int.ofNat 28218173655335220182823918940002), (Int.negOfNat 673944456965654089874419586642), (Int.ofNat 1138800561246315444864367826228), (Int.ofNat 155903835581374417934011398303), (Int.negOfNat 40696053304860716701937089003), (Int.negOfNat 3561673438544830331587727283), (Int.ofNat 637537410603153990375002361), (Int.ofNat 42379350993304814732905581), (Int.negOfNat 6129079802015132059846628), (Int.negOfNat 314082847662369375181940), (Int.ofNat 39801328400603582706576), (Int.ofNat 1589562516019335416287), (Int.negOfNat 184809976257638333899), (Int.negOfNat 5760852230697439046), (Int.ofNat 556783132096265436), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(568617023166913532109218888478997/2251799813685248000000000000000000), (-801802202396062424341573107726953/11258999068426240000000000000000000), (14109086827667610091411959470001/5629499534213120000000000000000000), (-336972228482827044937209793321/5629499534213120000000000000000000), (284700140311578861216091956557/2814749767106560000000000000000000), (155903835581374417934011398303/11258999068426240000000000000000000), (-40696053304860716701937089003/11258999068426240000000000000000000), (-3561673438544830331587727283/11258999068426240000000000000000000), (637537410603153990375002361/11258999068426240000000000000000000), (42379350993304814732905581/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial173.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial173.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial173.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial173 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 1367289301356857308263096410979322), (Int.negOfNat 656795586349113406072085112133795), (Int.ofNat 53078700398979673122192563240674), (Int.ofNat 7434399416198553387242177999725), (Int.ofNat 53505141782234572021323376260), (Int.negOfNat 314930765981205551634413478320), (Int.negOfNat 13362451527909919553150480736), (Int.ofNat 6295581322188780971870605228), (Int.ofNat 225082488773489516164664768), (Int.negOfNat 73796239747788457890188465), (Int.negOfNat 2069866669155546326369636), (Int.ofNat 566078956623229223842773), (Int.ofNat 12311413776704927225561), (Int.negOfNat 3040480283790434421555), (Int.negOfNat 51446089171643262350), (Int.ofNat 12070779563523201677), (Int.ofNat 239531020758582706), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(683644650678428654131548205489661/5629499534213120000000000000000000), (-131359117269822681214417022426759/2251799813685248000000000000000000), (26539350199489836561096281620337/5629499534213120000000000000000000), (297375976647942135489687119989/450359962737049600000000000000000), (2675257089111728601066168813/562949953421312000000000000000000), (-3936634574765069395430168479/140737488355328000000000000000000), (-417576610247184986035952523/351843720888320000000000000000000), (1573895330547195242967651307/2814749767106560000000000000000000), (3516913887085773690072887/175921860444160000000000000000000), (-14759247949557691578037693/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial173.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial173.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial173.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial173 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 316235963153316006278388580259099), (Int.negOfNat 378439084493257114453043561558868), (Int.ofNat 74854129587130885850538127136427), (Int.negOfNat 3348038922976533480503036702880), (Int.negOfNat 2183720405933855290075006699728), (Int.ofNat 5889808632518532701769412331), (Int.ofNat 51859831986111680439756018702), (Int.ofNat 247568244796787241318896211), (Int.negOfNat 756232893557100193543942640), (Int.negOfNat 3210658373400502632906070), (Int.ofNat 6999760259956923055681365), (Int.ofNat 19272410086587734583796), (Int.negOfNat 44163524660841457943868), (Int.negOfNat 58847536996850482672), (Int.ofNat 200569371744260318510), (Int.negOfNat 189968271413758077), (Int.negOfNat 687477706468073616), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(316235963153316006278388580259099/11258999068426240000000000000000000), (-94609771123314278613260890389717/2814749767106560000000000000000000), (74854129587130885850538127136427/11258999068426240000000000000000000), (-20925243268603334253143979393/70368744177664000000000000000000), (-136482525370865955629687918733/703687441776640000000000000000000), (5889808632518532701769412331/11258999068426240000000000000000000), (25929915993055840219878009351/5629499534213120000000000000000000), (247568244796787241318896211/11258999068426240000000000000000000), (-9452911169463752419299283/140737488355328000000000000000000), (-321065837340050263290607/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial173.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial173.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial173.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial173 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 199598543884698597537061908576834), (Int.negOfNat 179285692983216018590045531144825), (Int.ofNat 14148811879446161570788101230612), (Int.negOfNat 13414942991528644500341621859062), (Int.ofNat 285634451033796316129349666757), (Int.ofNat 356457985269026523022281371310), (Int.negOfNat 10201234987611566903717267139), (Int.negOfNat 6534276440618209270605958514), (Int.ofNat 155640764761356824410936125), (Int.ofNat 74546988995070932006326304), (Int.negOfNat 1480403463099702884622609), (Int.negOfNat 561873307245837719246374), (Int.ofNat 9668171646033395105124), (Int.ofNat 2980376026205620263934), (Int.negOfNat 45653842527282426419), (Int.negOfNat 11769232307474830910), (Int.ofNat 122073246008623764), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-99799271942349298768530954288417/5629499534213120000000000000000000), (-7171427719328640743601821245793/450359962737049600000000000000000), (3537202969861540392697025307653/2814749767106560000000000000000000), (-6707471495764322250170810929531/5629499534213120000000000000000000), (285634451033796316129349666757/11258999068426240000000000000000000), (35645798526902652302228137131/1125899906842624000000000000000000), (-10201234987611566903717267139/11258999068426240000000000000000000), (-3267138220309104635302979257/5629499534213120000000000000000000), (1245126118090854595287489/90071992547409920000000000000000), (2329593406095966625197697/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial173.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial173.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial173.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial173 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 594331277606608477708425608921490), (Int.negOfNat 250581200999914269561710500502170), (Int.negOfNat 37217663635567473642709918949170), (Int.negOfNat 1527833106999710956362910538061), (Int.ofNat 1842042074886314068661735939105), (Int.negOfNat 121492331044449125098843643431), (Int.negOfNat 46271323894757007778803466781), (Int.ofNat 2837429248117195644947085786), (Int.ofNat 671169180375565835615846655), (Int.negOfNat 33798676519935252256013296), (Int.negOfNat 6163311118236948094747311), (Int.ofNat 259046410974445910121766), (Int.ofNat 38685168080584764031856), (Int.negOfNat 1388430806714064771146), (Int.negOfNat 175569779040374278681), (Int.ofNat 5666295995869754610), (Int.ofNat 562581150287098796), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-59433127760660847770842560892149/1125899906842624000000000000000000), (-25058120099991426956171050050217/1125899906842624000000000000000000), (-3721766363556747364270991894917/1125899906842624000000000000000000), (-1527833106999710956362910538061/11258999068426240000000000000000000), (368408414977262813732347187821/2251799813685248000000000000000000), (-121492331044449125098843643431/11258999068426240000000000000000000), (-46271323894757007778803466781/11258999068426240000000000000000000), (1418714624058597822473542893/5629499534213120000000000000000000), (134233836075113167123169331/2251799813685248000000000000000000), (-2112417282495953266000831/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial173.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial173.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial173.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial173 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 1233451376081754539054543807803418), (Int.negOfNat 375591193667314155929225663974567), (Int.negOfNat 20107786909833596710651208866123), (Int.ofNat 3475498692017754576135118059842), (Int.negOfNat 806906673715052546700735842226), (Int.negOfNat 244593873055311396676486872310), (Int.ofNat 30898174574099894636350511218), (Int.ofNat 4923096401257215373838161651), (Int.negOfNat 482959557839084485903862200), (Int.negOfNat 56617220195499709099193530), (Int.ofNat 4539220418974127632653075), (Int.ofNat 428328945978645259698216), (Int.negOfNat 28689359047630265054152), (Int.negOfNat 2283822338412160870012), (Int.ofNat 130122928188516462190), (Int.ofNat 9248696574508451903), (Int.negOfNat 421229234685342824), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-616725688040877269527271903901709/5629499534213120000000000000000000), (-375591193667314155929225663974567/11258999068426240000000000000000000), (-20107786909833596710651208866123/11258999068426240000000000000000000), (1737749346008877288067559029921/5629499534213120000000000000000000), (-403453336857526273350367921113/5629499534213120000000000000000000), (-24459387305531139667648687231/1125899906842624000000000000000000), (15449087287049947318175255609/5629499534213120000000000000000000), (4923096401257215373838161651/11258999068426240000000000000000000), (-2414797789195422429519311/56294995342131200000000000000000), (-5661722019549970909919353/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial173.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial173.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial173.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial173 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 2055538026826820202167958579806144), (Int.negOfNat 452164624614871879392937044585093), (Int.negOfNat 28528432599444486192651709255915), (Int.negOfNat 6148679131087894659796724523853), (Int.negOfNat 714900147886936187973787076859), (Int.ofNat 254983007278026712225848645788), (Int.ofNat 27188234912151611756891852636), (Int.negOfNat 5246848675168117378219718852), (Int.negOfNat 410194407498086141671368988), (Int.ofNat 62217816520368201090124635), (Int.ofNat 3833315968852749566067156), (Int.negOfNat 474959062109711459540547), (Int.negOfNat 24522044776015247639141), (Int.ofNat 2522239017547744987285), (Int.ofNat 112885276299014648690), (Int.negOfNat 9969191838382208343), (Int.negOfNat 288106599767764446), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-32117781669169065658874352809471/175921860444160000000000000000000), (-452164624614871879392937044585093/11258999068426240000000000000000000), (-5705686519888897238530341851183/2251799813685248000000000000000000), (-6148679131087894659796724523853/11258999068426240000000000000000000), (-714900147886936187973787076859/11258999068426240000000000000000000), (63745751819506678056462161447/2814749767106560000000000000000000), (6797058728037902939222963159/2814749767106560000000000000000000), (-1311712168792029344554929713/2814749767106560000000000000000000), (-102548601874521535417842247/2814749767106560000000000000000000), (12443563304073640218024927/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial173.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial173.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial173.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial173 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 3125451215145600394334873772761935), (Int.negOfNat 639933986356376001320721203326128), (Int.negOfNat 59598981216137586357618059187133), (Int.negOfNat 620404353168620270030488972637), (Int.ofNat 1817910737826901005140565328815), (Int.ofNat 97467182049771886849776006634), (Int.negOfNat 45377472960875738620711755907), (Int.negOfNat 1990934989388736693290997083), (Int.ofNat 695232284206422232082249159), (Int.ofNat 23826358973786912964440601), (Int.negOfNat 6568906141674696710860352), (Int.negOfNat 190289939351286715329980), (Int.ofNat 41605291016637298344424), (Int.ofNat 1071429966591491397807), (Int.negOfNat 187988677037521870821), (Int.negOfNat 4598203455177302026), (Int.ofNat 551923809057151004), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-625090243029120078866974754552387/2251799813685248000000000000000000), (-39995874147273500082545075207883/703687441776640000000000000000000), (-59598981216137586357618059187133/11258999068426240000000000000000000), (-620404353168620270030488972637/11258999068426240000000000000000000), (363582147565380201028113065763/2251799813685248000000000000000000), (48733591024885943424888003317/5629499534213120000000000000000000), (-45377472960875738620711755907/11258999068426240000000000000000000), (-1990934989388736693290997083/11258999068426240000000000000000000), (695232284206422232082249159/11258999068426240000000000000000000), (23826358973786912964440601/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial173.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial173.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial173.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial173 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 4619448585571400969132469377789376), (Int.negOfNat 828676564188633352665735383819515), (Int.negOfNat 22845150801488952609587301247490), (Int.ofNat 10716114721737246558554652740155), (Int.ofNat 296340499257149305639658314542), (Int.negOfNat 309031085016285137852157779746), (Int.negOfNat 1712963276457616522838476789), (Int.ofNat 6338880753465201452428967175), (Int.ofNat 26510233351352346220221744), (Int.negOfNat 76441991265900289294075778), (Int.negOfNat 420770939591685002343264), (Int.ofNat 590260099600528847334831), (Int.ofNat 4017441591131386699522), (Int.negOfNat 3154945171983714555714), (Int.negOfNat 24852111651193091261), (Int.ofNat 12416523285818826313), (Int.negOfNat 29932808875505964), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-72178884149553140142694834027959/175921860444160000000000000000000), (-165735312837726670533147076763903/2251799813685248000000000000000000), (-2284515080148895260958730124749/1125899906842624000000000000000000), (2143222944347449311710930548031/2251799813685248000000000000000000), (148170249628574652819829157271/5629499534213120000000000000000000), (-154515542508142568926078889873/5629499534213120000000000000000000), (-1712963276457616522838476789/11258999068426240000000000000000000), (253555230138608058097158687/450359962737049600000000000000000), (1656889584459521638763859/703687441776640000000000000000000), (-38220995632950144647037889/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial173.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial173.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial173.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial173 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 6286930782106212416239120493857618), (Int.negOfNat 804337002477528444099338545795357), (Int.ofNat 27396644530363676121893160662020), (Int.ofNat 3655851490852731614720967272650), (Int.negOfNat 1381743224772091083708409524135), (Int.ofNat 74089178003722921944090749064), (Int.ofNat 45501382815674571173500278879), (Int.negOfNat 1767215675768808431174962235), (Int.negOfNat 738822894457742246219078855), (Int.ofNat 18282890585678542777060906), (Int.ofNat 7162298809791925611196867), (Int.negOfNat 113811426755191324087238), (Int.negOfNat 46105096938984404459623), (Int.ofNat 465473919264085969968), (Int.ofNat 211555277711108125425), (Int.negOfNat 1135613099061415991), (Int.negOfNat 682618383428959184), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-3143465391053106208119560246928809/5629499534213120000000000000000000), (-804337002477528444099338545795357/11258999068426240000000000000000000), (1369832226518183806094658033101/562949953421312000000000000000000), (73117029817054632294419345453/225179981368524800000000000000000), (-276348644954418216741681904827/2251799813685248000000000000000000), (9261147250465365243011343633/1407374883553280000000000000000000), (45501382815674571173500278879/11258999068426240000000000000000000), (-353443135153761686234992447/2251799813685248000000000000000000), (-147764578891548449243815771/2251799813685248000000000000000000), (9141445292839271388530453/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial173.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial173.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial173.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial173 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 7773995408398599858748975787310463), (Int.negOfNat 681904429194880929536657134360762), (Int.ofNat 30666429472555883789048418942668), (Int.ofNat 730671671803971106803855029810), (Int.ofNat 926635385688364764902921393464), (Int.ofNat 227602348914912810354892849518), (Int.negOfNat 29790016893330262538318303757), (Int.negOfNat 5711630338917300558104963210), (Int.ofNat 420490531717426583490971909), (Int.ofNat 72777085543833204250894429), (Int.negOfNat 3536760560040266783041988), (Int.negOfNat 580531447120304575910249), (Int.ofNat 19682566617355462265221), (Int.ofNat 3170517016586401554266), (Int.negOfNat 77594737976212347404), (Int.negOfNat 12656462292719102763), (Int.ofNat 347972217518776374), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-7773995408398599858748975787310463/11258999068426240000000000000000000), (-340952214597440464768328567180381/5629499534213120000000000000000000), (7666607368138970947262104735667/2814749767106560000000000000000000), (73067167180397110680385502981/1125899906842624000000000000000000), (115829423211045595612865174183/1407374883553280000000000000000000), (113801174457456405177446424759/5629499534213120000000000000000000), (-29790016893330262538318303757/11258999068426240000000000000000000), (-571163033891730055810496321/1125899906842624000000000000000000), (420490531717426583490971909/11258999068426240000000000000000000), (72777085543833204250894429/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial173.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial173.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial173.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial173 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 8989681182143096114893287784081709), (Int.negOfNat 510314370481502347844006662486622), (Int.ofNat 65543659296425224837824770831197), (Int.ofNat 10351921278003526516175789012444), (Int.ofNat 511874985028794403204901825684), (Int.negOfNat 317317211313212172697739608113), (Int.negOfNat 32446466901949733080543428199), (Int.ofNat 5829930701695264439233116642), (Int.ofNat 589948569319246862049122516), (Int.negOfNat 63210297856287659913171933), (Int.negOfNat 6107450302519644600707948), (Int.ofNat 438636735664890305825914), (Int.ofNat 41094161274433204666882), (Int.negOfNat 2100425138217658046463), (Int.negOfNat 193328333952186050836), (Int.ofNat 7452754854572488888), (Int.ofNat 707299821586343894), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-8989681182143096114893287784081709/11258999068426240000000000000000000), (-255157185240751173922003331243311/5629499534213120000000000000000000), (65543659296425224837824770831197/11258999068426240000000000000000000), (2587980319500881629043947253111/2814749767106560000000000000000000), (127968746257198600801225456421/2814749767106560000000000000000000), (-317317211313212172697739608113/11258999068426240000000000000000000), (-32446466901949733080543428199/11258999068426240000000000000000000), (2914965350847632219616558321/5629499534213120000000000000000000), (147487142329811715512280629/2814749767106560000000000000000000), (-63210297856287659913171933/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial173.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial173.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial173.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial173 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 9668500953767967972521149597791097), (Int.negOfNat 136106948568906485452072880246676), (Int.ofNat 111395657153983507139334213040293), (Int.ofNat 473531890338454736348489632549), (Int.negOfNat 2629117057628228439010780762521), (Int.negOfNat 113073029753898033301199292609), (Int.ofNat 60576955393052635252768350275), (Int.ofNat 3361016550978951940470262202), (Int.negOfNat 858451420978707181731390848), (Int.negOfNat 49778646549376502111677699), (Int.ofNat 7472547235396922252548400), (Int.ofNat 439230205883299927958086), (Int.negOfNat 43196597486683326126690), (Int.negOfNat 2549397331754862272933), (Int.ofNat 177815888866525632464), (Int.ofNat 10493377168898926020), (Int.negOfNat 647128206195495434), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-9668500953767967972521149597791097/11258999068426240000000000000000000), (-34026737142226621363018220061669/2814749767106560000000000000000000), (111395657153983507139334213040293/11258999068426240000000000000000000), (473531890338454736348489632549/11258999068426240000000000000000000), (-2629117057628228439010780762521/11258999068426240000000000000000000), (-113073029753898033301199292609/11258999068426240000000000000000000), (2423078215722105410110734011/450359962737049600000000000000000), (1680508275489475970235131101/5629499534213120000000000000000000), (-6706651726396149857276491/87960930222080000000000000000000), (-49778646549376502111677699/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial173.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial173.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial173.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial173 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 9532957935167349597787265467138118), (Int.ofNat 234165273391861905046393308957678), (Int.ofNat 57216744277423828144334378037399), (Int.negOfNat 15185929897396291273149472030408), (Int.negOfNat 233534220584843838633070336293), (Int.ofNat 479471795784572955620980742131), (Int.ofNat 6678877705556822040231765027), (Int.negOfNat 9332551868299733343796350214), (Int.negOfNat 236012748319000586491625855), (Int.ofNat 104912667434739309164978743), (Int.ofNat 3413888420527881285031860), (Int.negOfNat 741300448595505657563731), (Int.negOfNat 26973414315369837582631), (Int.ofNat 3605283368041792478370), (Int.ofNat 138374775662707569956), (Int.negOfNat 13194776705493457105), (Int.negOfNat 582403265405369074), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-4766478967583674798893632733569059/5629499534213120000000000000000000), (117082636695930952523196654478839/5629499534213120000000000000000000), (57216744277423828144334378037399/11258999068426240000000000000000000), (-1898241237174536409143684003801/1407374883553280000000000000000000), (-233534220584843838633070336293/11258999068426240000000000000000000), (479471795784572955620980742131/11258999068426240000000000000000000), (6678877705556822040231765027/11258999068426240000000000000000000), (-4666275934149866671898175107/5629499534213120000000000000000000), (-47202549663800117298325171/2251799813685248000000000000000000), (104912667434739309164978743/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial173.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial173.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial173.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial173 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 8946413224461372909164677681812843), (Int.ofNat 308795813962287161422399925249917), (Int.negOfNat 5736708765546584716998666567006), (Int.negOfNat 1872645456070540731383990454918), (Int.ofNat 2520049763279632961570109315737), (Int.negOfNat 114383313283358105215341790732), (Int.negOfNat 80130987217034931825016768185), (Int.ofNat 1111476487156458356423622671), (Int.ofNat 1237980803857264682984154869), (Int.ofNat 8095334690496664714042966), (Int.negOfNat 10954122261558600600076641), (Int.negOfNat 181882984564955741411762), (Int.ofNat 63512873056201239756129), (Int.ofNat 1377241843899731444808), (Int.negOfNat 262626065342441862795), (Int.negOfNat 6361096680522690677), (Int.ofNat 883835916781727084), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-8946413224461372909164677681812843/11258999068426240000000000000000000), (308795813962287161422399925249917/11258999068426240000000000000000000), (-2868354382773292358499333283503/5629499534213120000000000000000000), (-936322728035270365691995227459/5629499534213120000000000000000000), (2520049763279632961570109315737/11258999068426240000000000000000000), (-28595828320839526303835447683/2814749767106560000000000000000000), (-16026197443406986365003353637/2251799813685248000000000000000000), (1111476487156458356423622671/11258999068426240000000000000000000), (1237980803857264682984154869/11258999068426240000000000000000000), (4047667345248332357021483/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial173.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial173.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial173.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial173 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 8334765433897589970375376665571108), (Int.ofNat 321210765838949330482510142007139), (Int.ofNat 18002285290228024408075249620079), (Int.ofNat 3607286549405745403089178155209), (Int.negOfNat 1847884853173457873159037702880), (Int.negOfNat 498756502661470231785169161050), (Int.ofNat 43875775188197643768130638077), (Int.ofNat 12248572990055647432010400489), (Int.negOfNat 321314431622114763414586812), (Int.negOfNat 141073297373171103027527554), (Int.ofNat 587675581972167668197608), (Int.ofNat 989797171983321011710689), (Int.ofNat 5901477492946658082914), (Int.negOfNat 4781982192908098865582), (Int.negOfNat 53568134347685982461), (Int.ofNat 17311323510986786655), (Int.ofNat 264363856762098664), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-2083691358474397492593844166392777/2814749767106560000000000000000000), (321210765838949330482510142007139/11258999068426240000000000000000000), (18002285290228024408075249620079/11258999068426240000000000000000000), (3607286549405745403089178155209/11258999068426240000000000000000000), (-11549280332334111707243985643/70368744177664000000000000000000), (-9975130053229404635703383221/225179981368524800000000000000000), (43875775188197643768130638077/11258999068426240000000000000000000), (12248572990055647432010400489/11258999068426240000000000000000000), (-80328607905528690853646703/2814749767106560000000000000000000), (-70536648686585551513763777/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial173.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial173.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial173.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial173 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 7632778839888154705627570376541613), (Int.ofNat 350746007303876056277811268774972), (Int.negOfNat 27034113434810086789454239287438), (Int.negOfNat 18530840225483906525967784145269), (Int.negOfNat 1653283890019633639254085933799), (Int.ofNat 661307322471822265116014636824), (Int.ofNat 100477345008292187034450882747), (Int.negOfNat 7787110765820440857174693973), (Int.negOfNat 1594490936690235023299905965), (Int.ofNat 46226835416501097433045967), (Int.ofNat 13770485044771466006462816), (Int.negOfNat 147606852126302300832780), (Int.negOfNat 78258508097104404280748), (Int.ofNat 150676435003935099837), (Int.ofNat 320351891387763275979), (Int.ofNat 1069547068461367814), (Int.negOfNat 1014530491153535264), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-7632778839888154705627570376541613/11258999068426240000000000000000000), (87686501825969014069452817193743/2814749767106560000000000000000000), (-13517056717405043394727119643719/5629499534213120000000000000000000), (-18530840225483906525967784145269/11258999068426240000000000000000000), (-1653283890019633639254085933799/11258999068426240000000000000000000), (82663415308977783139501829603/1407374883553280000000000000000000), (100477345008292187034450882747/11258999068426240000000000000000000), (-7787110765820440857174693973/11258999068426240000000000000000000), (-318898187338047004659981193/2251799813685248000000000000000000), (46226835416501097433045967/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial173.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial173.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial173.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial173 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 7187897945806816368701496834548950), (Int.ofNat 34582708111277330771420805175194), (Int.negOfNat 108606739871916794840277130287118), (Int.ofNat 3998707125157864761157766034256), (Int.ofNat 7377897818071781721035740185936), (Int.ofNat 690898566010801920326986200624), (Int.negOfNat 116328538637097196717414884580), (Int.negOfNat 16032439586314335630367481532), (Int.ofNat 966891426727309711284155948), (Int.ofNat 172525629295202493735283017), (Int.negOfNat 5073617851435046707527656), (Int.negOfNat 1160336427629945039400473), (Int.ofNat 18251804354135503459547), (Int.ofNat 5473609314470638279731), (Int.negOfNat 46762601862030195290), (Int.negOfNat 19394737308439518925), (Int.ofNat 53675551881171746), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-143757958916136327374029936690979/225179981368524800000000000000000), (17291354055638665385710402587597/5629499534213120000000000000000000), (-54303369935958397420138565143559/5629499534213120000000000000000000), (249919195322366547572360377141/703687441776640000000000000000000), (461118613629486357564733761621/703687441776640000000000000000000), (43181160375675120020436637539/703687441776640000000000000000000), (-5816426931854859835870744229/562949953421312000000000000000000), (-4008109896578583907591870383/2814749767106560000000000000000000), (241722856681827427821038987/2814749767106560000000000000000000), (172525629295202493735283017/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial173.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial173.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial173.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial173 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 7390183487827859170579948374016777), (Int.negOfNat 88663483876471800827511311520815), (Int.ofNat 111472905666654784600892203170409), (Int.ofNat 65603912648765707741327989467780), (Int.ofNat 4483643951761494863070320027558), (Int.negOfNat 1342463982242318412480207775571), (Int.negOfNat 148557310877752511238806397386), (Int.ofNat 14297107020925209511999703165), (Int.ofNat 1973454209630591345680337444), (Int.negOfNat 98219506292736024892272738), (Int.negOfNat 15693740500513978625598173), (Int.ofNat 479125190771808412940224), (Int.ofNat 85444308458877028389420), (Int.negOfNat 1758803369565394542792), (Int.negOfNat 341766179474644563470), (Int.ofNat 4881273433649829309), (Int.ofNat 1145225065525343444), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-7390183487827859170579948374016777/11258999068426240000000000000000000), (-17732696775294360165502262304163/2251799813685248000000000000000000), (111472905666654784600892203170409/11258999068426240000000000000000000), (3280195632438285387066399473389/562949953421312000000000000000000), (2241821975880747431535160013779/5629499534213120000000000000000000), (-1342463982242318412480207775571/11258999068426240000000000000000000), (-74278655438876255619403198693/5629499534213120000000000000000000), (2859421404185041902399940633/2251799813685248000000000000000000), (493363552407647836420084361/2814749767106560000000000000000000), (-49109753146368012446136369/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial173.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial173.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial173.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial173 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 6575245557176603655045554669558408), (Int.ofNat 1160158211774265984019717923077319), (Int.ofNat 482182526473023337784641299949880), (Int.ofNat 34808167997802850131977310149321), (Int.negOfNat 12217827637338622962550725891858), (Int.negOfNat 1342728664506016507281158030344), (Int.ofNat 165402817249233581050661889755), (Int.ofNat 21028843475636133546961516518), (Int.negOfNat 1440956711141955157869577561), (Int.negOfNat 195296213956366300504176116), (Int.ofNat 8874636538034989928740081), (Int.ofNat 1224179195118522150010194), (Int.negOfNat 40762698938536123570232), (Int.negOfNat 5561352039553688020010), (Int.ofNat 144890580204629063879), (Int.ofNat 19093190052391148158), (Int.negOfNat 415279818648378216), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-821905694647075456880694333694801/1407374883553280000000000000000000), (1160158211774265984019717923077319/11258999068426240000000000000000000), (12054563161825583444616032498747/281474976710656000000000000000000), (34808167997802850131977310149321/11258999068426240000000000000000000), (-6108913818669311481275362945929/5629499534213120000000000000000000), (-167841083063252063410144753793/1407374883553280000000000000000000), (33080563449846716210132377951/2251799813685248000000000000000000), (10514421737818066773480758259/5629499534213120000000000000000000), (-1440956711141955157869577561/11258999068426240000000000000000000), (-48824053489091575126044029/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial173.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial173.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial173.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial173.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial173 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial173 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial173 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 9460075353955669209154482460835439), (Int.negOfNat 1598159318419980614662739244223480), (Int.ofNat 566782630717432702039577915835312), (Int.negOfNat 31140391779686026214597764420532), (Int.negOfNat 12666501910219006190019638980215), (Int.ofNat 1332288994723604459054068140345), (Int.ofNat 166401683628429577235643949415), (Int.negOfNat 21013326760453576236506290018), (Int.negOfNat 1442179071606787852250432761), (Int.ofNat 195281975931239995731402016), (Int.ofNat 8875578292082388367370381), (Int.negOfNat 1224169914635600702185394), (Int.negOfNat 40762698938536123570232), (Int.ofNat 5561352039553688020010), (Int.ofNat 144890580204629063879), (Int.negOfNat 19093190052391148158), (Int.negOfNat 415279818648378216), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-9460075353955669209154482460835439/11258999068426240000000000000000000), (-39953982960499515366568481105587/281474976710656000000000000000000), (35423914419839543877473619739707/703687441776640000000000000000000), (-7785097944921506553649441105133/2814749767106560000000000000000000), (-2533300382043801238003927796043/2251799813685248000000000000000000), (266457798944720891810813628069/2251799813685248000000000000000000), (33280336725685915447128789883/2251799813685248000000000000000000), (-10506663380226788118253145009/5629499534213120000000000000000000), (-1442179071606787852250432761/11258999068426240000000000000000000), (6102561747851249866606313/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial173.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial173.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial173.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 10790720134619906319257516141619452), (Int.ofNat 18080812756493204123502796581893), (Int.ofNat 206724221247870142958563604923293), (Int.negOfNat 65776861640395172190956275317584), (Int.ofNat 3993436172505302124451781334156), (Int.ofNat 1344745604103099287710202582808), (Int.negOfNat 147484414551487389993493793186), (Int.negOfNat 14302259590129233278247629165), (Int.ofNat 1972152854860603510115664444), (Int.ofNat 98225157785331608660516538), (Int.negOfNat 15692741430963067986345373), (Int.negOfNat 479128670952903955874524), (Int.ofNat 85444308458877028389420), (Int.ofNat 1758803369565394542792), (Int.negOfNat 341766179474644563470), (Int.negOfNat 4881273433649829309), (Int.ofNat 1145225065525343444), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-2697680033654976579814379035404863/2814749767106560000000000000000000), (18080812756493204123502796581893/11258999068426240000000000000000000), (206724221247870142958563604923293/11258999068426240000000000000000000), (-4111053852524698261934767207349/703687441776640000000000000000000), (998359043126325531112945333539/2814749767106560000000000000000000), (168093200512887410963775322851/1407374883553280000000000000000000), (-73742207275743694996746896593/5629499534213120000000000000000000), (-2860451918025846655649525833/2251799813685248000000000000000000), (493038213715150877528916111/2814749767106560000000000000000000), (49112578892665804330258269/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial173.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial173.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial173.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 10357680900419919330650305365554718), (Int.ofNat 258462749242813344144656566972391), (Int.negOfNat 25723837221933951648960380308792), (Int.negOfNat 7835562022641654440773182952631), (Int.ofNat 6972015788163905421386569670785), (Int.negOfNat 676738725611697339445754455522), (Int.negOfNat 115466461760409900482015657380), (Int.ofNat 16008205281051258844352259532), (Int.ofNat 965862589114223994343463048), (Int.negOfNat 172501722610461101347736517), (Int.negOfNat 5072833464708070721085656), (Int.ofNat 1160321346845197686685173), (Int.ofNat 18251804354135503459547), (Int.negOfNat 5473609314470638279731), (Int.negOfNat 46762601862030195290), (Int.ofNat 19394737308439518925), (Int.ofNat 53675551881171746), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-5178840450209959665325152682777359/5629499534213120000000000000000000), (258462749242813344144656566972391/11258999068426240000000000000000000), (-3215479652741743956120047538599/1407374883553280000000000000000000), (-7835562022641654440773182952631/11258999068426240000000000000000000), (1394403157632781084277313934157/2251799813685248000000000000000000), (-338369362805848669722877227761/5629499534213120000000000000000000), (-5773323088020495024100782869/562949953421312000000000000000000), (4002051320262814711088064883/2814749767106560000000000000000000), (120732823639277999292932881/1407374883553280000000000000000000), (-172501722610461101347736517/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial173.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial173.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial173.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 9921623285402095448001135451230214), (Int.ofNat 216087031329585987308927168494093), (Int.ofNat 24408166398845958398989667573854), (Int.ofNat 12135979987224092546105503156141), (Int.negOfNat 1873674578383240948557974912574), (Int.negOfNat 639245137336921084335987019031), (Int.ofNat 100903360804869602529070820307), (Int.ofNat 7750519317575808589307483573), (Int.negOfNat 1594971603606116407364436565), (Int.negOfNat 46191269127697335833455967), (Int.ofNat 13770840209163325031007816), (Int.ofNat 147584810979363862248880), (Int.negOfNat 78258508097104404280748), (Int.negOfNat 150676435003935099837), (Int.ofNat 320351891387763275979), (Int.negOfNat 1069547068461367814), (Int.negOfNat 1014530491153535264), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-4960811642701047724000567725615107/5629499534213120000000000000000000), (216087031329585987308927168494093/11258999068426240000000000000000000), (12204083199422979199494833786927/5629499534213120000000000000000000), (12135979987224092546105503156141/11258999068426240000000000000000000), (-936837289191620474278987456287/5629499534213120000000000000000000), (-639245137336921084335987019031/11258999068426240000000000000000000), (100903360804869602529070820307/11258999068426240000000000000000000), (7750519317575808589307483573/11258999068426240000000000000000000), (-318994320721223281472887313/2251799813685248000000000000000000), (-46191269127697335833455967/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial173.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial173.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial173.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 9338131349023927564763270761078768), (Int.ofNat 369430535419124052063924745367149), (Int.ofNat 27627962300630391389049149275247), (Int.negOfNat 10835779241715802939412930589304), (Int.negOfNat 1832729494044902734946363654236), (Int.ofNat 522715737662457367281380988744), (Int.ofNat 43760426364198634203772757887), (Int.negOfNat 12287515776811200449776260389), (Int.negOfNat 321121921416657668990012312), (Int.ofNat 141110776797130864120476354), (Int.ofNat 587506470735341062503708), (Int.negOfNat 989821533250989812250789), (Int.ofNat 5901477492946658082914), (Int.ofNat 4781982192908098865582), (Int.negOfNat 53568134347685982461), (Int.negOfNat 17311323510986786655), (Int.ofNat 264363856762098664), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-583633209313995472797704422567423/703687441776640000000000000000000), (369430535419124052063924745367149/11258999068426240000000000000000000), (27627962300630391389049149275247/11258999068426240000000000000000000), (-1354472405214475367426616323663/1407374883553280000000000000000000), (-458182373511225683736590913559/2814749767106560000000000000000000), (65339467207807170910172623593/1407374883553280000000000000000000), (43760426364198634203772757887/11258999068426240000000000000000000), (-12287515776811200449776260389/11258999068426240000000000000000000), (-40140240177082208623751539/1407374883553280000000000000000000), (70555388398565432060238177/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial173.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial173.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial173.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 8586824888052518144604134266403998), (Int.ofNat 335968682334760143920155359288877), (Int.negOfNat 37254858678468875236688813789929), (Int.negOfNat 4315955844847973712986662438184), (Int.ofNat 2757336040031888159577474761464), (Int.ofNat 133846924069328048245071626909), (Int.negOfNat 80745696829650754135086796485), (Int.negOfNat 1142225606437802343637538771), (Int.ofNat 1238787450146291365240152869), (Int.negOfNat 8066166086170456507882966), (Int.negOfNat 10954765765828410053951141), (Int.ofNat 181864423599112845762162), (Int.ofNat 63512873056201239756129), (Int.negOfNat 1377241843899731444808), (Int.negOfNat 262626065342441862795), (Int.ofNat 6361096680522690677), (Int.ofNat 883835916781727084), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-4293412444026259072302067133201999/5629499534213120000000000000000000), (335968682334760143920155359288877/11258999068426240000000000000000000), (-37254858678468875236688813789929/11258999068426240000000000000000000), (-539494480605996714123332804773/1407374883553280000000000000000000), (344667005003986019947184345183/1407374883553280000000000000000000), (133846924069328048245071626909/11258999068426240000000000000000000), (-16149139365930150827017359297/2251799813685248000000000000000000), (-1142225606437802343637538771/11258999068426240000000000000000000), (1238787450146291365240152869/11258999068426240000000000000000000), (-4033083043085228253941483/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial173.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial173.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial173.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 8055045656811543029998930523460851), (Int.ofNat 219282747230479640295700734522871), (Int.negOfNat 4347675632173607366735663910031), (Int.ofNat 11560181906462495776807046065569), (Int.ofNat 153907514162342585962551012466), (Int.negOfNat 469553135833524369670792374832), (Int.ofNat 5741216054800232114114810827), (Int.ofNat 9318204644096462018935869214), (Int.negOfNat 234818019221086786877512355), (Int.negOfNat 104899709287360987007997843), (Int.ofNat 3412948628319332349046260), (Int.ofNat 741293488233314571695131), (Int.negOfNat 26973414315369837582631), (Int.negOfNat 3605283368041792478370), (Int.ofNat 138374775662707569956), (Int.ofNat 13194776705493457105), (Int.negOfNat 582403265405369074), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-8055045656811543029998930523460851/11258999068426240000000000000000000), (219282747230479640295700734522871/11258999068426240000000000000000000), (-4347675632173607366735663910031/11258999068426240000000000000000000), (11560181906462495776807046065569/11258999068426240000000000000000000), (76953757081171292981275506233/5629499534213120000000000000000000), (-29347070989595273104424523427/703687441776640000000000000000000), (5741216054800232114114810827/11258999068426240000000000000000000), (4659102322048231009467934607/5629499534213120000000000000000000), (-46963603844217357375502471/2251799813685248000000000000000000), (-104899709287360987007997843/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial173.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial173.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial173.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 7552501368140945585829726074626874), (Int.ofNat 312794731744595990448612358158453), (Int.ofNat 37936353246413452983761217349460), (Int.negOfNat 758864011765935787755591907027), (Int.negOfNat 2201388203270813003043101687405), (Int.ofNat 111088183928327606088003259818), (Int.ofNat 59577705418860976142623529175), (Int.negOfNat 3355313220636704870677861502), (Int.negOfNat 857199008300766064224469048), (Int.ofNat 49771972392894842331033399), (Int.ofNat 7471570464569439868988200), (Int.negOfNat 439224405581474023067586), (Int.negOfNat 43196597486683326126690), (Int.ofNat 2549397331754862272933), (Int.ofNat 177815888866525632464), (Int.negOfNat 10493377168898926020), (Int.negOfNat 647128206195495434), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-3776250684070472792914863037313437/5629499534213120000000000000000000), (312794731744595990448612358158453/11258999068426240000000000000000000), (1896817662320672649188060867473/562949953421312000000000000000000), (-758864011765935787755591907027/11258999068426240000000000000000000), (-440277640654162600608620337481/2251799813685248000000000000000000), (55544091964163803044001629909/5629499534213120000000000000000000), (2383108216754439045704941167/450359962737049600000000000000000), (-1677656610318352435338930751/5629499534213120000000000000000000), (-107149876037595758028058631/1407374883553280000000000000000000), (49771972392894842331033399/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial173.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial173.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial173.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 6809708661924323977134256669431640), (Int.ofNat 403081449492291926701226436781929), (Int.ofNat 245282614002305417224919475400), (Int.negOfNat 7449308849113919031979955314734), (Int.ofNat 862760227700002302980198164550), (Int.ofNat 304360376136301602855820421724), (Int.negOfNat 33233271422517433682107344829), (Int.negOfNat 5806051095012738707764135342), (Int.ofNat 590914969368410025587354216), (Int.ofNat 63185966909023867236722333), (Int.negOfNat 6108197238082068806879748), (Int.negOfNat 438620494819777772132514), (Int.ofNat 41094161274433204666882), (Int.ofNat 2100425138217658046463), (Int.negOfNat 193328333952186050836), (Int.negOfNat 7452754854572488888), (Int.ofNat 707299821586343894), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-170242716548108099428356416735791/281474976710656000000000000000000), (403081449492291926701226436781929/11258999068426240000000000000000000), (1226413070011527086124597377/56294995342131200000000000000000), (-3724654424556959515989977657367/5629499534213120000000000000000000), (17255204554000046059603963291/225179981368524800000000000000000), (76090094034075400713955105431/2814749767106560000000000000000000), (-33233271422517433682107344829/11258999068426240000000000000000000), (-2903025547506369353882067671/5629499534213120000000000000000000), (73864371171051253198419277/1407374883553280000000000000000000), (63185966909023867236722333/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial173.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial173.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial173.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 6041308856989660540580044648439753), (Int.ofNat 358361693067002893245419683915735), (Int.negOfNat 10002748079471733925848112689222), (Int.ofNat 4349823369644702475781509420372), (Int.ofNat 1108405237106112831114287741723), (Int.negOfNat 247616573129081503616643166690), (Int.negOfNat 30152874336136778292484237657), (Int.ofNat 5746844497203917290259801610), (Int.ofNat 420908269347552623016755509), (Int.negOfNat 72812261147905975294659529), (Int.negOfNat 3537071785451001274143788), (Int.ofNat 580554648327608195472249), (Int.ofNat 19682566617355462265221), (Int.negOfNat 3170517016586401554266), (Int.negOfNat 77594737976212347404), (Int.ofNat 12656462292719102763), (Int.ofNat 347972217518776374), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-6041308856989660540580044648439753/11258999068426240000000000000000000), (71672338613400578649083936783147/2251799813685248000000000000000000), (-5001374039735866962924056344611/5629499534213120000000000000000000), (1087455842411175618945377355093/2814749767106560000000000000000000), (1108405237106112831114287741723/11258999068426240000000000000000000), (-24761657312908150361664316669/1125899906842624000000000000000000), (-30152874336136778292484237657/11258999068426240000000000000000000), (574684449720391729025980161/1125899906842624000000000000000000), (420908269347552623016755509/11258999068426240000000000000000000), (-72812261147905975294659529/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial173.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial173.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial173.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 5321113217187258940358796440553645), (Int.ofNat 383245446641462098461979776550924), (Int.ofNat 19908937402820056157662061366677), (Int.ofNat 2040451794479287172634986710294), (Int.negOfNat 1411704277539506526518172068393), (Int.negOfNat 95385301705775030537818824622), (Int.ofNat 45653966709398562874876287679), (Int.ofNat 1803871632931255996042902935), (Int.negOfNat 739063661016906111394160755), (Int.negOfNat 18319146316350390768865406), (Int.ofNat 7162504498758443503632067), (Int.ofNat 113834627962494943649238), (Int.negOfNat 46105096938984404459623), (Int.negOfNat 465473919264085969968), (Int.ofNat 211555277711108125425), (Int.ofNat 1135613099061415991), (Int.negOfNat 682618383428959184), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-1064222643437451788071759288110729/2251799813685248000000000000000000), (95811361660365524615494944137731/2814749767106560000000000000000000), (19908937402820056157662061366677/11258999068426240000000000000000000), (1020225897239643586317493355147/5629499534213120000000000000000000), (-1411704277539506526518172068393/11258999068426240000000000000000000), (-47692650852887515268909412311/5629499534213120000000000000000000), (45653966709398562874876287679/11258999068426240000000000000000000), (360774326586251199208580587/2251799813685248000000000000000000), (-147812732203381222278832151/2251799813685248000000000000000000), (-9159573158175195384432703/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial173.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial173.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial173.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 4481341009963586726684303280768081), (Int.ofNat 443372764896652407445031113403759), (Int.ofNat 1482864064241128620399202003559), (Int.negOfNat 6067026271500723446676064311880), (Int.ofNat 72424810860290401108040232383), (Int.ofNat 292466452543876821655081397808), (Int.negOfNat 1097496504602093514774361019), (Int.negOfNat 6310980692446934011423243475), (Int.ofNat 25683452609744227818699144), (Int.ofNat 76414673132182726345364278), (Int.negOfNat 420103546599825080624264), (Int.negOfNat 590242698695051132663331), (Int.ofNat 4017441591131386699522), (Int.ofNat 3154945171983714555714), (Int.negOfNat 24852111651193091261), (Int.negOfNat 12416523285818826313), (Int.negOfNat 29932808875505964), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-4481341009963586726684303280768081/11258999068426240000000000000000000), (443372764896652407445031113403759/11258999068426240000000000000000000), (1482864064241128620399202003559/11258999068426240000000000000000000), (-151675656787518086166901607797/281474976710656000000000000000000), (72424810860290401108040232383/11258999068426240000000000000000000), (18279153283992301353442587363/703687441776640000000000000000000), (-1097496504602093514774361019/11258999068426240000000000000000000), (-252439227697877360456929739/450359962737049600000000000000000), (3210431576218028477337393/1407374883553280000000000000000000), (38207336566091363172682139/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial173.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial173.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial173.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 3627516454156144630427858600511405), (Int.ofNat 399370598182308852664063305456333), (Int.negOfNat 13910721240154021086197712042282), (Int.ofNat 2928063182106161701702417728542), (Int.ofNat 1472062244192825113464437871732), (Int.negOfNat 104722232748463935224366987283), (Int.negOfNat 44479890021106534589766445037), (Int.ofNat 2002394294382305184211362783), (Int.ofNat 694053554954482342864889759), (Int.negOfNat 23837226744656150340296601), (Int.negOfNat 6567966678699013763845752), (Int.ofNat 190296899713477801198580), (Int.ofNat 41605291016637298344424), (Int.negOfNat 1071429966591491397807), (Int.negOfNat 187988677037521870821), (Int.ofNat 4598203455177302026), (Int.ofNat 551923809057151004), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-725503290831228926085571720102281/2251799813685248000000000000000000), (399370598182308852664063305456333/11258999068426240000000000000000000), (-6955360620077010543098856021141/5629499534213120000000000000000000), (1464031591053080850851208864271/5629499534213120000000000000000000), (368015561048206278366109467933/2814749767106560000000000000000000), (-104722232748463935224366987283/11258999068426240000000000000000000), (-44479890021106534589766445037/11258999068426240000000000000000000), (2002394294382305184211362783/11258999068426240000000000000000000), (694053554954482342864889759/11258999068426240000000000000000000), (-23837226744656150340296601/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial173.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial173.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial173.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 2843222863416380169509096102596602), (Int.ofNat 410574868949557979794219023328215), (Int.ofNat 22345981625414775069113493320246), (Int.ofNat 5547222418977930721323690426175), (Int.negOfNat 1077586710262185471016638726760), (Int.negOfNat 251046733735067579285833795520), (Int.ofNat 28110155414899541129715664536), (Int.ofNat 5238808587914373641290468052), (Int.negOfNat 411394645987273931342107688), (Int.negOfNat 62209292803523151823148835), (Int.ofNat 3834268120836073331978556), (Int.ofNat 474953261807885554650047), (Int.negOfNat 24522044776015247639141), (Int.negOfNat 2522239017547744987285), (Int.ofNat 112885276299014648690), (Int.ofNat 9969191838382208343), (Int.negOfNat 288106599767764446), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-1421611431708190084754548051298301/5629499534213120000000000000000000), (82114973789911595958843804665643/2251799813685248000000000000000000), (11172990812707387534556746660123/5629499534213120000000000000000000), (221888896759117228852947617047/450359962737049600000000000000000), (-26939667756554636775415968169/281474976710656000000000000000000), (-784521042922086185268230611/35184372088832000000000000000000), (3513769426862442641214458067/1407374883553280000000000000000000), (1309702146978593410322617013/2814749767106560000000000000000000), (-51424330748409241417763461/1407374883553280000000000000000000), (-12441858560704630364629767/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial173.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial173.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial173.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1911249073197060897815591392532459), (Int.ofNat 519162748421570975589135662954388), (Int.ofNat 18982068652050254956322715758533), (Int.negOfNat 6680082783571099326689193227280), (Int.negOfNat 1078463882294302665653510059412), (Int.ofNat 258404772878540356328824838749), (Int.ofNat 31581925474733239977313979918), (Int.negOfNat 4948240063565308319300186551), (Int.negOfNat 483846128334737977927336300), (Int.ofNat 56642709698344783144634830), (Int.ofNat 4539922470464190639990475), (Int.negOfNat 428346346884122974369716), (Int.negOfNat 28689359047630265054152), (Int.ofNat 2283822338412160870012), (Int.ofNat 130122928188516462190), (Int.negOfNat 9248696574508451903), (Int.negOfNat 421229234685342824), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-1911249073197060897815591392532459/11258999068426240000000000000000000), (129790687105392743897283915738597/2814749767106560000000000000000000), (18982068652050254956322715758533/11258999068426240000000000000000000), (-83501034794638741583614915341/140737488355328000000000000000000), (-269615970573575666413377514853/2814749767106560000000000000000000), (258404772878540356328824838749/11258999068426240000000000000000000), (15790962737366619988656989959/5629499534213120000000000000000000), (-4948240063565308319300186551/11258999068426240000000000000000000), (-4838461283347379779273363/112589990684262400000000000000000), (5664270969834478314463483/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial173.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial173.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial173.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 858125753799833097146952397770566), (Int.ofNat 504591380307730209947839150344625), (Int.negOfNat 22622073643729956024650741950152), (Int.negOfNat 3202894617449368620637375293978), (Int.ofNat 1741697207104662482285514558763), (Int.ofNat 141055518567820470040427010170), (Int.negOfNat 46019655404368008332503443281), (Int.negOfNat 2872509009612394130566666386), (Int.ofNat 670843408631592033715488155), (Int.ofNat 33834009609456827241306596), (Int.negOfNat 6163053513179501745746811), (Int.negOfNat 259069612181749529683766), (Int.ofNat 38685168080584764031856), (Int.ofNat 1388430806714064771146), (Int.negOfNat 175569779040374278681), (Int.negOfNat 5666295995869754610), (Int.ofNat 562581150287098796), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-429062876899916548573476198885283/5629499534213120000000000000000000), (4036731042461841679582713202757/90071992547409920000000000000000), (-2827759205466244503081342743769/1407374883553280000000000000000000), (-1601447308724684310318687646989/5629499534213120000000000000000000), (1741697207104662482285514558763/11258999068426240000000000000000000), (14105551856782047004042701017/1125899906842624000000000000000000), (-46019655404368008332503443281/11258999068426240000000000000000000), (-1436254504806197065283333193/5629499534213120000000000000000000), (134168681726318406743097631/2251799813685248000000000000000000), (8458502402364206810326649/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial173.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial173.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial173.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 64195932309146422696168180789990), (Int.ofNat 433295872291321981789011712803870), (Int.negOfNat 446778112245924415988890209310), (Int.ofNat 8684215267075221714999276493321), (Int.ofNat 385979318816211814893683123315), (Int.negOfNat 336894797745653419042799084449), (Int.negOfNat 10452903478000566350017290639), (Int.ofNat 6499196679123010784986377914), (Int.ofNat 155966536505330626311294625), (Int.negOfNat 74511655905549357021033004), (Int.negOfNat 1480661068157149233623109), (Int.ofNat 561850106038534099684374), (Int.ofNat 9668171646033395105124), (Int.negOfNat 2980376026205620263934), (Int.negOfNat 45653842527282426419), (Int.ofNat 11769232307474830910), (Int.ofNat 122073246008623764), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(6419593230914642269616818078999/1125899906842624000000000000000000), (43329587229132198178901171280387/1125899906842624000000000000000000), (-44677811224592441598889020931/1125899906842624000000000000000000), (8684215267075221714999276493321/11258999068426240000000000000000000), (77195863763242362978736624663/2251799813685248000000000000000000), (-336894797745653419042799084449/11258999068426240000000000000000000), (-10452903478000566350017290639/11258999068426240000000000000000000), (3249598339561505392493188957/5629499534213120000000000000000000), (1247732292042645010490357/90071992547409920000000000000000), (-18627913976387339255258251/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial173.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial173.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial173.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 994033660270306408374883918605418), (Int.ofNat 522010639248245091605586480742127), (Int.ofNat 35764274025331659875445695354283), (Int.ofNat 143454831415091263931457371578), (Int.negOfNat 1912163197354110367225842390494), (Int.ofNat 7921091191137120632209585830), (Int.ofNat 51176081085478335098792550002), (Int.negOfNat 272711907104880186780921111), (Int.negOfNat 755346323061446701520468540), (Int.ofNat 3236147876245576678347370), (Int.ofNat 6999058208466860048343965), (Int.negOfNat 19289810992065449255296), (Int.negOfNat 44163524660841457943868), (Int.ofNat 58847536996850482672), (Int.ofNat 200569371744260318510), (Int.ofNat 189968271413758077), (Int.negOfNat 687477706468073616), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(497016830135153204187441959302709/5629499534213120000000000000000000), (522010639248245091605586480742127/11258999068426240000000000000000000), (35764274025331659875445695354283/11258999068426240000000000000000000), (71727415707545631965728685789/5629499534213120000000000000000000), (-956081598677055183612921195247/5629499534213120000000000000000000), (792109119113712063220958583/1125899906842624000000000000000000), (25588040542739167549396275001/5629499534213120000000000000000000), (-272711907104880186780921111/11258999068426240000000000000000000), (-37767316153072335076023427/562949953421312000000000000000000), (323614787624557667834737/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial173.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial173.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial173.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 2154974137949831864084806988074084), (Int.ofNat 615205830684759781232067753045573), (Int.ofNat 2204286174145655330396065840435), (Int.negOfNat 8035856128314217923302695971587), (Int.ofNat 416191704158698074557741018939), (Int.ofNat 318867039524087273504258685332), (Int.negOfNat 14284372030657848925974292636), (Int.negOfNat 6303621409442524708799856028), (Int.ofNat 226282727262677305835403468), (Int.ofNat 73804763464633507157164265), (Int.negOfNat 2070818821138870092281036), (Int.negOfNat 566084756925055128733273), (Int.ofNat 12311413776704927225561), (Int.ofNat 3040480283790434421555), (Int.negOfNat 51446089171643262350), (Int.negOfNat 12070779563523201677), (Int.ofNat 239531020758582706), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(538743534487457966021201747018521/2814749767106560000000000000000000), (615205830684759781232067753045573/11258999068426240000000000000000000), (440857234829131066079213168087/2251799813685248000000000000000000), (-8035856128314217923302695971587/11258999068426240000000000000000000), (416191704158698074557741018939/11258999068426240000000000000000000), (79716759881021818376064671333/2814749767106560000000000000000000), (-3571093007664462231493573159/2814749767106560000000000000000000), (-1575905352360631177199964007/2814749767106560000000000000000000), (56570681815669326458850867/2814749767106560000000000000000000), (14760952692926701431432853/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial173.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial173.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial173.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3345150354850471343176022839971595), (Int.ofNat 561238814222986204351212499825388), (Int.negOfNat 17470086320658209759812349869627), (Int.ofNat 2981603285901133481817525166297), (Int.ofNat 1484649054881016932225649885485), (Int.negOfNat 163158886280155355062749171194), (Int.negOfNat 41593636244717050449130271993), (Int.ofNat 3573132743538398822508092983), (Int.ofNat 638716139855093879592361761), (Int.negOfNat 42390218764174052108761581), (Int.negOfNat 6130019264990815006861228), (Int.ofNat 314089808024560461050540), (Int.ofNat 39801328400603582706576), (Int.negOfNat 1589562516019335416287), (Int.negOfNat 184809976257638333899), (Int.ofNat 5760852230697439046), (Int.ofNat 556783132096265436), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(669030070970094268635204567994319/2251799813685248000000000000000000), (140309703555746551087803124956347/2814749767106560000000000000000000), (-17470086320658209759812349869627/11258999068426240000000000000000000), (2981603285901133481817525166297/11258999068426240000000000000000000), (296929810976203386445129977097/2251799813685248000000000000000000), (-81579443140077677531374585597/5629499534213120000000000000000000), (-41593636244717050449130271993/11258999068426240000000000000000000), (3573132743538398822508092983/11258999068426240000000000000000000), (638716139855093879592361761/11258999068426240000000000000000000), (-42390218764174052108761581/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial173.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial173.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial173.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4438065453959904797712115928232676), (Int.ofNat 555737957120020544842289389921035), (Int.ofNat 16306917897205335606269697165230), (Int.ofNat 4518106112419126249265320513225), (Int.negOfNat 1162463165773569908341693278002), (Int.negOfNat 198253560609952617766384702214), (Int.ofNat 37409133723914575761033944149), (Int.ofNat 4227951523606182781604685565), (Int.negOfNat 592198701638047612973382624), (Int.negOfNat 53189706688964732877326202), (Int.ofNat 5523865395297228820745764), (Int.ofNat 433535655545016994129849), (Int.negOfNat 33801963079046346483702), (Int.negOfNat 2437531808847244397626), (Int.ofNat 146092669058719214461), (Int.ofNat 9987365766070469407), (Int.negOfNat 557570429401853116), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(1109516363489976199428028982058169/2814749767106560000000000000000000), (111147591424004108968457877984207/2251799813685248000000000000000000), (1630691789720533560626969716523/1125899906842624000000000000000000), (180724244496765049970612820529/450359962737049600000000000000000), (-581231582886784954170846639001/5629499534213120000000000000000000), (-99126780304976308883192351107/5629499534213120000000000000000000), (37409133723914575761033944149/11258999068426240000000000000000000), (845590304721236556320937113/2251799813685248000000000000000000), (-18506209426188987905418207/351843720888320000000000000000000), (-26594853344482366438663101/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial173.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial173.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial173.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 5628733279032754616038516748703758), (Int.ofNat 630503735242627380625638033659997), (Int.ofNat 10242442393803902888710100417280), (Int.negOfNat 5607032586713137805054356295210), (Int.negOfNat 506796714237516667636164227365), (Int.ofNat 286577335574931394311967900436), (Int.ofNat 17099225500997642315103152741), (Int.negOfNat 6361671316026263438786460825), (Int.negOfNat 316754912923916726315529365), (Int.ofNat 76987019183224343175268734), (Int.ofNat 3554468719092039574903633), (Int.negOfNat 579800419591534554666102), (Int.negOfNat 25815609005426762656117), (Int.ofNat 2972043614451282751272), (Int.ofNat 129390257260014751555), (Int.negOfNat 11052401842758761909), (Int.negOfNat 426088557724457256), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(2814366639516377308019258374351879/5629499534213120000000000000000000), (630503735242627380625638033659997/11258999068426240000000000000000000), (8001908120159299131804765951/8796093022208000000000000000000), (-560703258671313780505435629521/1125899906842624000000000000000000), (-101359342847503333527232845473/2251799813685248000000000000000000), (71644333893732848577991975109/2814749767106560000000000000000000), (17099225500997642315103152741/11258999068426240000000000000000000), (-254466852641050537551458433/450359962737049600000000000000000), (-63350982584783345263105873/2251799813685248000000000000000000), (38493509591612171587634367/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial173.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial173.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial173.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 6887156742988951657814585498014243), (Int.ofNat 611195053087742519194054327454722), (Int.negOfNat 12997396822491067171269365170428), (Int.ofNat 849427019411317539675594028270), (Int.ofNat 1580504987275269625560921842916), (Int.negOfNat 19335821089975171744685929098), (Int.negOfNat 53140047355196504893657834343), (Int.negOfNat 284091012991200246358632990), (Int.ofNat 876013635197613653584383951), (Int.ofNat 13343868652371589876086911), (Int.negOfNat 8364368681497112798502172), (Int.negOfNat 175063824199431639033931), (Int.ofNat 51694373608922587675719), (Int.ofNat 1240949814368233962714), (Int.negOfNat 224568807918493020116), (Int.negOfNat 5870818960577139857), (Int.ofNat 875609838045123526), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(6887156742988951657814585498014243/11258999068426240000000000000000000), (305597526543871259597027163727361/5629499534213120000000000000000000), (-3249349205622766792817341292607/2814749767106560000000000000000000), (84942701941131753967559402827/1125899906842624000000000000000000), (395126246818817406390230460729/2814749767106560000000000000000000), (-9667910544987585872342964549/5629499534213120000000000000000000), (-53140047355196504893657834343/11258999068426240000000000000000000), (-28409101299120024635863299/1125899906842624000000000000000000), (876013635197613653584383951/11258999068426240000000000000000000), (13343868652371589876086911/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial173.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial173.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial173.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 8085807070855104419801786482419189), (Int.ofNat 608982016508330995385201514742542), (Int.ofNat 17073521070224831994737209064343), (Int.ofNat 5570228614648301597125688109236), (Int.negOfNat 958911447926298654761120702124), (Int.negOfNat 328743054366479907550572164907), (Int.ofNat 22419217420901448845510573519), (Int.ofNat 8042261558835248476431374658), (Int.negOfNat 205316818925305297438270656), (Int.negOfNat 102379986442640277492047347), (Int.ofNat 518355414979957519751768), (Int.ofNat 781826553105897433334926), (Int.ofNat 3892888813820860401638), (Int.negOfNat 4017978941031518595017), (Int.negOfNat 41554468297840827284), (Int.ofNat 15184682331134997252), (Int.ofNat 189380847138225606), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(8085807070855104419801786482419189/11258999068426240000000000000000000), (304491008254165497692600757371271/5629499534213120000000000000000000), (17073521070224831994737209064343/11258999068426240000000000000000000), (1392557153662075399281422027309/2814749767106560000000000000000000), (-239727861981574663690280175531/2814749767106560000000000000000000), (-328743054366479907550572164907/11258999068426240000000000000000000), (22419217420901448845510573519/11258999068426240000000000000000000), (4021130779417624238215687329/5629499534213120000000000000000000), (-3208075295707895272472979/175921860444160000000000000000000), (-102379986442640277492047347/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial173.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial173.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial173.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 9393126030721132562648304313479717), (Int.ofNat 694606869655146900860302317444236), (Int.ofNat 11154497425489121854677257980707), (Int.negOfNat 8038120944602385436459090402349), (Int.negOfNat 1253093152909624639836004618059), (Int.ofNat 343829762699388606279927070189), (Int.ofNat 55871048566118981699009310585), (Int.negOfNat 5695636110605805858161522422), (Int.negOfNat 1052965702486146811583751252), (Int.ofNat 43050972999099094647945699), (Int.ofNat 10325805899278444301852820), (Int.negOfNat 177882973068951437939566), (Int.negOfNat 63835276618361411918830), (Int.ofNat 379521120867418994053), (Int.ofNat 275879671311487173616), (Int.ofNat 128797109656171640), (Int.negOfNat 1000506394226098346), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(9393126030721132562648304313479717/11258999068426240000000000000000000), (173651717413786725215075579361059/2814749767106560000000000000000000), (11154497425489121854677257980707/11258999068426240000000000000000000), (-8038120944602385436459090402349/11258999068426240000000000000000000), (-1253093152909624639836004618059/11258999068426240000000000000000000), (343829762699388606279927070189/11258999068426240000000000000000000), (11174209713223796339801862117/2251799813685248000000000000000000), (-2847818055302902929080761211/5629499534213120000000000000000000), (-263241425621536702895937813/2814749767106560000000000000000000), (43050972999099094647945699/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial173.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial173.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial173.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 10756214998124003219426183887386978), (Int.ofNat 637420704096272561636564717797542), (Int.negOfNat 31639242677924317105331404189939), (Int.negOfNat 71123378273950868883275296072), (Int.ofNat 3060540676079796174022824904533), (Int.ofNat 222847809018862755350696525149), (Int.negOfNat 84291158616396455680382758007), (Int.negOfNat 8830027172331976606227113746), (Int.ofNat 906117867164219119819351195), (Int.ofNat 118872397400302822852253717), (Int.negOfNat 5582044938602318310599620), (Int.negOfNat 904231751436951624662129), (Int.ofNat 22718142953231147740411), (Int.ofNat 4600288985018679767330), (Int.negOfNat 65011816908910700996), (Int.negOfNat 17347767454955173995), (Int.ofNat 109775141538493454), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(5378107499062001609713091943693489/5629499534213120000000000000000000), (318710352048136280818282358898771/5629499534213120000000000000000000), (-31639242677924317105331404189939/11258999068426240000000000000000000), (-8890422284243858610409412009/1407374883553280000000000000000000), (3060540676079796174022824904533/11258999068426240000000000000000000), (222847809018862755350696525149/11258999068426240000000000000000000), (-84291158616396455680382758007/11258999068426240000000000000000000), (-4415013586165988303113556873/5629499534213120000000000000000000), (181223573432843823963870239/2251799813685248000000000000000000), (118872397400302822852253717/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial173.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial173.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial173.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 11953790741734233656315676421107843), (Int.ofNat 606799397612365243507940473119183), (Int.ofNat 35135152161455586584105176780806), (Int.ofNat 17038426745556985907170211410578), (Int.negOfNat 855480316702368784250852675237), (Int.negOfNat 952829224078850339385073956348), (Int.negOfNat 56405767673109510286493325795), (Int.ofNat 13678243472867753348138807229), (Int.ofNat 1191258430955065607920357511), (Int.negOfNat 108253548049679216417944686), (Int.negOfNat 11454065798848563817521219), (Int.ofNat 568338881719626507088862), (Int.ofNat 69172595569098118007971), (Int.negOfNat 2162528475357063567248), (Int.negOfNat 295134661714082428025), (Int.ofNat 6188344645854901257), (Int.ofNat 975824956068713636), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(11953790741734233656315676421107843/11258999068426240000000000000000000), (606799397612365243507940473119183/11258999068426240000000000000000000), (17567576080727793292052588390403/5629499534213120000000000000000000), (8519213372778492953585105705289/5629499534213120000000000000000000), (-855480316702368784250852675237/11258999068426240000000000000000000), (-238207306019712584846268489087/2814749767106560000000000000000000), (-11281153534621902057298665159/2251799813685248000000000000000000), (13678243472867753348138807229/11258999068426240000000000000000000), (1191258430955065607920357511/11258999068426240000000000000000000), (-54126774024839608208972343/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial173.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial173.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial173.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 13398439417753902536949659852229408), (Int.ofNat 844417107296053157147850987458121), (Int.ofNat 37786425676604388209986794766961), (Int.negOfNat 27875900588046544655983425724989), (Int.negOfNat 9162719270867270147585535883900), (Int.negOfNat 234817180568061297445212819790), (Int.ofNat 169093200062876461388867490063), (Int.ofNat 10556382819514152255799658131), (Int.negOfNat 1658683485563936570101587548), (Int.negOfNat 130927794259525269679106826), (Int.ofNat 10669755277726336304595692), (Int.ofNat 944483671947109698833511), (Int.negOfNat 49331579058248017685734), (Int.negOfNat 4655149232470198716118), (Int.ofNat 173113559136575442541), (Int.ofNat 17107828448054897545), (Int.negOfNat 427814550181763864), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(418701231804809454279676870382169/351843720888320000000000000000000), (844417107296053157147850987458121/11258999068426240000000000000000000), (37786425676604388209986794766961/11258999068426240000000000000000000), (-27875900588046544655983425724989/11258999068426240000000000000000000), (-91627192708672701475855358839/112589990684262400000000000000000), (-23481718056806129744521281979/1125899906842624000000000000000000), (169093200062876461388867490063/11258999068426240000000000000000000), (10556382819514152255799658131/11258999068426240000000000000000000), (-414670871390984142525396887/2814749767106560000000000000000000), (-65463897129762634839553413/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial173.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial173.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial173.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 14872988619327678878542351721867333), (Int.ofNat 384318447497680049401372434570428), (Int.negOfNat 323913521083239432839598412273922), (Int.negOfNat 81083063933666214356137743780671), (Int.negOfNat 619576916722612280405998491221), (Int.ofNat 1781653406948383599553015840376), (Int.ofNat 89171769544963839435123570333), (Int.negOfNat 21267585231163974530562111527), (Int.negOfNat 1385442028069152080998804195), (Int.ofNat 165720728204015318068895093), (Int.ofNat 11824379006138881685343924), (Int.negOfNat 916753567409842937773540), (Int.negOfNat 67257829262852580798292), (Int.ofNat 3795090871316758887243), (Int.ofNat 277252217363136399061), (Int.negOfNat 11922161200093619274), (Int.negOfNat 845130381696905456), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(14872988619327678878542351721867333/11258999068426240000000000000000000), (96079611874420012350343108642607/2814749767106560000000000000000000), (-161956760541619716419799206136961/5629499534213120000000000000000000), (-81083063933666214356137743780671/11258999068426240000000000000000000), (-619576916722612280405998491221/11258999068426240000000000000000000), (222706675868547949944126980047/1407374883553280000000000000000000), (89171769544963839435123570333/11258999068426240000000000000000000), (-21267585231163974530562111527/11258999068426240000000000000000000), (-277088405613830416199760839/2251799813685248000000000000000000), (165720728204015318068895093/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial173.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial173.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial173.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 13747131505415294768677968553572730), (Int.negOfNat 1755021571287908385994018934327674), (Int.negOfNat 677252588683751554249792352742542), (Int.negOfNat 13871090459239041451792284960476), (Int.ofNat 15822136956825179716319905575884), (Int.ofNat 841569432667712124422554558096), (Int.negOfNat 229171137082450443674984740940), (Int.negOfNat 14250408934383289620482070868), (Int.ofNat 2180247801099548557785315892), (Int.ofNat 138380885547655727051717163), (Int.negOfNat 14497585508687814905370264), (Int.negOfNat 895718421917233915577507), (Int.ofNat 70796004095498008211913), (Int.ofNat 4168089411374156956149), (Int.negOfNat 263452830832094830810), (Int.negOfNat 14660497000618279575), (Int.ofNat 745853958825034274), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(1374713150541529476867796855357273/1125899906842624000000000000000000), (-877510785643954192997009467163837/5629499534213120000000000000000000), (-338626294341875777124896176371271/5629499534213120000000000000000000), (-3467772614809760362948071240119/2814749767106560000000000000000000), (3955534239206294929079976393971/2814749767106560000000000000000000), (52598089541732007776409659881/703687441776640000000000000000000), (-11458556854122522183749237047/562949953421312000000000000000000), (-3562602233595822405120517717/2814749767106560000000000000000000), (545061950274887139446328973/2814749767106560000000000000000000), (138380885547655727051717163/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial173.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial173.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial173.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 7681315326348229119126118623673577), (Int.negOfNat 4104767101046384401494350008630565), (Int.negOfNat 373641868554591714397147555712489), (Int.ofNat 106120568683269897641583766075380), (Int.ofNat 9274787774870645024538976222022), (Int.negOfNat 1984941803825754290682291333269), (Int.negOfNat 148582120049250041287134189834), (Int.ofNat 24030641915580378516590511495), (Int.ofNat 1551789745167847604234310576), (Int.negOfNat 196593468743153023801471942), (Int.negOfNat 11133973723705092426057107), (Int.ofNat 1147252684109901723659816), (Int.ofNat 57726349461869277299320), (Int.negOfNat 4987390920656515712948), (Int.negOfNat 225716970969378772270), (Int.ofNat 16572654319424769151), (Int.ofNat 714435807325097276), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(7681315326348229119126118623673577/11258999068426240000000000000000000), (-820953420209276880298870001726113/2251799813685248000000000000000000), (-373641868554591714397147555712489/11258999068426240000000000000000000), (5306028434163494882079188303769/562949953421312000000000000000000), (4637393887435322512269488111011/5629499534213120000000000000000000), (-1984941803825754290682291333269/11258999068426240000000000000000000), (-74291060024625020643567094917/5629499534213120000000000000000000), (4806128383116075703318102299/2251799813685248000000000000000000), (96986859072990475264644411/703687441776640000000000000000000), (-98296734371576511900735971/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial173.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial173.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial173.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 1095088924145193801880906510323072), (Int.negOfNat 4204558796279380097344349423480739), (Int.ofNat 309151972415342619753202568640140), (Int.ofNat 92211489354837153078618221099819), (Int.negOfNat 11911509472383407279183933052882), (Int.negOfNat 1502312141422470907073093722716), (Int.ofNat 211279565000681597701743365825), (Int.ofNat 16765564110594595016282850742), (Int.negOfNat 2252737881641158851263431159), (Int.negOfNat 130721636022528465078224744), (Int.ofNat 16158276903975566602646459), (Int.ofNat 741333532772678781382626), (Int.negOfNat 83262858982984263870388), (Int.negOfNat 3167481225300140286390), (Int.ofNat 323111721087196766861), (Int.ofNat 10357601158105825842), (Int.negOfNat 1020328509344368624), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-8555382219884326577194582111899/87960930222080000000000000000000), (-4204558796279380097344349423480739/11258999068426240000000000000000000), (15457598620767130987660128432007/562949953421312000000000000000000), (92211489354837153078618221099819/11258999068426240000000000000000000), (-5955754736191703639591966526441/5629499534213120000000000000000000), (-375578035355617726768273430679/2814749767106560000000000000000000), (8451182600027263908069734633/450359962737049600000000000000000), (8382782055297297508141425371/5629499534213120000000000000000000), (-2252737881641158851263431159/11258999068426240000000000000000000), (-16340204502816058134778093/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial173.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial173.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial173.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial173.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial173.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial173.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial173.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial173.reflect := by
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

end Bin173
end
end ErdosOverlap.OuterNumerics
