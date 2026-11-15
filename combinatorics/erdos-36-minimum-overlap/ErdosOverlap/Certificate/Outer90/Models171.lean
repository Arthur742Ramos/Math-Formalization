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

/-! # Exact integer weighted outer models for source bin 171

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin171

def weightDenominator : ℤ := (Int.ofNat 20000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 875056441436322100)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 3444556149427284000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 2343433854922876400)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 967282705485290000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 1704403665615142600)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 1395498019697918000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 988719128909287800)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 690488482436874000)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 370785129046860500)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 211119245156227840)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial171.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial171.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 17682561224913494000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 6829441777527171000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 2256399115246639200)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 1806355143547472000)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 903848509574653320)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 336932890397547000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 6694197087470273)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 80630908201449300)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 79185343843206720)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial171.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial171.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 17682561224913494000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 6829441777527171000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 2256399115246639200)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 1806355143547472000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 903848509574653320)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 336932890397547000)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 6694197087470273)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 80630908201449300)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 79185343843206720)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial171.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial171.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial171.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 7993695159208021283067324494096651), (Int.ofNat 7566128404420886663099124389475372), (Int.ofNat 782450104178294406203594705150938), (Int.negOfNat 177339498040613667726293076326760), (Int.negOfNat 24371226420577803767741930021067), (Int.ofNat 2992283481032272888955899007027), (Int.ofNat 416707749340896372123200620307), (Int.negOfNat 33732874551717620952556339956), (Int.negOfNat 4410863401563838697318231203), (Int.ofNat 264535347808108031952093070), (Int.ofNat 31545598237859218307899565), (Int.negOfNat 1507570276044080008400324), (Int.negOfNat 162224453638529053981458), (Int.ofNat 6468804421631085271982), (Int.ofNat 628563822338405225459), (Int.negOfNat 21235703373800510814), (Int.negOfNat 1982124326088689320), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-7993695159208021283067324494096651/22517998136852480000000000000000000), (1891532101105221665774781097368843/5629499534213120000000000000000000), (391225052089147203101797352575469/11258999068426240000000000000000000), (-4433487451015341693157326908169/562949953421312000000000000000000), (-24371226420577803767741930021067/22517998136852480000000000000000000), (2992283481032272888955899007027/22517998136852480000000000000000000), (416707749340896372123200620307/22517998136852480000000000000000000), (-8433218637929405238139084989/5629499534213120000000000000000000), (-4410863401563838697318231203/22517998136852480000000000000000000), (26453534780810803195209307/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial171.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial171.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial171.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial171 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 8576845892937278552185143241317400), (Int.ofNat 8088487558645766460909440173230133), (Int.negOfNat 556146326158161818620634190586401), (Int.negOfNat 210912363158683643045395242787844), (Int.ofNat 17577982581488368716769371325100), (Int.ofNat 3912507041674094090922956523746), (Int.negOfNat 295854922150488940213001597804), (Int.negOfNat 47060165096147837392246179577), (Int.ofNat 3118147845940648016768025602), (Int.ofNat 383270068261802626866286154), (Int.negOfNat 22447437083662063295284859), (Int.negOfNat 2228844195572943697223304), (Int.ofNat 116658349320562240748014), (Int.ofNat 9662157508335530492450), (Int.negOfNat 456998148489579039740), (Int.negOfNat 32024384602555002673), (Int.ofNat 1451247561566179200), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(42884229464686392760925716206587/112589990684262400000000000000000), (8088487558645766460909440173230133/22517998136852480000000000000000000), (-556146326158161818620634190586401/22517998136852480000000000000000000), (-52728090789670910761348810696961/5629499534213120000000000000000000), (175779825814883687167693713251/225179981368524800000000000000000), (1956253520837047045461478261873/11258999068426240000000000000000000), (-73963730537622235053250399451/5629499534213120000000000000000000), (-47060165096147837392246179577/22517998136852480000000000000000000), (1559073922970324008384012801/11258999068426240000000000000000000), (191635034130901313433143077/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial171.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial171.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial171.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial171 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 21224393808644164232634793724509048), (Int.ofNat 4134502126146309421698181578430297), (Int.negOfNat 1182336268366976070987063574800884), (Int.ofNat 19746118167188277688279746898905), (Int.ofNat 30434516217842053734990412114587), (Int.negOfNat 1653664434170189568288400302704), (Int.negOfNat 447680898140158186928010606812), (Int.ofNat 28477023122360385558702950620), (Int.ofNat 4247465435047925200019746600), (Int.negOfNat 277269203762805034316824441), (Int.negOfNat 28107103573486482883421280), (Int.ofNat 1796854335506640985006093), (Int.ofNat 136643921662052924072843), (Int.negOfNat 8369157384370988407833), (Int.negOfNat 506530261495177390980), (Int.ofNat 29459027639969371661), (Int.ofNat 1427951934463212520), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(2653049226080520529079349215563631/2814749767106560000000000000000000), (4134502126146309421698181578430297/22517998136852480000000000000000000), (-295584067091744017746765893700221/5629499534213120000000000000000000), (3949223633437655537655949379781/4503599627370496000000000000000000), (30434516217842053734990412114587/22517998136852480000000000000000000), (-103354027135636848018025018919/1407374883553280000000000000000000), (-111920224535039546732002651703/5629499534213120000000000000000000), (1423851156118019277935147531/1125899906842624000000000000000000), (21237327175239626000098733/112589990684262400000000000000000), (-277269203762805034316824441/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial171.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial171.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial171.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial171 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 25331971183343279189496361887620694), (Int.ofNat 414114578797430898343789233816451), (Int.negOfNat 547962837094880987714408180029006), (Int.ofNat 147171515441574844999255524047039), (Int.negOfNat 1638240928730385278280949777628), (Int.negOfNat 3452725429073594240323950497029), (Int.ofNat 178450988099822670231174390665), (Int.ofNat 41390722611242781366667443685), (Int.negOfNat 2762780279876992590008999943), (Int.negOfNat 320826695883147138611318843), (Int.ofNat 23581344759757453335085382), (Int.ofNat 1763521801804781738141640), (Int.negOfNat 134173633351423917002532), (Int.negOfNat 7256523986911125746255), (Int.ofNat 553266280305794188709), (Int.ofNat 22649508305304241200), (Int.negOfNat 1688803593095799360), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(12665985591671639594748180943810347/11258999068426240000000000000000000), (414114578797430898343789233816451/22517998136852480000000000000000000), (-273981418547440493857204090014503/11258999068426240000000000000000000), (147171515441574844999255524047039/22517998136852480000000000000000000), (-409560232182596319570237444407/5629499534213120000000000000000000), (-3452725429073594240323950497029/22517998136852480000000000000000000), (35690197619964534046234878133/4503599627370496000000000000000000), (8278144522248556273333488737/4503599627370496000000000000000000), (-2762780279876992590008999943/22517998136852480000000000000000000), (-320826695883147138611318843/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial171.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial171.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial171.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial171 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 25024896547898090101418724011984296), (Int.negOfNat 290945981386809544353398828900115), (Int.ofNat 84055283463864516216929105881125), (Int.ofNat 41431776753806443750586610027572), (Int.negOfNat 17884536645395810485130688966564), (Int.ofNat 507928117954208140323158070406), (Int.ofNat 329140718469620858837281626529), (Int.negOfNat 20990400165377230521607993677), (Int.negOfNat 3207438881834171169809106024), (Int.ofNat 259705654259454800533173368), (Int.ofNat 20460773657791589228241922), (Int.negOfNat 1873454517193577329369259), (Int.negOfNat 93749560494577673142012), (Int.ofNat 9234718955945607547964), (Int.ofNat 325990486045399569289), (Int.negOfNat 33941773263160386301), (Int.negOfNat 794594198994529000), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(3128112068487261262677340501498037/2814749767106560000000000000000000), (-58189196277361908870679765780023/4503599627370496000000000000000000), (672442267710916129735432847049/180143985094819840000000000000000), (10357944188451610937646652506893/5629499534213120000000000000000000), (-4471134161348952621282672241641/5629499534213120000000000000000000), (253964058977104070161579035203/11258999068426240000000000000000000), (329140718469620858837281626529/22517998136852480000000000000000000), (-20990400165377230521607993677/22517998136852480000000000000000000), (-400929860229271396226138253/2814749767106560000000000000000000), (32463206782431850066646671/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial171.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial171.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial171.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial171 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 24858487957008938818854099366101938), (Int.ofNat 61972686491471681835690917522821), (Int.ofNat 4566712869150853302616595457515), (Int.negOfNat 44543588791495931579793264605064), (Int.negOfNat 1291728228203255789334335391666), (Int.ofNat 1884422707356033239966483201677), (Int.negOfNat 111740491477807528600216599753), (Int.negOfNat 26438394592206578235800882563), (Int.ofNat 2348384823497909685031090577), (Int.ofNat 206854622279177495775471010), (Int.negOfNat 22590106633988477334385057), (Int.negOfNat 1072081381918138153303828), (Int.ofNat 136456616477752116089433), (Int.ofNat 4016491695581984621200), (Int.negOfNat 582262462386579101615), (Int.negOfNat 11268686640876889647), (Int.ofNat 1926359624625419520), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(12429243978504469409427049683050969/11258999068426240000000000000000000), (61972686491471681835690917522821/22517998136852480000000000000000000), (913342573830170660523319091503/4503599627370496000000000000000000), (-5567948598936991447474158075633/2814749767106560000000000000000000), (-645864114101627894667167695833/11258999068426240000000000000000000), (1884422707356033239966483201677/22517998136852480000000000000000000), (-111740491477807528600216599753/22517998136852480000000000000000000), (-26438394592206578235800882563/22517998136852480000000000000000000), (2348384823497909685031090577/22517998136852480000000000000000000), (20685462227917749577547101/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial171.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial171.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial171.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial171 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 24674132190398642616780568515302549), (Int.negOfNat 375406488644626258805693833434497), (Int.negOfNat 182646095074068779819193909164859), (Int.negOfNat 7240298192496608799719419514045), (Int.ofNat 6578799891122588714366657800674), (Int.negOfNat 407516788118738931823107251804), (Int.negOfNat 163114366724920947615461727905), (Int.ofNat 17211857582747206579183634382), (Int.ofNat 1721544653931840422155470897), (Int.negOfNat 232864680267764879552738927), (Int.negOfNat 10414422543895202362116664), (Int.ofNat 1773341641898998547675011), (Int.ofNat 41227179930677492522265), (Int.negOfNat 9024751347521473041552), (Int.negOfNat 112712382400327283184), (Int.ofNat 34043763295540430701), (Int.ofNat 161236463525845480), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(24674132190398642616780568515302549/22517998136852480000000000000000000), (-375406488644626258805693833434497/22517998136852480000000000000000000), (-182646095074068779819193909164859/22517998136852480000000000000000000), (-1448059638499321759943883902809/4503599627370496000000000000000000), (3289399945561294357183328900337/11258999068426240000000000000000000), (-101879197029684732955776812951/5629499534213120000000000000000000), (-32622873344984189523092345581/4503599627370496000000000000000000), (8605928791373603289591817191/11258999068426240000000000000000000), (1721544653931840422155470897/22517998136852480000000000000000000), (-232864680267764879552738927/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial171.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial171.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial171.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial171 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 23219111056941792306487986486691570), (Int.negOfNat 1037367717512777243417087923373263), (Int.negOfNat 126435847618205712072260625753324), (Int.ofNat 14379817650060821862490106857291), (Int.negOfNat 1537856329131151594551713089395), (Int.negOfNat 647651679178290633418159457096), (Int.ofNat 105857970965944336841082988623), (Int.ofNat 10647905606376329497283625040), (Int.negOfNat 2043648222749900115279616146), (Int.negOfNat 78514475172210095832149247), (Int.ofNat 20112799295203550222232406), (Int.ofNat 305045270707900734385214), (Int.negOfNat 124464413963600521367414), (Int.negOfNat 517401812702113535205), (Int.ofNat 538021937080919048044), (Int.negOfNat 1119614911914103266), (Int.negOfNat 1952796410998811840), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(2321911105694179230648798648669157/2251799813685248000000000000000000), (-1037367717512777243417087923373263/22517998136852480000000000000000000), (-31608961904551428018065156438331/5629499534213120000000000000000000), (14379817650060821862490106857291/22517998136852480000000000000000000), (-307571265826230318910342617879/4503599627370496000000000000000000), (-80956459897286329177269932137/2814749767106560000000000000000000), (105857970965944336841082988623/22517998136852480000000000000000000), (133098820079704118716045313/281474976710656000000000000000000), (-1021824111374950057639808073/11258999068426240000000000000000000), (-78514475172210095832149247/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial171.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial171.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial171.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial171 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 20715935401238456730032162140900890), (Int.negOfNat 1448652046120427892436645488786381), (Int.negOfNat 100108342659779103537499836011256), (Int.negOfNat 4705269926109097290510598373438), (Int.negOfNat 1019160297709570388501951859434), (Int.ofNat 602184522973524539935950192896), (Int.ofNat 38291737897839406119979691943), (Int.negOfNat 15423183162991855030379220760), (Int.negOfNat 343546984191042287957465666), (Int.ofNat 197740686389594415011239407), (Int.ofNat 505726387679311173769526), (Int.negOfNat 1513318729482630537609534), (Int.ofNat 10739382013157532890426), (Int.ofNat 7783315091860576514965), (Int.negOfNat 95160362622915121156), (Int.negOfNat 29428513772450755934), (Int.ofNat 419372714473023640), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(2071593540123845673003216214090089/2251799813685248000000000000000000), (-1448652046120427892436645488786381/22517998136852480000000000000000000), (-12513542832472387942187479501407/2814749767106560000000000000000000), (-2352634963054548645255299186719/11258999068426240000000000000000000), (-509580148854785194250975929717/11258999068426240000000000000000000), (2352283292865330234124805441/87960930222080000000000000000000), (38291737897839406119979691943/22517998136852480000000000000000000), (-385579579074796375759480519/562949953421312000000000000000000), (-171773492095521143978732833/11258999068426240000000000000000000), (197740686389594415011239407/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial171.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial171.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial171.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial171 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 17384006441788694117498087188704277), (Int.negOfNat 1889454589446332369829534874193271), (Int.negOfNat 105538735406736465461534126168654), (Int.ofNat 9113154934141970396791708248156), (Int.ofNat 3341127404688343766198068632829), (Int.negOfNat 26320360336931786251291076596), (Int.negOfNat 101698681180702334106689107185), (Int.ofNat 1091685217004252763741278258), (Int.ofNat 1675165360723334765401379057), (Int.negOfNat 31379488264813445407933713), (Int.negOfNat 16041655739079602889498184), (Int.ofNat 380787313785806311890589), (Int.ofNat 99295400267493264857865), (Int.negOfNat 2625502176239989294928), (Int.negOfNat 431591286792241232864), (Int.ofNat 12241451024321669619), (Int.ofNat 1688928608372769600), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(17384006441788694117498087188704277/22517998136852480000000000000000000), (-1889454589446332369829534874193271/22517998136852480000000000000000000), (-52769367703368232730767063084327/11258999068426240000000000000000000), (2278288733535492599197927062039/5629499534213120000000000000000000), (3341127404688343766198068632829/22517998136852480000000000000000000), (-6580090084232946562822769149/5629499534213120000000000000000000), (-20339736236140466821337821437/4503599627370496000000000000000000), (545842608502126381870639129/11258999068426240000000000000000000), (1675165360723334765401379057/22517998136852480000000000000000000), (-31379488264813445407933713/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial171.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial171.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial171.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial171 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 13302491875639595841914057467535809), (Int.negOfNat 2114910814068852491825250627271518), (Int.ofNat 6236918053285519833231001894693), (Int.ofNat 21741921272149306183721314708566), (Int.negOfNat 1156955699897516320406973767853), (Int.negOfNat 577084258605408022853397534944), (Int.ofNat 36850074218103236686402485007), (Int.ofNat 12051603880363278467844350683), (Int.negOfNat 665419152552428711611372543), (Int.negOfNat 145827844756720268561666090), (Int.ofNat 7360101749111575433599023), (Int.ofNat 1100929723091645405484708), (Int.negOfNat 52981136058618867394567), (Int.negOfNat 5650026235260899354000), (Int.ofNat 264065668125353221185), (Int.ofNat 21012867805995039567), (Int.negOfNat 868047991158871640), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(13302491875639595841914057467535809/22517998136852480000000000000000000), (-1057455407034426245912625313635759/11258999068426240000000000000000000), (6236918053285519833231001894693/22517998136852480000000000000000000), (10870960636074653091860657354283/11258999068426240000000000000000000), (-1156955699897516320406973767853/22517998136852480000000000000000000), (-18033883081419000714168672967/703687441776640000000000000000000), (36850074218103236686402485007/22517998136852480000000000000000000), (12051603880363278467844350683/22517998136852480000000000000000000), (-665419152552428711611372543/22517998136852480000000000000000000), (-14582784475672026856166609/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial171.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial171.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial171.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial171 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 9238240834392048559273390369954129), (Int.negOfNat 1900743936971123280773908606371907), (Int.ofNat 77944479417743400354076773593871), (Int.ofNat 223576196470752480133521541834), (Int.negOfNat 2538630651328498472735494164839), (Int.ofNat 370350935321188676466152637174), (Int.ofNat 69928435419033543112842444969), (Int.negOfNat 8535231582819923505678700243), (Int.negOfNat 1100389404156406697618891104), (Int.ofNat 107614719231818883068936192), (Int.ofNat 10304065926508397304591762), (Int.negOfNat 874557841345199257179461), (Int.negOfNat 63198813378811408377132), (Int.ofNat 4904838492188451511476), (Int.ofNat 273338227678384301609), (Int.negOfNat 20057995376262297219), (Int.negOfNat 1055570872904086080), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(9238240834392048559273390369954129/22517998136852480000000000000000000), (-1900743936971123280773908606371907/22517998136852480000000000000000000), (77944479417743400354076773593871/22517998136852480000000000000000000), (111788098235376240066760770917/11258999068426240000000000000000000), (-2538630651328498472735494164839/22517998136852480000000000000000000), (185175467660594338233076318587/11258999068426240000000000000000000), (69928435419033543112842444969/22517998136852480000000000000000000), (-8535231582819923505678700243/22517998136852480000000000000000000), (-34387168879887709300590347/703687441776640000000000000000000), (6568281203113945499813/1374389534720000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial171.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial171.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial171.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial171 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 5724717481859580021838991504537211), (Int.negOfNat 1629125949562566410921552269511043), (Int.ofNat 57648686691228429449951569622178), (Int.negOfNat 140161982197878935160154485768), (Int.ofNat 2267738521426272000445178732112), (Int.ofNat 269164933729357315963380862529), (Int.negOfNat 81305304378163443762590129175), (Int.negOfNat 6350206623725461534111796005), (Int.ofNat 1272546013828530006155885817), (Int.ofNat 76439556579618363388558323), (Int.negOfNat 12217565734721294427879258), (Int.negOfNat 569354536308171959205640), (Int.ofNat 79248970550847973106508), (Int.ofNat 2885911908699884243455), (Int.negOfNat 367661309779492608251), (Int.negOfNat 10437287974174695760), (Int.ofNat 1105604022688491800), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(5724717481859580021838991504537211/22517998136852480000000000000000000), (-1629125949562566410921552269511043/22517998136852480000000000000000000), (28824343345614214724975784811089/11258999068426240000000000000000000), (-17520247774734866895019310721/2814749767106560000000000000000000), (141733657589142000027823670757/1407374883553280000000000000000000), (269164933729357315963380862529/22517998136852480000000000000000000), (-3252212175126537750503605167/900719925474099200000000000000000), (-1270041324745092306822359201/4503599627370496000000000000000000), (1272546013828530006155885817/22517998136852480000000000000000000), (76439556579618363388558323/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial171.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial171.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial171.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial171 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 2735171335871915926072199517614362), (Int.negOfNat 1323155536474381435005074928917377), (Int.ofNat 111467551544658032298844271874038), (Int.ofNat 14692492415418590772243759318359), (Int.negOfNat 141084814986858108123022141018), (Int.negOfNat 622484148305186698834391673476), (Int.negOfNat 20763141144976097674601314932), (Int.ofNat 12436756717658174221481999620), (Int.ofNat 369160865995643125283011200), (Int.negOfNat 145694311081121615331453079), (Int.negOfNat 3444936567017869660018480), (Int.ofNat 1117103377629407712291347), (Int.ofNat 20542104934276641046603), (Int.negOfNat 5998438752584369556487), (Int.negOfNat 85483745054736901140), (Int.ofNat 23810525512764781459), (Int.ofNat 422213137435402560), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(1367585667935957963036099758807181/11258999068426240000000000000000000), (-1323155536474381435005074928917377/22517998136852480000000000000000000), (55733775772329016149422135937019/11258999068426240000000000000000000), (14692492415418590772243759318359/22517998136852480000000000000000000), (-70542407493429054061511070509/11258999068426240000000000000000000), (-155621037076296674708597918369/5629499534213120000000000000000000), (-5190785286244024418650328733/5629499534213120000000000000000000), (621837835882908711074099981/1125899906842624000000000000000000), (115362770623638476650941/7036874417766400000000000000000), (-145694311081121615331453079/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial171.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial171.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial171.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial171 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 630375326749404522346957962740739), (Int.negOfNat 753666255860952616482789292964828), (Int.ofNat 149794452826752102685554942466947), (Int.negOfNat 7819977126655871919786756463228), (Int.negOfNat 4302129418390881884592128138106), (Int.ofNat 50052478801548956873464218827), (Int.ofNat 101623719616921106830726726236), (Int.negOfNat 182039606507287148591216143), (Int.negOfNat 1480125926803519521288813718), (Int.ofNat 759158121280443537969446), (Int.ofNat 13696747460834558278940341), (Int.negOfNat 11785553844365757938776), (Int.negOfNat 86422933373328752525986), (Int.ofNat 131987112170569758430), (Int.ofNat 392558958546816366100), (Int.negOfNat 1299760244197326767), (Int.negOfNat 1343160054218111960), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(630375326749404522346957962740739/22517998136852480000000000000000000), (-188416563965238154120697323241207/5629499534213120000000000000000000), (149794452826752102685554942466947/22517998136852480000000000000000000), (-1954994281663967979946689115807/5629499534213120000000000000000000), (-2151064709195440942296064069053/11258999068426240000000000000000000), (50052478801548956873464218827/22517998136852480000000000000000000), (25405929904230276707681681559/5629499534213120000000000000000000), (-182039606507287148591216143/22517998136852480000000000000000000), (-740062963401759760644406859/11258999068426240000000000000000000), (379579060640221768984723/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial171.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial171.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial171.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial171 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 401455833858141963420726987112874), (Int.negOfNat 364007890682733227069815158957665), (Int.ofNat 25397935170569636133755863797342), (Int.negOfNat 26524891003146456836292078283194), (Int.ofNat 763241620894830164684526083865), (Int.ofNat 694453057826888748424882424386), (Int.negOfNat 25134154246903958413567489133), (Int.negOfNat 12680101558468178245953712204), (Int.ofNat 375014139747226771657509997), (Int.ofNat 144565487288709896227718330), (Int.negOfNat 3502552898928024527634275), (Int.negOfNat 1089860727699437140316956), (Int.ofNat 22497570780170893639902), (Int.ofNat 5784050356544683643298), (Int.negOfNat 104735009808579521181), (Int.negOfNat 22858864485995998306), (Int.ofNat 290329941876487680), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-200727916929070981710363493556437/11258999068426240000000000000000000), (-72801578136546645413963031791533/4503599627370496000000000000000000), (12698967585284818066877931898671/11258999068426240000000000000000000), (-13262445501573228418146039141597/11258999068426240000000000000000000), (152648324178966032936905216773/4503599627370496000000000000000000), (347226528913444374212441212193/11258999068426240000000000000000000), (-25134154246903958413567489133/22517998136852480000000000000000000), (-3170025389617044561488428051/5629499534213120000000000000000000), (375014139747226771657509997/22517998136852480000000000000000000), (14456548728870989622771833/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial171.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial171.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial171.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial171 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 1208711938061063260664257317958152), (Int.negOfNat 510553581082051151553731220391212), (Int.negOfNat 73161062738708004548837757514214), (Int.negOfNat 2409673177569484661974343550419), (Int.ofNat 3563889300804036766988518137639), (Int.negOfNat 269290890554010693464474074087), (Int.negOfNat 88920555771157577871075213507), (Int.ofNat 6145912281820084496334695156), (Int.ofNat 1287626178918883243623077203), (Int.negOfNat 72557233259179395377807070), (Int.negOfNat 11826095715787691957208365), (Int.ofNat 552585465082452438963524), (Int.ofNat 74292732897172895838658), (Int.negOfNat 2946800075331807954382), (Int.negOfNat 337539274562903496259), (Int.ofNat 11950768306747352414), (Int.ofNat 1079292251592069720), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-151088992257632907583032164744769/2814749767106560000000000000000000), (-127638395270512787888432805097803/5629499534213120000000000000000000), (-36580531369354002274418878757107/11258999068426240000000000000000000), (-2409673177569484661974343550419/22517998136852480000000000000000000), (3563889300804036766988518137639/22517998136852480000000000000000000), (-269290890554010693464474074087/22517998136852480000000000000000000), (-88920555771157577871075213507/22517998136852480000000000000000000), (1536478070455021124083673789/5629499534213120000000000000000000), (1287626178918883243623077203/22517998136852480000000000000000000), (-7255723325917939537780707/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial171.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial171.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial171.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial171 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 2497958275230273618085291022238734), (Int.negOfNat 752833436144076308653641909737571), (Int.negOfNat 38983067104596906667809411340751), (Int.ofNat 6310558492318322437668193352256), (Int.negOfNat 1721378619152019520529288652806), (Int.negOfNat 462266969289371514212146030686), (Int.ofNat 64536423767445185944270975404), (Int.ofNat 9300304248666852494437038377), (Int.negOfNat 1002694920333675254061300802), (Int.negOfNat 106959001672079609304362154), (Int.ofNat 9388123897756970707655259), (Int.ofNat 810298007927497391733704), (Int.negOfNat 59166211612839264918814), (Int.negOfNat 4328647070074643204850), (Int.ofNat 267756728803426192540), (Int.ofNat 17579071410609089073), (Int.negOfNat 870939119875356800), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-1248979137615136809042645511119367/11258999068426240000000000000000000), (-752833436144076308653641909737571/22517998136852480000000000000000000), (-38983067104596906667809411340751/22517998136852480000000000000000000), (98602476442473788088565521129/351843720888320000000000000000000), (-860689309576009760264644326403/11258999068426240000000000000000000), (-231133484644685757106073015343/11258999068426240000000000000000000), (16134105941861296486067743851/5629499534213120000000000000000000), (9300304248666852494437038377/22517998136852480000000000000000000), (-501347460166837627030650401/11258999068426240000000000000000000), (-53479500836039804652181077/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial171.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial171.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial171.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial171 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 4146387231743958854178709356352454), (Int.negOfNat 909764595183118260727008328848997), (Int.negOfNat 59838919021776042148714035280527), (Int.negOfNat 12618268426695170616575219697129), (Int.negOfNat 1270418542395882180701955973819), (Int.ofNat 521117575157409389944446510904), (Int.ofNat 49877564392907298652979488812), (Int.negOfNat 10689159955146009846127831020), (Int.negOfNat 753323386424238748477467000), (Int.ofNat 126465661198624802549405641), (Int.ofNat 7058871490392751042743280), (Int.negOfNat 963735446306844118511693), (Int.negOfNat 45337004570703725381243), (Int.ofNat 5110844097445350789833), (Int.ofNat 209485080777086522180), (Int.negOfNat 20174092572916213261), (Int.negOfNat 525119859966592920), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-2073193615871979427089354678176227/11258999068426240000000000000000000), (-909764595183118260727008328848997/22517998136852480000000000000000000), (-59838919021776042148714035280527/22517998136852480000000000000000000), (-12618268426695170616575219697129/22517998136852480000000000000000000), (-1270418542395882180701955973819/22517998136852480000000000000000000), (65139696894676173743055813863/2814749767106560000000000000000000), (12469391098226824663244872203/5629499534213120000000000000000000), (-534457997757300492306391551/1125899906842624000000000000000000), (-753323386424238748477467/22517998136852480000000000000000), (126465661198624802549405641/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial171.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial171.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial171.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial171 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 6308168215127301257382911335923797), (Int.negOfNat 1295171294511872969095460832648506), (Int.negOfNat 120276878391007965586037621410017), (Int.negOfNat 548285841128229052813222623363), (Int.ofNat 3657078499091760241326385173721), (Int.ofNat 164889262224571852469357049142), (Int.negOfNat 91140049867498487108096004425), (Int.negOfNat 3374350318554034488515157685), (Int.ofNat 1395382832149585820204467543), (Int.ofNat 40731877595399717232105243), (Int.negOfNat 13174904780872893213011782), (Int.negOfNat 329825547155291926058040), (Int.ofNat 83388504743772740526132), (Int.ofNat 1882533135124957275055), (Int.negOfNat 376563355947347889109), (Int.negOfNat 8204195113358327600), (Int.ofNat 1108495151404976960), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-6308168215127301257382911335923797/22517998136852480000000000000000000), (-647585647255936484547730416324253/11258999068426240000000000000000000), (-120276878391007965586037621410017/22517998136852480000000000000000000), (-548285841128229052813222623363/22517998136852480000000000000000000), (3657078499091760241326385173721/22517998136852480000000000000000000), (82444631112285926234678524571/11258999068426240000000000000000000), (-3645601994699939484323840177/900719925474099200000000000000000), (-674870063710806897703031537/4503599627370496000000000000000000), (1395382832149585820204467543/22517998136852480000000000000000000), (40731877595399717232105243/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial171.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial171.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial171.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial171 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 9326115515325329363396392142503490), (Int.negOfNat 1670197531025573724415090417996223), (Int.negOfNat 44213796400076274457520830224512), (Int.ofNat 21344725192431439296998753348649), (Int.ofNat 439664599811132482847241100016), (Int.negOfNat 612309665724653306352651384686), (Int.ofNat 1175368298423259136049461071), (Int.ofNat 12576987054001003781387624477), (Int.negOfNat 14959073690135906569350776), (Int.negOfNat 151782292199305784735363768), (Int.negOfNat 231376336428199729833522), (Int.ofNat 1172206677709812844047259), (Int.ofNat 4333009346669135604012), (Int.negOfNat 6265160121339057511164), (Int.negOfNat 33485729454607532889), (Int.ofNat 24656838196107227901), (Int.negOfNat 108237875502090600), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-932611551532532936339639214250349/2251799813685248000000000000000000), (-1670197531025573724415090417996223/22517998136852480000000000000000000), (-345420284375595894199381486129/175921860444160000000000000000000), (21344725192431439296998753348649/22517998136852480000000000000000000), (27479037488195780177952568751/1407374883553280000000000000000000), (-306154832862326653176325692343/11258999068426240000000000000000000), (1175368298423259136049461071/22517998136852480000000000000000000), (12576987054001003781387624477/22517998136852480000000000000000000), (-1869884211266988321168847/2814749767106560000000000000000000), (-18972786524913223091920471/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial171.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial171.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial171.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial171 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 12683561570842670177611042487007960), (Int.negOfNat 1620324589719103648540289234640117), (Int.ofNat 53458980862981632926049187025450), (Int.ofNat 6802673166573304309374724726862), (Int.negOfNat 2675399555228779234781493699041), (Int.ofNat 176777151699534417561448050730), (Int.ofNat 89049599174964024106712788553), (Int.negOfNat 4104743919758204273284029837), (Int.negOfNat 1451609778058040710997220977), (Int.ofNat 42948144974927118030404590), (Int.ofNat 14094829838139548148159057), (Int.negOfNat 274042374054725730540172), (Int.negOfNat 90801258719692698248233), (Int.ofNat 1168397882588260550400), (Int.ofNat 416838619963382574415), (Int.negOfNat 3176626551069023953), (Int.negOfNat 1346051182934597120), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-317089039271066754440276062175199/562949953421312000000000000000000), (-1620324589719103648540289234640117/22517998136852480000000000000000000), (1069179617259632658520983740509/450359962737049600000000000000000), (3401336583286652154687362363431/11258999068426240000000000000000000), (-2675399555228779234781493699041/22517998136852480000000000000000000), (17677715169953441756144805073/2251799813685248000000000000000000), (89049599174964024106712788553/22517998136852480000000000000000000), (-4104743919758204273284029837/22517998136852480000000000000000000), (-1451609778058040710997220977/22517998136852480000000000000000000), (4294814497492711803040459/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial171.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial171.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial171.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial171 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 15688265304933012174802205897756061), (Int.negOfNat 1382389144539137786770444266092582), (Int.ofNat 60566593439255809281172629836144), (Int.ofNat 2244778980719484986642866515294), (Int.ofNat 2000570027745907889492265445434), (Int.ofNat 433976960225965631976582295224), (Int.negOfNat 63642298442434636407866748895), (Int.negOfNat 11065888893809079327192529182), (Int.ofNat 898358059601342064767759103), (Int.ofNat 141680386259235769445148927), (Int.negOfNat 7579721526863246589968936), (Int.negOfNat 1132802938443016224416211), (Int.ofNat 42423073282114270415735), (Int.ofNat 6195229171788217382752), (Int.negOfNat 168601610424348393616), (Int.negOfNat 24758828228487272301), (Int.ofNat 741595610970774120), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-15688265304933012174802205897756061/22517998136852480000000000000000000), (-691194572269568893385222133046291/11258999068426240000000000000000000), (3785412089953488080073289364759/1407374883553280000000000000000000), (1122389490359742493321433257647/11258999068426240000000000000000000), (1000285013872953944746132722717/11258999068426240000000000000000000), (54247120028245703997072786903/2814749767106560000000000000000000), (-12728459688486927281573349779/4503599627370496000000000000000000), (-5532944446904539663596264591/11258999068426240000000000000000000), (898358059601342064767759103/22517998136852480000000000000000000), (141680386259235769445148927/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial171.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial171.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial171.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial171 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 18152119486705803331135632855074857), (Int.negOfNat 1030429735123150342315721682818186), (Int.ofNat 136203952861025888707262531819919), (Int.ofNat 21442434137409487920644174254776), (Int.ofNat 858455806800426450817395772836), (Int.negOfNat 659690890381750531779799171491), (Int.negOfNat 61271747740180435993811117663), (Int.ofNat 12097436702487844272230259760), (Int.ofNat 1129950739280558886596149346), (Int.negOfNat 131115266302468468738936353), (Int.negOfNat 11769252084933732127081206), (Int.ofNat 911096614614346440558786), (Int.ofNat 79467625884422422132614), (Int.negOfNat 4374225568594017431195), (Int.negOfNat 374663851084674509244), (Int.ofNat 15564928103860016866), (Int.ofNat 1372487969307989440), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-18152119486705803331135632855074857/22517998136852480000000000000000000), (-515214867561575171157860841409093/11258999068426240000000000000000000), (136203952861025888707262531819919/22517998136852480000000000000000000), (2680304267176185990080521781847/2814749767106560000000000000000000), (214613951700106612704348943209/5629499534213120000000000000000000), (-659690890381750531779799171491/22517998136852480000000000000000000), (-61271747740180435993811117663/22517998136852480000000000000000000), (151217958781098053402878247/281474976710656000000000000000000), (564975369640279443298074673/11258999068426240000000000000000000), (-131115266302468468738936353/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial171.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial171.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial171.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial171 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 19506159173270630250367531887319063), (Int.negOfNat 259147257946118962753255937546208), (Int.ofNat 227425798701835581340059313196841), (Int.ofNat 78659367972544859860354771725), (Int.negOfNat 5402145813971498215813786917867), (Int.negOfNat 198557635066379586113008515563), (Int.ofNat 123961324284383468433753394457), (Int.ofNat 6208937911099660612755307560), (Int.negOfNat 1752480335947566155236099134), (Int.negOfNat 93757602136594533324728207), (Int.ofNat 15251483540822955242210474), (Int.ofNat 835618672293910282185134), (Int.negOfNat 88252499188539406742026), (Int.negOfNat 4877561418718404910965), (Int.ofNat 363891701035317543956), (Int.ofNat 20143578705397597534), (Int.negOfNat 1322204788969643240), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-19506159173270630250367531887319063/22517998136852480000000000000000000), (-8098351810816217586039248048319/703687441776640000000000000000000), (227425798701835581340059313196841/22517998136852480000000000000000000), (3146374718901794394414190869/900719925474099200000000000000000), (-5402145813971498215813786917867/22517998136852480000000000000000000), (-198557635066379586113008515563/22517998136852480000000000000000000), (123961324284383468433753394457/22517998136852480000000000000000000), (155223447777491515318882689/562949953421312000000000000000000), (-876240167973783077618049567/11258999068426240000000000000000000), (-93757602136594533324728207/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial171.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial171.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial171.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial171 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 19198660832821246809042098207808272), (Int.ofNat 487403311032693559488940333550972), (Int.ofNat 112904924208418897005916730982169), (Int.negOfNat 31155987347802994085058495016040), (Int.negOfNat 324620611426189989729763297757), (Int.ofNat 973968512613600665252856163903), (Int.ofNat 9233314561294753472101947185), (Int.negOfNat 18865050015010187539174773458), (Int.negOfNat 409389437409283522510334257), (Int.ofNat 211821200531142424988365713), (Int.ofNat 6250690328011418635278984), (Int.negOfNat 1497147896992623501015789), (Int.negOfNat 50389087844557336312665), (Int.ofNat 7287743424872161832128), (Int.ofNat 261041472630084192064), (Int.negOfNat 26686764216267583219), (Int.negOfNat 1108620166681947200), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-1199916302051327925565131137988017/1407374883553280000000000000000000), (121850827758173389872235083387743/5629499534213120000000000000000000), (112904924208418897005916730982169/22517998136852480000000000000000000), (-778899683695074852126462375401/562949953421312000000000000000000), (-324620611426189989729763297757/22517998136852480000000000000000000), (973968512613600665252856163903/22517998136852480000000000000000000), (1846662912258950694420389437/4503599627370496000000000000000000), (-9432525007505093769587386729/11258999068426240000000000000000000), (-409389437409283522510334257/22517998136852480000000000000000000), (211821200531142424988365713/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial171.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial171.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial171.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial171 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 17997326304383360317163195260339187), (Int.ofNat 626085168766609544142660120260455), (Int.negOfNat 14095605449596016709237529043958), (Int.negOfNat 3446813042130370255141971077788), (Int.ofNat 5099636907202964298913463013487), (Int.negOfNat 252660071747262030039186311716), (Int.negOfNat 160768347629264981640955951407), (Int.ofNat 2773334030465275843560180517), (Int.ofNat 2479709049556513497071948143), (Int.ofNat 9563856978403049094699290), (Int.negOfNat 21942908941556639988513423), (Int.negOfNat 313788437927907302103108), (Int.ofNat 127299399678287656408567), (Int.ofNat 2494624537981738508800), (Int.negOfNat 526776373595166504385), (Int.negOfNat 11727932738941881167), (Int.ofNat 1770880065655491240), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-17997326304383360317163195260339187/22517998136852480000000000000000000), (125217033753321908828532024052091/4503599627370496000000000000000000), (-7047802724798008354618764521979/11258999068426240000000000000000000), (-861703260532592563785492769447/5629499534213120000000000000000000), (5099636907202964298913463013487/22517998136852480000000000000000000), (-63165017936815507509796577929/5629499534213120000000000000000000), (-160768347629264981640955951407/22517998136852480000000000000000000), (2773334030465275843560180517/22517998136852480000000000000000000), (2479709049556513497071948143/22517998136852480000000000000000000), (956385697840304909469929/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial171.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial171.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial171.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial171 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 16764920889275801829799009701072002), (Int.ofNat 644140070539938442541114882321509), (Int.ofNat 34916162273880422443037841895643), (Int.ofNat 7233429598247098150969634804727), (Int.negOfNat 3772378732272788247268289147366), (Int.negOfNat 991789919384491724732427403554), (Int.ofNat 91499857414284669667078321351), (Int.ofNat 24363169076405341178286992243), (Int.negOfNat 706459409892900853134712496), (Int.negOfNat 280751632056633871005671392), (Int.ofNat 1784783205857463676725038), (Int.ofNat 1970887393078633170315061), (Int.ofNat 7997633548607295583932), (Int.negOfNat 9527007133207072182676), (Int.negOfNat 90249918188520713209), (Int.ofNat 34503308568208210819), (Int.ofNat 475262431213263680), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-8382460444637900914899504850536001/11258999068426240000000000000000000), (644140070539938442541114882321509/22517998136852480000000000000000000), (34916162273880422443037841895643/22517998136852480000000000000000000), (7233429598247098150969634804727/22517998136852480000000000000000000), (-1886189366136394123634144573683/11258999068426240000000000000000000), (-495894959692245862366213701777/11258999068426240000000000000000000), (91499857414284669667078321351/22517998136852480000000000000000000), (24363169076405341178286992243/22517998136852480000000000000000000), (-44153713118306303320919531/1407374883553280000000000000000000), (-8773488501769808468927231/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial171.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial171.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial171.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial171 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 15362548303008809415046504891344781), (Int.ofNat 697689993639203348287841618796448), (Int.negOfNat 55716130788330310304787537790762), (Int.negOfNat 37000368274944146738670076566643), (Int.negOfNat 3197055899196163524139503856905), (Int.ofNat 1340579401515023018150714299204), (Int.ofNat 198330008946841669431735754775), (Int.negOfNat 16075001465294172693993497195), (Int.negOfNat 3155140136500301054520451017), (Int.ofNat 98814786833390627178356477), (Int.ofNat 27271583537466701090430458), (Int.negOfNat 344142230098107109775160), (Int.negOfNat 155055245763035311791708), (Int.ofNat 557836434986634865345), (Int.ofNat 634912439376604723851), (Int.ofNat 1152352907121537360), (Int.negOfNat 2008436097185111400), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-15362548303008809415046504891344781/22517998136852480000000000000000000), (21802812301225104633995050587389/703687441776640000000000000000000), (-27858065394165155152393768895381/11258999068426240000000000000000000), (-37000368274944146738670076566643/22517998136852480000000000000000000), (-639411179839232704827900771381/4503599627370496000000000000000000), (335144850378755754537678574801/5629499534213120000000000000000000), (7933200357873666777269430191/900719925474099200000000000000000), (-3215000293058834538798699439/4503599627370496000000000000000000), (-3155140136500301054520451017/22517998136852480000000000000000000), (98814786833390627178356477/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial171.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial171.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial171.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial171 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 14484385139884390340317004120086556), (Int.ofNat 63768226477600909720526970097250), (Int.negOfNat 215308880447609009589770868555580), (Int.ofNat 9041896973544450076021871427270), (Int.ofNat 14805389944989878486501847480770), (Int.ofNat 1350790227076577893379066277596), (Int.negOfNat 235720202882553057831255660668), (Int.negOfNat 31563932021452289526848434020), (Int.ofNat 1989359804049779477397967600), (Int.ofNat 340124060783985001007623879), (Int.negOfNat 10691934401721922136526720), (Int.negOfNat 2288346917459767767072947), (Int.ofNat 39945535796918885672197), (Int.ofNat 10795665631982263068887), (Int.negOfNat 108883646370376459660), (Int.negOfNat 38255838704710695059), (Int.ofNat 158095304255419840), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-3621096284971097585079251030021639/5629499534213120000000000000000000), (255072905910403638882107880389/90071992547409920000000000000000), (-10765444022380450479488543427779/1125899906842624000000000000000000), (904189697354445007602187142727/2251799813685248000000000000000000), (1480538994498987848650184748077/2251799813685248000000000000000000), (337697556769144473344766569399/5629499534213120000000000000000000), (-58930050720638264457813915167/5629499534213120000000000000000000), (-1578196601072614476342421701/1125899906842624000000000000000000), (4973399510124448693494919/56294995342131200000000000000000), (340124060783985001007623879/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial171.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial171.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial171.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial171 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 14884095749234166230103345580485405), (Int.negOfNat 163785989230370904706348963140277), (Int.ofNat 229500232299984724196065614194085), (Int.ofNat 131265653832531969967758074309480), (Int.ofNat 8700082026796156116220020258672), (Int.negOfNat 2698798901682173164927299879467), (Int.negOfNat 291443038167619566521647218236), (Int.ofNat 28987629948608795931983022143), (Int.ofNat 3877072045478667184583851718), (Int.negOfNat 201574365582791974914562246), (Int.negOfNat 30832448872341740968010741), (Int.ofNat 998376311689706155069176), (Int.ofNat 167815163726352910099986), (Int.negOfNat 3729815149967033703630), (Int.negOfNat 671000851910044841300), (Int.ofNat 10584695311250485167), (Int.ofNat 2245992128714731560), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-2976819149846833246020669116097081/4503599627370496000000000000000000), (-163785989230370904706348963140277/22517998136852480000000000000000000), (45900046459996944839213122838817/4503599627370496000000000000000000), (3281641345813299249193951857737/562949953421312000000000000000000), (543755126674759757263751266167/1407374883553280000000000000000000), (-2698798901682173164927299879467/22517998136852480000000000000000000), (-72860759541904891630411804559/5629499534213120000000000000000000), (28987629948608795931983022143/22517998136852480000000000000000000), (1938536022739333592291925859/11258999068426240000000000000000000), (-100787182791395987457281123/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial171.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial171.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial171.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial171 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 13204783315151829046027268311689896), (Int.ofNat 2352293823926399534843970599287805), (Int.ofNat 965227861754181297059629704183934), (Int.ofNat 67966514400686370633749808743795), (Int.negOfNat 24481339345393492951465298590924), (Int.negOfNat 2634566211434721206415150146986), (Int.ofNat 332953528218261309973386097213), (Int.ofNat 41244306281138794624157544204), (Int.negOfNat 2921468608369077690111275597), (Int.negOfNat 382641558562339883295606330), (Int.ofNat 18144542119660171809091075), (Int.ofNat 2395936638009639676000956), (Int.negOfNat 84055922883051354069902), (Int.negOfNat 10874131626904962043298), (Int.ofNat 301168157660644870381), (Int.ofNat 37304177677941911906), (Int.negOfNat 870638383567310080), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-1650597914393978630753408538961237/2814749767106560000000000000000000), (470458764785279906968794119857561/4503599627370496000000000000000000), (482613930877090648529814852091967/11258999068426240000000000000000000), (13593302880137274126749961748759/4503599627370496000000000000000000), (-6120334836348373237866324647731/5629499534213120000000000000000000), (-1317283105717360603207575073493/11258999068426240000000000000000000), (332953528218261309973386097213/22517998136852480000000000000000000), (10311076570284698656039386051/5629499534213120000000000000000000), (-2921468608369077690111275597/22517998136852480000000000000000000), (-38264155856233988329560633/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial171.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial171.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial171.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial171.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial171 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial171 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial171 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 19033371096772053069924235193410869), (Int.negOfNat 3237347693382406775586252139409212), (Int.ofNat 1136144195097513807406012118926262), (Int.negOfNat 60555860793419472032288726553600), (Int.negOfNat 25387749202267932487030034390053), (Int.ofNat 2613474740985370369961929899933), (Int.ofNat 334971384386079204603924282333), (Int.negOfNat 41212959161533846495603378204), (Int.negOfNat 2923937924164446669352684397), (Int.ofNat 382612795513810647688805930), (Int.ofNat 18146444564382571442544275), (Int.negOfNat 2395917890538800292989756), (Int.negOfNat 84055922883051354069902), (Int.ofNat 10874131626904962043298), (Int.ofNat 301168157660644870381), (Int.negOfNat 37304177677941911906), (Int.negOfNat 870638383567310080), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-19033371096772053069924235193410869/22517998136852480000000000000000000), (-809336923345601693896563034852303/5629499534213120000000000000000000), (568072097548756903703006059463131/11258999068426240000000000000000000), (-2365463312242948126261278381/879609302220800000000000000000), (-25387749202267932487030034390053/22517998136852480000000000000000000), (2613474740985370369961929899933/22517998136852480000000000000000000), (334971384386079204603924282333/22517998136852480000000000000000000), (-10303239790383461623900844551/5629499534213120000000000000000000), (-2923937924164446669352684397/22517998136852480000000000000000000), (38261279551381064768880593/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial171.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial171.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial171.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 21754885681962381315352790313256000), (Int.ofNat 21031750349703033360747447235147), (Int.ofNat 421940148649286822347316395989841), (Int.negOfNat 131614076276918286895231782179116), (Int.ofNat 7709750643460818224906137219660), (Int.ofNat 2703406405337948096727835674054), (Int.negOfNat 289275612222697940556478753436), (Int.negOfNat 28998037365703595732206866143), (Int.ofNat 3874443140325595030968239718), (Int.ofNat 201585781553301191255309446), (Int.negOfNat 30830430639427421523267541), (Int.negOfNat 998383341991270923698376), (Int.ofNat 167815163726352910099986), (Int.ofNat 3729815149967033703630), (Int.negOfNat 671000851910044841300), (Int.negOfNat 10584695311250485167), (Int.ofNat 2245992128714731560), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-2719360710245297664419098789157/2814749767106560000000000000000), (21031750349703033360747447235147/22517998136852480000000000000000000), (421940148649286822347316395989841/22517998136852480000000000000000000), (-32903519069229571723807945544779/5629499534213120000000000000000000), (385487532173040911245306860983/1125899906842624000000000000000000), (1351703202668974048363917837027/11258999068426240000000000000000000), (-72318903055674485139119688359/5629499534213120000000000000000000), (-28998037365703595732206866143/22517998136852480000000000000000000), (1937221570162797515484119859/11258999068426240000000000000000000), (100792890776650595627654723/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial171.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial171.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial171.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 20889272408545759729565298430667128), (Int.ofNat 528142954513272523358804032516703), (Int.negOfNat 47850298662958769893245218811876), (Int.negOfNat 16792329411044882325322901707785), (Int.ofNat 13985393401188508965159977566653), (Int.negOfNat 1322186627368468767392128973496), (Int.negOfNat 233978639940826816527263887868), (Int.ofNat 31514976900245536245985766020), (Int.ofNat 1987281402295512157718020000), (Int.negOfNat 340075767213157353820177879), (Int.negOfNat 10690349845260029337978720), (Int.ofNat 2288316452819653769679747), (Int.ofNat 39945535796918885672197), (Int.negOfNat 10795665631982263068887), (Int.negOfNat 108883646370376459660), (Int.ofNat 38255838704710695059), (Int.ofNat 158095304255419840), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-2611159051068219966195662303833391/2814749767106560000000000000000000), (528142954513272523358804032516703/22517998136852480000000000000000000), (-11962574665739692473311304702969/5629499534213120000000000000000000), (-3358465882208976465064580341557/4503599627370496000000000000000000), (13985393401188508965159977566653/22517998136852480000000000000000000), (-165273328421058595924016121687/2814749767106560000000000000000000), (-58494659985206704131815971967/5629499534213120000000000000000000), (1575748845012276812299288301/1125899906842624000000000000000000), (99364070114775607885901/1125899906842624000000000000000), (-340075767213157353820177879/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial171.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial171.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial171.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 19987882283576597237161370116984894), (Int.ofNat 447409162730906329944329845045149), (Int.ofNat 48229819918954929640470943869646), (Int.ofNat 24081900732527889647013900843641), (Int.negOfNat 3642343322097790763338982798052), (Int.negOfNat 1296011269110551640738004714971), (Int.ofNat 199190687871224258926004827495), (Int.ofNat 16001082898741509830706479595), (Int.negOfNat 3156111181418270981927837417), (Int.negOfNat 98742939354413178923096477), (Int.ofNat 27272301023402272424710458), (Int.ofNat 344097704854863575123560), (Int.negOfNat 155055245763035311791708), (Int.negOfNat 557836434986634865345), (Int.ofNat 634912439376604723851), (Int.negOfNat 1152352907121537360), (Int.negOfNat 2008436097185111400), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-9993941141788298618580685058492447/11258999068426240000000000000000000), (447409162730906329944329845045149/22517998136852480000000000000000000), (24114909959477464820235471934823/11258999068426240000000000000000000), (24081900732527889647013900843641/22517998136852480000000000000000000), (-910585830524447690834745699513/5629499534213120000000000000000000), (-1296011269110551640738004714971/22517998136852480000000000000000000), (39838137574244851785200965499/4503599627370496000000000000000000), (3200216579748301966141295919/4503599627370496000000000000000000), (-3156111181418270981927837417/22517998136852480000000000000000000), (-98742939354413178923096477/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial171.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial171.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial171.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 18793273502429964723446920525942976), (Int.ofNat 751168840383557465083703282587235), (Int.ofNat 54385347752510240116504890899315), (Int.negOfNat 21836501803606140472884251036932), (Int.negOfNat 3741831503948597857339627409036), (Int.ofNat 1040191257830431699977048164994), (Int.ofNat 91266917630278807950682128071), (Int.negOfNat 24441838356777605407319587843), (Int.negOfNat 706070566133226063493434496), (Int.ofNat 280827344618458387891538592), (Int.ofNat 1784441600879875784933438), (Int.negOfNat 1970936605189586550719461), (Int.ofNat 7997633548607295583932), (Int.ofNat 9527007133207072182676), (Int.negOfNat 90249918188520713209), (Int.negOfNat 34503308568208210819), (Int.ofNat 475262431213263680), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-293644898475468198803858133217859/351843720888320000000000000000000), (150233768076711493016740656517447/4503599627370496000000000000000000), (10877069550502048023300978179863/4503599627370496000000000000000000), (-5459125450901535118221062759233/5629499534213120000000000000000000), (-935457875987149464334906852259/5629499534213120000000000000000000), (520095628915215849988524082497/11258999068426240000000000000000000), (91266917630278807950682128071/22517998136852480000000000000000000), (-24441838356777605407319587843/22517998136852480000000000000000000), (-5516176297915828621042457/175921860444160000000000000000000), (8775854519326824621610581/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial171.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial171.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial171.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 17271996172886695713885552347422018), (Int.ofNat 676633838053234726463590344622339), (Int.negOfNat 77747343516116798658608267533115), (Int.negOfNat 9056056347981273792632030372696), (Int.ofNat 5578927945139292250664701085146), (Int.ofNat 291980616088211005074834197323), (Int.negOfNat 162010064391416482558881716607), (Int.negOfNat 2835451950306923198826428917), (Int.ofNat 2481338519418549047515760143), (Int.negOfNat 9504932778254995948059290), (Int.negOfNat 21944208869791625422691423), (Int.ofNat 313750942986228536080708), (Int.ofNat 127299399678287656408567), (Int.negOfNat 2494624537981738508800), (Int.negOfNat 526776373595166504385), (Int.ofNat 11727932738941881167), (Int.ofNat 1770880065655491240), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-8635998086443347856942776173711009/11258999068426240000000000000000000), (676633838053234726463590344622339/22517998136852480000000000000000000), (-15549468703223359731721653506623/4503599627370496000000000000000000), (-1132007043497659224079003796587/2814749767106560000000000000000000), (2789463972569646125332350542573/11258999068426240000000000000000000), (291980616088211005074834197323/22517998136852480000000000000000000), (-162010064391416482558881716607/22517998136852480000000000000000000), (-2835451950306923198826428917/22517998136852480000000000000000000), (2481338519418549047515760143/22517998136852480000000000000000000), (-950493277825499594805929/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial171.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial171.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial171.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 16213682656102152003523815612420109), (Int.ofNat 428892826442666095458293009268857), (Int.negOfNat 11451981431969239968390551725781), (Int.ofNat 23830022668746690519413795104965), (Int.ofNat 458023504351897482961802795286), (Int.negOfNat 953929177088203462878006899796), (Int.ofNat 7339176103791725757986582385), (Int.ofNat 18836065096811638155458709458), (Int.negOfNat 406975986433510576177040257), (Int.negOfNat 211795022827290298288746113), (Int.ofNat 6248791864210399277272584), (Int.ofNat 1497133836389493963757389), (Int.negOfNat 50389087844557336312665), (Int.negOfNat 7287743424872161832128), (Int.ofNat 261041472630084192064), (Int.ofNat 26686764216267583219), (Int.negOfNat 1108620166681947200), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-16213682656102152003523815612420109/22517998136852480000000000000000000), (428892826442666095458293009268857/22517998136852480000000000000000000), (-11451981431969239968390551725781/22517998136852480000000000000000000), (4766004533749338103882759020993/4503599627370496000000000000000000), (229011752175948741480901397643/11258999068426240000000000000000000), (-238482294272050865719501724949/5629499534213120000000000000000000), (1467835220758345151597316477/4503599627370496000000000000000000), (9418032548405819077729354729/11258999068426240000000000000000000), (-406975986433510576177040257/22517998136852480000000000000000000), (-211795022827290298288746113/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial171.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial171.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial171.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 15231584802663298118716150332723330), (Int.ofNat 616377817240315036703153893308183), (Int.ofNat 79030062788193820621986176406644), (Int.negOfNat 656755496085483529951419735051), (Int.negOfNat 4538089876939024459405949941725), (Int.ofNat 194550897534735559292285098016), (Int.ofNat 121942740270288974054316426057), (Int.negOfNat 6197418899912878443559796760), (Int.negOfNat 1749950339920029088895119934), (Int.ofNat 93744120751413840066459007), (Int.ofNat 15249510369517110180281674), (Int.negOfNat 835606955124635667803134), (Int.negOfNat 88252499188539406742026), (Int.ofNat 4877561418718404910965), (Int.ofNat 363891701035317543956), (Int.negOfNat 20143578705397597534), (Int.negOfNat 1322204788969643240), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-1523158480266329811871615033272333/2251799813685248000000000000000000), (616377817240315036703153893308183/22517998136852480000000000000000000), (19757515697048455155496544101661/5629499534213120000000000000000000), (-656755496085483529951419735051/22517998136852480000000000000000000), (-181523595077560978376237997669/900719925474099200000000000000000), (6079715547960486227883909313/703687441776640000000000000000000), (121942740270288974054316426057/22517998136852480000000000000000000), (-154935472497821961088994919/562949953421312000000000000000000), (-874975169960014544447559967/11258999068426240000000000000000000), (93744120751413840066459007/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial171.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial171.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial171.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 13747722106964173488792452876974330), (Int.ofNat 814089590267439614479674263940261), (Int.ofNat 4284173488679276759346979202056), (Int.negOfNat 15580443614079246939898450160242), (Int.ofNat 1567307871603268898648958949794), (Int.ofNat 633519456326997927327301925024), (Int.negOfNat 62861202290936687979035094223), (Int.negOfNat 12049199684518706500890162560), (Int.ofNat 1131902980653168655986324146), (Int.ofNat 131066116414501255479513953), (Int.negOfNat 11770760973957770631360406), (Int.negOfNat 911063806540377520289186), (Int.ofNat 79467625884422422132614), (Int.ofNat 4374225568594017431195), (Int.negOfNat 374663851084674509244), (Int.negOfNat 15564928103860016866), (Int.ofNat 1372487969307989440), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-1374772210696417348879245287697433/2251799813685248000000000000000000), (814089590267439614479674263940261/22517998136852480000000000000000000), (535521686084909594918372400257/2814749767106560000000000000000000), (-7790221807039623469949225080121/11258999068426240000000000000000000), (783653935801634449324479474897/11258999068426240000000000000000000), (19797483010218685228978185157/703687441776640000000000000000000), (-62861202290936687979035094223/22517998136852480000000000000000000), (-18826874507060478907640879/35184372088832000000000000000000), (565951490326584327993162073/11258999068426240000000000000000000), (131066116414501255479513953/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial171.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial171.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial171.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 12186922338679502141263469795732077), (Int.ofNat 729021633238350428452849943014031), (Int.negOfNat 21608306279135228829512715582226), (Int.ofNat 8017083143279800902599237196244), (Int.ofNat 2367816346893032035774344249851), (Int.negOfNat 474405567945040444826440644404), (Int.negOfNat 64375365405483693499758200495), (Int.ofNat 11137023251546296205105978782), (Int.ofNat 899201965746854933780277503), (Int.negOfNat 141751443610447532515053327), (Int.negOfNat 7580350244690862683068136), (Int.ofNat 1132849807120114681944211), (Int.ofNat 42423073282114270415735), (Int.negOfNat 6195229171788217382752), (Int.negOfNat 168601610424348393616), (Int.ofNat 24758828228487272301), (Int.ofNat 741595610970774120), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-12186922338679502141263469795732077/22517998136852480000000000000000000), (729021633238350428452849943014031/22517998136852480000000000000000000), (-10804153139567614414756357791113/11258999068426240000000000000000000), (2004270785819950225649809299061/5629499534213120000000000000000000), (2367816346893032035774344249851/22517998136852480000000000000000000), (-118601391986260111206610161101/5629499534213120000000000000000000), (-12875073081096738699951640099/4503599627370496000000000000000000), (5568511625773148102552989391/11258999068426240000000000000000000), (899201965746854933780277503/22517998136852480000000000000000000), (-141751443610447532515053327/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial171.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial171.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial171.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 10731013735392454013727361569064849), (Int.ofNat 769809235703411459470330391141038), (Int.ofNat 38307922044344751530921651908267), (Int.ofNat 4703682289686892456175024333434), (Int.negOfNat 2735853539914448946754923209947), (Int.negOfNat 219796159342848899959611791536), (Int.ofNat 89357754966357134811422595753), (Int.ofNat 4178791519483572074510000637), (Int.negOfNat 1452096102857397436401984577), (Int.negOfNat 43021384597883248893702590), (Int.ofNat 14095245331878199067587857), (Int.ofNat 274089242731824188068172), (Int.negOfNat 90801258719692698248233), (Int.negOfNat 1168397882588260550400), (Int.ofNat 416838619963382574415), (Int.ofNat 3176626551069023953), (Int.negOfNat 1346051182934597120), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-10731013735392454013727361569064849/22517998136852480000000000000000000), (384904617851705729735165195570519/11258999068426240000000000000000000), (38307922044344751530921651908267/22517998136852480000000000000000000), (2351841144843446228087512166717/11258999068426240000000000000000000), (-2735853539914448946754923209947/22517998136852480000000000000000000), (-13737259958928056247475736971/1407374883553280000000000000000000), (89357754966357134811422595753/22517998136852480000000000000000000), (4178791519483572074510000637/22517998136852480000000000000000000), (-1452096102857397436401984577/22517998136852480000000000000000000), (-4302138459788324889370259/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial171.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial171.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial171.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 9045466612942331199432390058414929), (Int.ofNat 891869834244869556486498347421507), (Int.ofNat 4903375782744955386140552364769), (Int.negOfNat 11953247203030036794414585299034), (Int.negOfNat 12589214055932722201287008881), (Int.ofNat 578847726378293453554293053826), (Int.ofNat 2418584071628672625657870111), (Int.negOfNat 12520626411551779187877401677), (Int.negOfNat 16629198836479354648485176), (Int.ofNat 151727107013848505236957768), (Int.negOfNat 230028156015289505597522), (Int.negOfNat 1172171526201989000901259), (Int.ofNat 4333009346669135604012), (Int.ofNat 6265160121339057511164), (Int.negOfNat 33485729454607532889), (Int.negOfNat 24656838196107227901), (Int.negOfNat 108237875502090600), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-9045466612942331199432390058414929/22517998136852480000000000000000000), (891869834244869556486498347421507/22517998136852480000000000000000000), (4903375782744955386140552364769/22517998136852480000000000000000000), (-5976623601515018397207292649517/11258999068426240000000000000000000), (-12589214055932722201287008881/22517998136852480000000000000000000), (289423863189146726777146526913/11258999068426240000000000000000000), (2418584071628672625657870111/22517998136852480000000000000000000), (-12520626411551779187877401677/22517998136852480000000000000000000), (-2078649854559919331060647/2814749767106560000000000000000000), (18965888376731063154619721/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial171.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial171.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial171.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 7320794711129334638625049365016331), (Int.ofNat 809123062048578708205731938638883), (Int.negOfNat 28008869539435772303063331188498), (Int.ofNat 5210464749531384366928228357008), (Int.ofNat 2958505639094369093692488595848), (Int.negOfNat 179545977356124008662559739129), (Int.negOfNat 89326928851280294594369981385), (Int.ofNat 3397499868212728692128328485), (Int.ofNat 1393001735044615349643993943), (Int.negOfNat 40753831842145867075869243), (Int.negOfNat 13173006994626370617229382), (Int.ofNat 329839607758421463316440), (Int.ofNat 83388504743772740526132), (Int.negOfNat 1882533135124957275055), (Int.negOfNat 376563355947347889109), (Int.ofNat 8204195113358327600), (Int.ofNat 1108495151404976960), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-7320794711129334638625049365016331/22517998136852480000000000000000000), (809123062048578708205731938638883/22517998136852480000000000000000000), (-14004434769717886151531665594249/11258999068426240000000000000000000), (325654046845711522933014272313/1407374883553280000000000000000000), (369813204886796136711561074481/2814749767106560000000000000000000), (-179545977356124008662559739129/22517998136852480000000000000000000), (-17865385770256058918873996277/4503599627370496000000000000000000), (679499973642545738425665697/4503599627370496000000000000000000), (1393001735044615349643993943/22517998136852480000000000000000000), (-40753831842145867075869243/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial171.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial171.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial171.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 5736268522589739194378784304287082), (Int.ofNat 825563687551279496014145254121977), (Int.ofNat 42910237063049489742794249295482), (Int.ofNat 11404303628142448308290510133961), (Int.negOfNat 2003018804925316750197126607102), (Int.negOfNat 513167657087516130730472261924), (Int.ofNat 51739864010288664686430072412), (Int.ofNat 10672919585926746562067975820), (Int.negOfNat 755747942860570637386649800), (Int.negOfNat 126448443111485663378650441), (Int.ofNat 7060794913222411876104880), (Int.ofNat 963723729137569504129693), (Int.negOfNat 45337004570703725381243), (Int.negOfNat 5110844097445350789833), (Int.ofNat 209485080777086522180), (Int.ofNat 20174092572916213261), (Int.negOfNat 525119859966592920), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-2868134261294869597189392152143541/11258999068426240000000000000000000), (825563687551279496014145254121977/22517998136852480000000000000000000), (21455118531524744871397124647741/11258999068426240000000000000000000), (11404303628142448308290510133961/22517998136852480000000000000000000), (-1001509402462658375098563303551/11258999068426240000000000000000000), (-128291914271879032682618065481/5629499534213120000000000000000000), (12934966002572166171607518103/5629499534213120000000000000000000), (533645979296337328103398791/1125899906842624000000000000000000), (-3778739714302853186933249/112589990684262400000000000000000), (-126448443111485663378650441/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial171.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial171.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial171.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 3866307183728573618245414572356659), (Int.ofNat 1042602212788187079627757527171948), (Int.ofNat 39967682048989633757272637403933), (Int.negOfNat 12782678588561844140461532144852), (Int.negOfNat 2269909831721057915176182596014), (Int.ofNat 490163893362799543776910363573), (Int.ofNat 65917621292264725324815478204), (Int.negOfNat 9351094938046182252377793977), (Int.negOfNat 1004485851202127446201401202), (Int.ofNat 107010492028927161244899354), (Int.ofNat 9389542098806996790060859), (Int.negOfNat 810333159435321234879704), (Int.negOfNat 59166211612839264918814), (Int.ofNat 4328647070074643204850), (Int.ofNat 267756728803426192540), (Int.negOfNat 17579071410609089073), (Int.negOfNat 870939119875356800), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-3866307183728573618245414572356659/22517998136852480000000000000000000), (260650553197046769906939381792987/5629499534213120000000000000000000), (39967682048989633757272637403933/22517998136852480000000000000000000), (-3195669647140461035115383036213/5629499534213120000000000000000000), (-1134954915860528957588091298007/11258999068426240000000000000000000), (490163893362799543776910363573/22517998136852480000000000000000000), (16479405323066181331203869551/5629499534213120000000000000000000), (-9351094938046182252377793977/22517998136852480000000000000000000), (-502242925601063723100700601/11258999068426240000000000000000000), (53505246014463580622449677/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial171.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial171.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial171.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 1741299590557775834896372375439366), (Int.ofNat 1023379395597065340781375257322985), (Int.negOfNat 43681629997678028541362712173382), (Int.negOfNat 7145183067742202198203457015326), (Int.ofNat 3361197127178268320542929232415), (Int.ofNat 308807620334183864130066006174), (Int.negOfNat 88412176924162994755946979507), (Int.negOfNat 6216774554826074659322581556), (Int.ofNat 1286968098005106743203003203), (Int.ofNat 72628608471799628727232270), (Int.negOfNat 11825575332282633164586365), (Int.negOfNat 552632333759550896491524), (Int.ofNat 74292732897172895838658), (Int.ofNat 2946800075331807954382), (Int.negOfNat 337539274562903496259), (Int.negOfNat 11950768306747352414), (Int.ofNat 1079292251592069720), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-870649795278887917448186187719683/11258999068426240000000000000000000), (204675879119413068156275051464597/4503599627370496000000000000000000), (-21840814998839014270681356086691/11258999068426240000000000000000000), (-3572591533871101099101728507663/11258999068426240000000000000000000), (672239425435653664108585846483/4503599627370496000000000000000000), (154403810167091932065033003087/11258999068426240000000000000000000), (-88412176924162994755946979507/22517998136852480000000000000000000), (-1554193638706518664830645389/5629499534213120000000000000000000), (1286968098005106743203003203/22517998136852480000000000000000000), (7262860847179962872723227/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial171.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial171.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial171.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 131131818639860571510033691571952), (Int.ofNat 876833705198330657034229752477092), (Int.negOfNat 4081497570168121981255106906626), (Int.ofNat 16970034757825809192919446868499), (Int.ofNat 965933794522096979793026200521), (Int.negOfNat 654936328046699298236399066593), (Int.negOfNat 25642533093898541528695723133), (Int.ofNat 12609239285462188082965825804), (Int.ofNat 375672220661003272077583997), (Int.negOfNat 144494112076089662878293130), (Int.negOfNat 3503073282433083320256275), (Int.ofNat 1089813859022338682788956), (Int.ofNat 22497570780170893639902), (Int.negOfNat 5784050356544683643298), (Int.negOfNat 104735009808579521181), (Int.ofNat 22858864485995998306), (Int.ofNat 290329941876487680), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(8195738664991285719377105723247/1407374883553280000000000000000000), (219208426299582664258557438119273/5629499534213120000000000000000000), (-2040748785084060990627553453313/11258999068426240000000000000000000), (16970034757825809192919446868499/22517998136852480000000000000000000), (965933794522096979793026200521/22517998136852480000000000000000000), (-654936328046699298236399066593/22517998136852480000000000000000000), (-25642533093898541528695723133/22517998136852480000000000000000000), (3152309821365547020741456451/5629499534213120000000000000000000), (375672220661003272077583997/22517998136852480000000000000000000), (-14449411207608966287829313/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial171.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial171.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial171.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 1998724235251130473058211017065654), (Int.ofNat 1043435032506529926345026032787731), (Int.ofNat 70843703673334409849015846501191), (Int.ofNat 1347857030396089901995753932584), (Int.negOfNat 3753598205820773309053918145394), (Int.negOfNat 22155554727272411317326952794), (Int.ofNat 100242522092101567450182223436), (Int.ofNat 131248917127957390650460543), (Int.negOfNat 1478334995935067329148713318), (Int.negOfNat 707667764432891597432246), (Int.ofNat 13695329259784532196534741), (Int.ofNat 11750402336541914792776), (Int.negOfNat 86422933373328752525986), (Int.negOfNat 131987112170569758430), (Int.ofNat 392558958546816366100), (Int.ofNat 1299760244197326767), (Int.negOfNat 1343160054218111960), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(999362117625565236529105508532827/11258999068426240000000000000000000), (1043435032506529926345026032787731/22517998136852480000000000000000000), (70843703673334409849015846501191/22517998136852480000000000000000000), (168482128799511237749469241573/2814749767106560000000000000000000), (-1876799102910386654526959072697/11258999068426240000000000000000000), (-11077777363636205658663476397/11258999068426240000000000000000000), (25060630523025391862545555859/5629499534213120000000000000000000), (131248917127957390650460543/22517998136852480000000000000000000), (-739167497967533664574356659/11258999068426240000000000000000000), (-353833882216445798716123/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial171.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial171.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial171.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 4325052626724590838462767242775534), (Int.ofNat 1238954628844467332363356342027997), (Int.ofNat 8718395459883705228189760249207), (Int.negOfNat 15906457213982348287102670727911), (Int.ofNat 591515447545020932765879992259), (Int.ofNat 630434066374915805103246538696), (Int.negOfNat 22625440762357463708051898532), (Int.negOfNat 12452997086877437505541854820), (Int.ofNat 371585422431975014192194000), (Int.ofNat 145711529168260754502208279), (Int.negOfNat 3446859989847530493380080), (Int.negOfNat 1117115094798682326673347), (Int.ofNat 20542104934276641046603), (Int.ofNat 5998438752584369556487), (Int.negOfNat 85483745054736901140), (Int.negOfNat 23810525512764781459), (Int.ofNat 422213137435402560), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(2162526313362295419231383621387767/11258999068426240000000000000000000), (1238954628844467332363356342027997/22517998136852480000000000000000000), (8718395459883705228189760249207/22517998136852480000000000000000000), (-15906457213982348287102670727911/22517998136852480000000000000000000), (591515447545020932765879992259/22517998136852480000000000000000000), (78804258296864475637905817337/2814749767106560000000000000000000), (-5656360190589365927012974633/5629499534213120000000000000000000), (-622649854343871875277092741/1125899906842624000000000000000000), (185792711215987507096097/11258999068426240000000000000000), (145711529168260754502208279/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial171.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial171.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial171.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 6737343977872410741098581508965397), (Int.ofNat 1143077717101263999804984661958146), (Int.negOfNat 34619322160361931201409110424143), (Int.ofNat 4802340890596722341962599546843), (Int.ofNat 2966311381424813100400355777559), (Int.negOfNat 283821648861084122367161391662), (Int.negOfNat 83118425394540006964002565655), (Int.ofNat 6373356173384155737724966805), (Int.ofNat 1274927110933500476716359417), (Int.negOfNat 76461510826364513232322323), (Int.negOfNat 12219463520967817023661658), (Int.ofNat 569368596911301496464040), (Int.ofNat 79248970550847973106508), (Int.negOfNat 2885911908699884243455), (Int.negOfNat 367661309779492608251), (Int.ofNat 10437287974174695760), (Int.ofNat 1105604022688491800), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(6737343977872410741098581508965397/22517998136852480000000000000000000), (571538858550631999902492330979073/11258999068426240000000000000000000), (-34619322160361931201409110424143/22517998136852480000000000000000000), (4802340890596722341962599546843/22517998136852480000000000000000000), (2966311381424813100400355777559/22517998136852480000000000000000000), (-141910824430542061183580695831/11258999068426240000000000000000000), (-16623685078908001392800513131/4503599627370496000000000000000000), (1274671234676831147544993361/4503599627370496000000000000000000), (1274927110933500476716359417/22517998136852480000000000000000000), (-76461510826364513232322323/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial171.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial171.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial171.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 8957591932023711413353010267305650), (Int.ofNat 1122416240192248503220452687391063), (Int.ofNat 28827307234861868316527203612392), (Int.ofNat 9167901792913869728041086889671), (Int.negOfNat 2086376837467450066337743059696), (Int.negOfNat 403812874667542747007077997714), (Int.ofNat 68685219645828129623234035929), (Int.ofNat 8591592225269148099188923043), (Int.negOfNat 1098719279010063249539756704), (Int.negOfNat 107669904417276162567342192), (Int.ofNat 10302717746095487080355762), (Int.ofNat 874592992853023100325461), (Int.negOfNat 63198813378811408377132), (Int.negOfNat 4904838492188451511476), (Int.ofNat 273338227678384301609), (Int.ofNat 20057995376262297219), (Int.negOfNat 1055570872904086080), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(179151838640474228267060205346113/450359962737049600000000000000000), (1122416240192248503220452687391063/22517998136852480000000000000000000), (3603413404357733539565900451549/2814749767106560000000000000000000), (9167901792913869728041086889671/22517998136852480000000000000000000), (-130398552341715629146108941231/1407374883553280000000000000000000), (-201906437333771373503538998857/11258999068426240000000000000000000), (68685219645828129623234035929/22517998136852480000000000000000000), (8591592225269148099188923043/22517998136852480000000000000000000), (-34334977469064476548117397/703687441776640000000000000000000), (-6729369026079760160458887/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial171.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial171.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial171.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 11349944040207290113211030002350440), (Int.ofNat 1264395460054408508569435492130397), (Int.ofNat 21387976871680221824946558243990), (Int.negOfNat 10235565815932392819367775141342), (Int.negOfNat 1096501715209039422799964948319), (Int.ofNat 534065250962439949747672987270), (Int.ofNat 36541918426710125981692677807), (Int.negOfNat 11977556280637910666618379883), (Int.negOfNat 664932827753071986206608943), (Int.ofNat 145754605133764137698368090), (Int.ofNat 7359686255372924514170223), (Int.negOfNat 1100882854414546947956708), (Int.negOfNat 52981136058618867394567), (Int.ofNat 5650026235260899354000), (Int.ofNat 264065668125353221185), (Int.negOfNat 21012867805995039567), (Int.negOfNat 868047991158871640), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(283748601005182252830275750058761/562949953421312000000000000000000), (1264395460054408508569435492130397/22517998136852480000000000000000000), (2138797687168022182494655824399/2251799813685248000000000000000000), (-5117782907966196409683887570671/11258999068426240000000000000000000), (-1096501715209039422799964948319/22517998136852480000000000000000000), (53406525096243994974767298727/2251799813685248000000000000000000), (36541918426710125981692677807/22517998136852480000000000000000000), (-11977556280637910666618379883/22517998136852480000000000000000000), (-664932827753071986206608943/22517998136852480000000000000000000), (14575460513376413769836809/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial171.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial171.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial171.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 13882663475554242416907937790403901), (Int.ofNat 1236087078145352700463115314211302), (Int.negOfNat 23363835688798105624623966807984), (Int.ofNat 1148707189843409182211456611546), (Int.ofNat 2973881085542751088781140940486), (Int.negOfNat 14108247381633313762891562344), (Int.negOfNat 100965614217653277014797655585), (Int.negOfNat 1020550859267035885827828658), (Int.ofNat 1674321454577821896388860657), (Int.ofNat 31308430913601682338029313), (Int.negOfNat 16041027021251986796398984), (Int.negOfNat 380740445108707854362589), (Int.ofNat 99295400267493264857865), (Int.ofNat 2625502176239989294928), (Int.negOfNat 431591286792241232864), (Int.negOfNat 12241451024321669619), (Int.ofNat 1688928608372769600), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(13882663475554242416907937790403901/22517998136852480000000000000000000), (618043539072676350231557657105651/11258999068426240000000000000000000), (-1460239730549881601538997925499/1407374883553280000000000000000000), (574353594921704591105728305773/11258999068426240000000000000000000), (1486940542771375544390570470243/11258999068426240000000000000000000), (-1763530922704164220361445293/2814749767106560000000000000000000), (-20193122843530655402959531117/4503599627370496000000000000000000), (-510275429633517942913914329/11258999068426240000000000000000000), (1674321454577821896388860657/22517998136852480000000000000000000), (31308430913601682338029313/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial171.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial171.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial171.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 16311538021513630224331487124504737), (Int.ofNat 1232311901262680664051723017957026), (Int.ofNat 31811436712139063351502345800241), (Int.ofNat 10567260449456533441109166610664), (Int.negOfNat 1728012362511485906628382811876), (Int.negOfNat 628355957028610165286711691949), (Int.ofNat 39881192448595658105203668503), (Int.ofNat 15471420180960992801719317960), (Int.negOfNat 345499225563652057347640466), (Int.negOfNat 197789836277561628270661807), (Int.ofNat 507235276703349678048726), (Int.ofNat 1513351537556599457879134), (Int.ofNat 10739382013157532890426), (Int.negOfNat 7783315091860576514965), (Int.negOfNat 95160362622915121156), (Int.ofNat 29428513772450755934), (Int.ofNat 419372714473023640), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(16311538021513630224331487124504737/22517998136852480000000000000000000), (616155950631340332025861508978513/11258999068426240000000000000000000), (31811436712139063351502345800241/22517998136852480000000000000000000), (1320907556182066680138645826333/2814749767106560000000000000000000), (-432003090627871476657095702969/5629499534213120000000000000000000), (-628355957028610165286711691949/22517998136852480000000000000000000), (39881192448595658105203668503/22517998136852480000000000000000000), (386785504524024820042982949/562949953421312000000000000000000), (-172749612781826028673820233/11258999068426240000000000000000000), (-197789836277561628270661807/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial171.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial171.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial171.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 18944536686345637465861187549185623), (Int.ofNat 1394598276803448072440717517903368), (Int.ofNat 21959888295151324775999366395639), (Int.negOfNat 14957913778150953754325089321125), (Int.negOfNat 2401912266160311692352461152253), (Int.ofNat 643644941646797371148380482763), (Int.ofNat 107876554980038831220519957023), (Int.negOfNat 10636386595189547328088114240), (Int.negOfNat 2046178218777437181620595346), (Int.ofNat 78500993787029402573880047), (Int.ofNat 20114772466509395284161206), (Int.negOfNat 305033553538626120003214), (Int.negOfNat 124464413963600521367414), (Int.ofNat 517401812702113535205), (Int.ofNat 538021937080919048044), (Int.ofNat 1119614911914103266), (Int.negOfNat 1952796410998811840), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(18944536686345637465861187549185623/22517998136852480000000000000000000), (174324784600431009055089689737921/2814749767106560000000000000000000), (21959888295151324775999366395639/22517998136852480000000000000000000), (-119663310225207630034600714569/180143985094819840000000000000000), (-2401912266160311692352461152253/22517998136852480000000000000000000), (643644941646797371148380482763/22517998136852480000000000000000000), (107876554980038831220519957023/22517998136852480000000000000000000), (-33238708109967335400275357/70368744177664000000000000000000), (-1023089109388718590810297673/11258999068426240000000000000000000), (78500993787029402573880047/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial171.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial171.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial171.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 21689154013682750554578206570875232), (Int.ofNat 1291702626115713557300442672475468), (Int.negOfNat 58289189433748987073641941575369), (Int.negOfNat 85666486538391849311614291720), (Int.ofNat 5796155775344363492127199683757), (Int.ofNat 427556123643795289315425674497), (Int.negOfNat 161220228267417919901346363105), (Int.negOfNat 17240842500945755962899698382), (Int.ofNat 1719131202956067475822176897), (Int.ofNat 232890857971617006252358527), (Int.negOfNat 10412524080094183004110264), (Int.negOfNat 1773355702502128084933411), (Int.ofNat 41227179930677492522265), (Int.ofNat 9024751347521473041552), (Int.negOfNat 112712382400327283184), (Int.negOfNat 34043763295540430701), (Int.ofNat 161236463525845480), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(677786062927585954830568955339851/703687441776640000000000000000000), (322925656528928389325110668118867/5629499534213120000000000000000000), (-58289189433748987073641941575369/22517998136852480000000000000000000), (-2141662163459796232790357293/562949953421312000000000000000000), (5796155775344363492127199683757/22517998136852480000000000000000000), (427556123643795289315425674497/22517998136852480000000000000000000), (-32244045653483583980269272621/4503599627370496000000000000000000), (-8620421250472877981449849191/11258999068426240000000000000000000), (1719131202956067475822176897/22517998136852480000000000000000000), (232890857971617006252358527/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial171.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial171.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial171.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 24133157825506885528406420760420227), (Int.ofNat 1240746320324182480969856477351985), (Int.ofNat 68218450935817431791410933091158), (Int.ofNat 32040719401413814063306604799548), (Int.negOfNat 1771019266143359649626809807167), (Int.negOfNat 1845102163015232138353063274124), (Int.negOfNat 110498774715656027682290834553), (Int.ofNat 26376276672364930880534634163), (Int.ofNat 2346755353635874134587278577), (Int.negOfNat 206795698079029442628831010), (Int.negOfNat 22588806705753491900207057), (Int.ofNat 1072043886976459387281428), (Int.ofNat 136456616477752116089433), (Int.negOfNat 4016491695581984621200), (Int.negOfNat 582262462386579101615), (Int.ofNat 11268686640876889647), (Int.ofNat 1926359624625419520), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(24133157825506885528406420760420227/22517998136852480000000000000000000), (248149264064836496193971295470397/4503599627370496000000000000000000), (34109225467908715895705466545579/11258999068426240000000000000000000), (8010179850353453515826651199887/5629499534213120000000000000000000), (-1771019266143359649626809807167/22517998136852480000000000000000000), (-461275540753808034588265818531/5629499534213120000000000000000000), (-110498774715656027682290834553/22517998136852480000000000000000000), (26376276672364930880534634163/22517998136852480000000000000000000), (2346755353635874134587278577/22517998136852480000000000000000000), (-20679569807902944262883101/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial171.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial171.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial171.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 27053249161039337627905492455408882), (Int.ofNat 1686254892307062151172545639891131), (Int.ofNat 64586097985565371548909200703237), (Int.negOfNat 56034848959154099454954874345887), (Int.negOfNat 17915083873721833842558336067394), (Int.negOfNat 459526779508746168270313034446), (Int.ofNat 329373658253468349865991406369), (Int.ofNat 20911730885004966292575398077), (Int.negOfNat 3207827725593845959450384024), (Int.negOfNat 259629941697630283647306168), (Int.ofNat 20461115262769177120033522), (Int.ofNat 1873405305082623948964859), (Int.negOfNat 93749560494577673142012), (Int.negOfNat 9234718955945607547964), (Int.ofNat 325990486045399569289), (Int.ofNat 33941773263160386301), (Int.negOfNat 794594198994529000), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(13526624580519668813952746227704441/11258999068426240000000000000000000), (1686254892307062151172545639891131/22517998136852480000000000000000000), (64586097985565371548909200703237/22517998136852480000000000000000000), (-56034848959154099454954874345887/22517998136852480000000000000000000), (-8957541936860916921279168033697/11258999068426240000000000000000000), (-229763389754373084135156517223/11258999068426240000000000000000000), (329373658253468349865991406369/22517998136852480000000000000000000), (20911730885004966292575398077/22517998136852480000000000000000000), (-400978465699230744931298003/2814749767106560000000000000000000), (-32453742712203785455913271/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial171.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial171.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial171.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 29957305163892928271350070919972501), (Int.ofNat 730984577570686417903879023260872), (Int.negOfNat 651908787801863529877594591334838), (Int.negOfNat 160089982984008143912232259105557), (Int.negOfNat 1192953505834240555226310242255), (Int.ofNat 3497293561478213491158888039316), (Int.ofNat 177590309175598451424591731385), (Int.negOfNat 41464641177795444229954461285), (Int.negOfNat 2761809234959022662601613543), (Int.ofNat 320898543362124586866578843), (Int.ofNat 23580627273821882000805382), (Int.negOfNat 1763566327048025272793240), (Int.negOfNat 134173633351423917002532), (Int.ofNat 7256523986911125746255), (Int.ofNat 553266280305794188709), (Int.negOfNat 22649508305304241200), (Int.negOfNat 1688803593095799360), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(29957305163892928271350070919972501/22517998136852480000000000000000000), (91373072196335802237984877907609/2814749767106560000000000000000000), (-325954393900931764938797295667419/11258999068426240000000000000000000), (-160089982984008143912232259105557/22517998136852480000000000000000000), (-238590701166848111045262048451/4503599627370496000000000000000000), (874323390369553372789722009829/5629499534213120000000000000000000), (35518061835119690284918346277/4503599627370496000000000000000000), (-8292928235559088845990892257/4503599627370496000000000000000000), (-2761809234959022662601613543/22517998136852480000000000000000000), (320898543362124586866578843/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial171.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial171.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial171.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 27629281077284318712266623701767676), (Int.negOfNat 3542590945156585150149402595203650), (Int.negOfNat 1349794850151502015813543466874020), (Int.negOfNat 27496550604715648857848276843590), (Int.ofNat 31254512761647089564721375274910), (Int.ofNat 1682268033878937959283516230884), (Int.negOfNat 449422461081884428232002379612), (Int.negOfNat 28525978243567138839565618620), (Int.ofNat 4249543836802192519699694200), (Int.ofNat 277317497333632681504270441), (Int.negOfNat 28108688129948375681969280), (Int.negOfNat 1796884800146754982399293), (Int.ofNat 136643921662052924072843), (Int.ofNat 8369157384370988407833), (Int.negOfNat 506530261495177390980), (Int.negOfNat 29459027639969371661), (Int.ofNat 1427951934463212520), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(6907320269321079678066655925441919/5629499534213120000000000000000000), (-70851818903131703002988051904073/450359962737049600000000000000000), (-67489742507575100790677173343701/1125899906842624000000000000000000), (-2749655060471564885784827684359/2251799813685248000000000000000000), (3125451276164708956472137527491/2251799813685248000000000000000000), (420567008469734489820879057721/5629499534213120000000000000000000), (-112355615270471107058000594903/5629499534213120000000000000000000), (-1426298912178356941978280931/1125899906842624000000000000000000), (21247719184010962598498471/112589990684262400000000000000000), (277317497333632681504270441/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial171.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial171.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial171.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 15447635825642353391632415276079845), (Int.negOfNat 8231241797527244129433259313106283), (Int.negOfNat 748586242507349813253615260533085), (Int.ofNat 210563940714306239487218592966920), (Int.ofNat 18568313964830499581735875621408), (Int.negOfNat 3907899538018625403232335100653), (Int.negOfNat 298022348095410566178170062604), (Int.ofNat 47049757679053037592022335577), (Int.ofNat 3120776751093720170383637602), (Int.negOfNat 383258652291293410525538954), (Int.negOfNat 22449455316576382740028059), (Int.ofNat 2228837165271378928594104), (Int.ofNat 116658349320562240748014), (Int.negOfNat 9662157508335530492450), (Int.negOfNat 456998148489579039740), (Int.ofNat 32024384602555002673), (Int.ofNat 1451247561566179200), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(3089527165128470678326483055215969/4503599627370496000000000000000000), (-8231241797527244129433259313106283/22517998136852480000000000000000000), (-149717248501469962650723052106617/4503599627370496000000000000000000), (5264098517857655987180464824173/562949953421312000000000000000000), (580259811400953111929246113169/703687441776640000000000000000000), (-3907899538018625403232335100653/22517998136852480000000000000000000), (-74505587023852641544542515651/5629499534213120000000000000000000), (47049757679053037592022335577/22517998136852480000000000000000000), (1560388375546860085191818801/11258999068426240000000000000000000), (-191629326145646705262769477/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial171.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial171.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial171.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 2165107377612201395258602700343184), (Int.negOfNat 8451182273877256533044268118409365), (Int.ofNat 611533770835123550874264368686146), (Int.ofNat 184750151647892722345225289830805), (Int.negOfNat 23464816563706861454765617980716), (Int.negOfNat 3013374951482091231335436524174), (Int.ofNat 414689893173236848180348848627), (Int.ofNat 33764221671322569081110505956), (Int.negOfNat 4408394085768469718076822403), (Int.negOfNat 264564110856637267558893470), (Int.ofNat 31543695793136818674446365), (Int.ofNat 1507589023514919391411524), (Int.negOfNat 162224453638529053981458), (Int.negOfNat 6468804421631085271982), (Int.ofNat 628563822338405225459), (Int.ofNat 21235703373800510814), (Int.negOfNat 1982124326088689320), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-135319211100762587203662668771449/1407374883553280000000000000000000), (-1690236454775451306608853623681873/4503599627370496000000000000000000), (305766885417561775437132184343073/11258999068426240000000000000000000), (36950030329578544469045057966161/4503599627370496000000000000000000), (-5866204140926715363691404495179/5629499534213120000000000000000000), (-1506687475741045615667718262087/11258999068426240000000000000000000), (414689893173236848180348848627/22517998136852480000000000000000000), (8441055417830642270277626489/5629499534213120000000000000000000), (-4408394085768469718076822403/22517998136852480000000000000000000), (-26456411085663726755889347/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial171.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial171.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial171.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial171.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial171.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial171.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial171.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial171.reflect := by
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

end Bin171
end
end ErdosOverlap.OuterNumerics
