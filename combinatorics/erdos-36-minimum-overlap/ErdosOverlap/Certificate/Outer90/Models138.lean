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

/-! # Exact integer weighted outer models for source bin 138

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin138

def weightDenominator : ℤ := (Int.ofNat 1000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 333760071480232730)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 308285542437204130)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 220449734600088570)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 118342389877093270)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 56139763840869016)⟩, ⟨(19494472361809/1000000000000), (Int.negOfNat 59110695574798000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 78814995434363520)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 19322807244228550)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 44900564109546445)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 9972758210975110)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial138.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial138.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 976499047449889000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 168315129387756330)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 162193027803646280)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 58576052061822860)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 9976527680746103)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 10633266679490765)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 6693348369873021)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 2367737170226838)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 2138009525109870)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial138.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial138.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 976499047449889000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 168315129387756330)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 162193027803646280)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 58576052061822860)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 9976527680746103)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 10633266679490765)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 6693348369873021)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 2367737170226838)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 2138009525109870)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial138.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial138.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial138.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 1054167670265905322798412688167418), (Int.ofNat 463210509378881014591673637299727), (Int.ofNat 98924049970854179125735370268104), (Int.negOfNat 15044737070391574371320384051186), (Int.negOfNat 2690108868903375636330842659286), (Int.ofNat 303983177970145189611320881860), (Int.ofNat 39368877345781196089904640676), (Int.negOfNat 3687373245972805278494956597), (Int.negOfNat 355917773344334121677997947), (Int.ofNat 29200074254014761258535489), (Int.ofNat 2177079120110454419877449), (Int.negOfNat 162580665154685011492791), (Int.negOfNat 9637974705220266758488), (Int.ofNat 672487057564985175776), (Int.ofNat 32367616297546640405), (Int.negOfNat 2120957417710759300), (Int.negOfNat 84304035183989613), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-527083835132952661399206344083709/562949953421312000000000000000000), (463210509378881014591673637299727/1125899906842624000000000000000000), (12365506246356772390716921283513/140737488355328000000000000000000), (-7522368535195787185660192025593/562949953421312000000000000000000), (-1345054434451687818165421329643/562949953421312000000000000000000), (15199158898507259480566044093/56294995342131200000000000000000), (9842219336445299022476160169/281474976710656000000000000000000), (-3687373245972805278494956597/1125899906842624000000000000000000), (-355917773344334121677997947/1125899906842624000000000000000000), (29200074254014761258535489/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial138.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial138.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial138.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial138 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 116250694319449949691539738543352), (Int.ofNat 622223850694837029090019125472483), (Int.negOfNat 25100998196719150445141636303060), (Int.negOfNat 20627310886222387350852170586152), (Int.ofNat 1419941957325471629096266731360), (Int.ofNat 378105856870460903241386320911), (Int.negOfNat 27986657549917992347278372689), (Int.negOfNat 4105761116616391840073525197), (Int.ofNat 302569525749630202330549537), (Int.ofNat 29005399261434646214422361), (Int.negOfNat 2121532619844486564630289), (Int.negOfNat 143757558324349717777910), (Int.ofNat 10543357785392103619195), (Int.ofNat 529232446568086683784), (Int.negOfNat 39302629769760877555), (Int.negOfNat 1469905825173836259), (Int.ofNat 120894172516584857), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(14531336789931243711442467317919/140737488355328000000000000000000), (622223850694837029090019125472483/1125899906842624000000000000000000), (-1255049909835957522257081815153/56294995342131200000000000000000), (-2578413860777798418856521323269/140737488355328000000000000000000), (8874637233284197681851667071/7036874417766400000000000000000), (378105856870460903241386320911/1125899906842624000000000000000000), (-27986657549917992347278372689/1125899906842624000000000000000000), (-4105761116616391840073525197/1125899906842624000000000000000000), (302569525749630202330549537/1125899906842624000000000000000000), (29005399261434646214422361/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial138.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial138.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial138.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial138 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 1127867579597235336463019284934050), (Int.ofNat 343130379809994473512272058362954), (Int.negOfNat 93365502669846909242168571963807), (Int.negOfNat 259842775839874060928812577860), (Int.ofNat 2794916096098653804126641104534), (Int.negOfNat 128751205170642785436343618551), (Int.negOfNat 40634887931116721922302935540), (Int.ofNat 2422725978664087612470154459), (Int.ofNat 349943007413719338355763135), (Int.negOfNat 23259953059991066336298094), (Int.negOfNat 2000249618526081927048334), (Int.ofNat 144548630834106733468161), (Int.ofNat 8172390376602652426347), (Int.negOfNat 641287141890092312138), (Int.negOfNat 25097656314988203438), (Int.ofNat 2147773976537389389), (Int.ofNat 52247751025954413), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(22557351591944706729260385698681/22517998136852480000000000000000), (171565189904997236756136029181477/562949953421312000000000000000000), (-93365502669846909242168571963807/1125899906842624000000000000000000), (-12992138791993703046440628893/56294995342131200000000000000000), (1397458048049326902063320552267/562949953421312000000000000000000), (-128751205170642785436343618551/1125899906842624000000000000000000), (-2031744396555836096115146777/56294995342131200000000000000000), (2422725978664087612470154459/1125899906842624000000000000000000), (69988601482743867671152627/225179981368524800000000000000000), (-11629976529995533168149047/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial138.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial138.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial138.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial138 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 1476971633377697422444267347011006), (Int.ofNat 39267259233074701383366884693215), (Int.negOfNat 45769584601074601510224776700681), (Int.ofNat 12282734738942729744831781370817), (Int.ofNat 25829884406174353601643110517), (Int.negOfNat 314236041373892823078527901525), (Int.ofNat 12591326158609000063107670705), (Int.ofNat 3644783952969126389396768709), (Int.negOfNat 202598124166300882170315792), (Int.negOfNat 25287637698056059980885674), (Int.ofNat 1690166945924241205355074), (Int.ofNat 118080016744905539423990), (Int.negOfNat 9244818367065119541465), (Int.negOfNat 397272307569716148587), (Int.ofNat 36518401157353837924), (Int.ofNat 932504423378559688), (Int.negOfNat 114480143941255247), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(738485816688848711222133673505503/562949953421312000000000000000000), (7853451846614940276673376938643/225179981368524800000000000000000), (-45769584601074601510224776700681/1125899906842624000000000000000000), (12282734738942729744831781370817/1125899906842624000000000000000000), (25829884406174353601643110517/1125899906842624000000000000000000), (-12569441654955712923141116061/45035996273704960000000000000000), (2518265231721800012621534141/225179981368524800000000000000000), (3644783952969126389396768709/1125899906842624000000000000000000), (-12662382760393805135644737/70368744177664000000000000000000), (-12643818849028029990442837/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial138.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial138.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial138.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial138 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 1462256913068463167184066271711959), (Int.negOfNat 16936174948929188312881711308499), (Int.ofNat 8421611409674484848895262567362), (Int.ofNat 3506440725777437562453810243146), (Int.negOfNat 1642955118365902660829714755565), (Int.ofNat 17370184660822189536014391862), (Int.ofNat 30754421638101616722849732104), (Int.negOfNat 1253087187252900682409036822), (Int.negOfNat 279790973735154482518858594), (Int.ofNat 16171685382439105183540460), (Int.ofNat 1561340336747441924507175), (Int.negOfNat 115329402768148762424544), (Int.negOfNat 5903143313426388349245), (Int.ofNat 551790184028196832082), (Int.ofNat 15877879522239264465), (Int.negOfNat 1988323469607959629), (Int.negOfNat 22329476393029083), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(1462256913068463167184066271711959/1125899906842624000000000000000000), (-16936174948929188312881711308499/1125899906842624000000000000000000), (4210805704837242424447631283681/562949953421312000000000000000000), (1753220362888718781226905121573/562949953421312000000000000000000), (-328591023673180532165942951113/225179981368524800000000000000000), (8685092330411094768007195931/562949953421312000000000000000000), (3844302704762702090356216513/140737488355328000000000000000000), (-626543593626450341204518411/562949953421312000000000000000000), (-139895486867577241259429297/562949953421312000000000000000000), (808584269121955259177023/56294995342131200000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial138.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial138.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial138.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial138 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 1466136983022285954038806857889141), (Int.ofNat 12743410511106637059434238150566), (Int.negOfNat 2454499647804676586154639395604), (Int.negOfNat 5119245176046263572216337901982), (Int.negOfNat 207436471682286293781709683192), (Int.ofNat 197193802840494216343946582047), (Int.negOfNat 3937705691057146844129032190), (Int.negOfNat 2596369672375426432824350414), (Int.ofNat 117500780610855731514668626), (Int.ofNat 18334539557695934471072054), (Int.negOfNat 1206063538294511888563033), (Int.negOfNat 81024377519610838291193), (Int.ofNat 7303939183024311633953), (Int.ofNat 237675748857203464615), (Int.negOfNat 30488038752846312897), (Int.negOfNat 437240502907758847), (Int.ofNat 108066115365925637), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(1466136983022285954038806857889141/1125899906842624000000000000000000), (6371705255553318529717119075283/562949953421312000000000000000000), (-613624911951169146538659848901/281474976710656000000000000000000), (-2559622588023131786108168950991/562949953421312000000000000000000), (-25929558960285786722713710399/140737488355328000000000000000000), (197193802840494216343946582047/1125899906842624000000000000000000), (-393770569105714684412903219/112589990684262400000000000000000), (-1298184836187713216412175207/562949953421312000000000000000000), (58750390305427865757334313/562949953421312000000000000000000), (9167269778847967235536027/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial138.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial138.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial138.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial138 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 1443296811600136369367177409259119), (Int.negOfNat 51131541687644187423369371749150), (Int.negOfNat 24783360083487206259255782304909), (Int.negOfNat 686935279523887233913079200226), (Int.ofNat 988130259257297960334433946739), (Int.ofNat 10114615503814319497247131741), (Int.negOfNat 19595899988785972927256668660), (Int.ofNat 535819229102227196301616353), (Int.ofNat 185192883757088137559155248), (Int.negOfNat 9999638880932424804215814), (Int.negOfNat 1001083958696703481597449), (Int.ofNat 82449644471358316366375), (Int.ofNat 3322110830392149591377), (Int.negOfNat 424101867976320753025), (Int.negOfNat 6288385517682610206), (Int.ofNat 1555260314690220859), (Int.negOfNat 7588798239896247), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(1443296811600136369367177409259119/1125899906842624000000000000000000), (-1022630833752883748467387434983/22517998136852480000000000000000), (-24783360083487206259255782304909/1125899906842624000000000000000000), (-343467639761943616956539600113/562949953421312000000000000000000), (988130259257297960334433946739/1125899906842624000000000000000000), (10114615503814319497247131741/1125899906842624000000000000000000), (-979794999439298646362833433/56294995342131200000000000000000), (535819229102227196301616353/1125899906842624000000000000000000), (11574555234818008597447203/70368744177664000000000000000000), (-4999819440466212402107907/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial138.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial138.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial138.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial138 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 1251394448151208714801484985373890), (Int.negOfNat 129438773399295291295913969475389), (Int.negOfNat 8446889427805050758919800264193), (Int.ofNat 5053867937343940926958010093947), (Int.ofNat 220940898295544702906019006533), (Int.negOfNat 122659853399240899156508847703), (Int.negOfNat 114973446966154132233224484), (Int.ofNat 1570568645857144042983546313), (Int.negOfNat 57304153861838147895760593), (Int.negOfNat 10819790543148202256158676), (Int.ofNat 757719596065797867321306), (Int.ofNat 42351909638854648579573), (Int.negOfNat 5081569687513076587457), (Int.negOfNat 83066566008099101874), (Int.ofNat 22181011762292345233), (Int.negOfNat 72887287717814554), (Int.negOfNat 91679328579620917), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(125139444815120871480148498537389/112589990684262400000000000000000), (-129438773399295291295913969475389/1125899906842624000000000000000000), (-8446889427805050758919800264193/1125899906842624000000000000000000), (5053867937343940926958010093947/1125899906842624000000000000000000), (220940898295544702906019006533/1125899906842624000000000000000000), (-122659853399240899156508847703/1125899906842624000000000000000000), (-28743361741538533058306121/281474976710656000000000000000000), (1570568645857144042983546313/1125899906842624000000000000000000), (-57304153861838147895760593/1125899906842624000000000000000000), (-2704947635787050564039669/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial138.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial138.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial138.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial138 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 998944532599480866142079365810672), (Int.negOfNat 104720434015238747206102863645976), (Int.ofNat 18250966326157797608586458517801), (Int.ofNat 2628114437986127501059527961255), (Int.negOfNat 669282332867238811298679307614), (Int.negOfNat 32754653051576706668651343426), (Int.ofNat 11053796294461087297974312714), (Int.negOfNat 81908427732418994347638185), (Int.negOfNat 99405889437651487829057271), (Int.ofNat 5076223687624849180718102), (Int.ofNat 477915623929465662923422), (Int.negOfNat 50217575647830492884343), (Int.negOfNat 1007192703034130742201), (Int.ofNat 277238666681957906342), (Int.negOfNat 1710248251296206217), (Int.negOfNat 1096194386253641400), (Int.ofNat 23258295611626727), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(62434033287467554133879960363167/70368744177664000000000000000000), (-13090054251904843400762857955747/140737488355328000000000000000000), (18250966326157797608586458517801/1125899906842624000000000000000000), (525622887597225500211905592251/225179981368524800000000000000000), (-334641166433619405649339653807/562949953421312000000000000000000), (-16377326525788353334325671713/562949953421312000000000000000000), (5526898147230543648987156357/562949953421312000000000000000000), (-16381685546483798869527637/225179981368524800000000000000000), (-99405889437651487829057271/1125899906842624000000000000000000), (2538111843812424590359051/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial138.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial138.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial138.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial138 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 872450273581687962008364145551100), (Int.negOfNat 22219193603274656419927687654553), (Int.ofNat 17783695443599530099860844231791), (Int.negOfNat 2459253000698738802704728011536), (Int.negOfNat 443131322706020467337590325981), (Int.ofNat 61064025637238892151878037833), (Int.ofNat 3045801735097997554500961498), (Int.negOfNat 745151314955445813414357781), (Int.ofNat 14057433896418123985802550), (Int.ofNat 4588231954146845217304458), (Int.negOfNat 369252437278827870029933), (Int.negOfNat 10860927354078738194715), (Int.ofNat 2833668735861916321453), (Int.negOfNat 36091945774275971873), (Int.negOfNat 12978171948848053366), (Int.ofNat 409811020165700165), (Int.ofNat 67457793107450957), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(8724502735816879620083641455511/11258999068426240000000000000000), (-22219193603274656419927687654553/1125899906842624000000000000000000), (17783695443599530099860844231791/1125899906842624000000000000000000), (-153703312543671175169045500721/70368744177664000000000000000000), (-443131322706020467337590325981/1125899906842624000000000000000000), (61064025637238892151878037833/1125899906842624000000000000000000), (1522900867548998777250480749/562949953421312000000000000000000), (-745151314955445813414357781/1125899906842624000000000000000000), (281148677928362479716051/22517998136852480000000000000000), (2294115977073422608652229/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial138.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial138.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial138.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial138 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 874441702378397170701096727139109), (Int.ofNat 10383457570197327343464075859191), (Int.negOfNat 2449646329434121763254475625776), (Int.negOfNat 3447672383112982656471046788122), (Int.ofNat 170771186824442948587734448883), (Int.ofNat 47533375261903811348152219761), (Int.negOfNat 3978870303916600568468417778), (Int.negOfNat 208344578577210080681638014), (Int.ofNat 34745174986346538181592154), (Int.negOfNat 1267603867754704897339490), (Int.negOfNat 96080381494910301425269), (Int.ofNat 20959155788020472619013), (Int.negOfNat 586729603358960513833), (Int.negOfNat 128379376014456754263), (Int.ofNat 6854231683756157553), (Int.ofNat 473230008868091991), (Int.negOfNat 26817025247272227), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(874441702378397170701096727139109/1125899906842624000000000000000000), (10383457570197327343464075859191/1125899906842624000000000000000000), (-153102895589632610203404726611/70368744177664000000000000000000), (-1723836191556491328235523394061/562949953421312000000000000000000), (170771186824442948587734448883/1125899906842624000000000000000000), (47533375261903811348152219761/1125899906842624000000000000000000), (-1989435151958300284234208889/562949953421312000000000000000000), (-104172289288605040340819007/562949953421312000000000000000000), (17372587493173269090796077/562949953421312000000000000000000), (-126760386775470489733949/112589990684262400000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial138.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial138.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial138.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial138 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 861808931287825014165880093920255), (Int.negOfNat 32344747538059106240492394747532), (Int.negOfNat 16273590233564934925245873412270), (Int.negOfNat 878699730620066014164243193697), (Int.ofNat 382320567475017941034933777273), (Int.negOfNat 4952366739285848227582797666), (Int.negOfNat 3925748829780188425152794024), (Int.ofNat 158079334846082512256352890), (Int.ofNat 13954341564008259844217084), (Int.negOfNat 541368824599993369867414), (Int.ofNat 53223661218126800873219), (Int.negOfNat 7931209011672363281696), (Int.negOfNat 766375706375857033361), (Int.ofNat 98754145964205243796), (Int.ofNat 3831298293895910145), (Int.negOfNat 609750415328223385), (Int.negOfNat 37539518474525627), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(172361786257565002833176018784051/225179981368524800000000000000000), (-8086186884514776560123098686883/281474976710656000000000000000000), (-1627359023356493492524587341227/112589990684262400000000000000000), (-878699730620066014164243193697/1125899906842624000000000000000000), (382320567475017941034933777273/1125899906842624000000000000000000), (-2476183369642924113791398833/562949953421312000000000000000000), (-490718603722523553144099253/140737488355328000000000000000000), (15807933484608251225635289/112589990684262400000000000000000), (3488585391002064961054271/281474976710656000000000000000000), (-270684412299996684933707/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial138.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial138.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial138.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial138 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 730726448109475478535031110167849), (Int.negOfNat 96815148825531174683177438847571), (Int.negOfNat 13579368468521163054751988038204), (Int.ofNat 1464697440705255222784091060228), (Int.ofNat 155281938488598668371575921721), (Int.negOfNat 33470838994272198474533048452), (Int.negOfNat 474126898518548484639451337), (Int.ofNat 304768681143970392777530509), (Int.ofNat 1580637326303922801030760), (Int.negOfNat 1379386154063647913850530), (Int.negOfNat 91142360784796068005820), (Int.ofNat 3350366080870846870190), (Int.ofNat 1210528426680199188271), (Int.negOfNat 6333687527273206885), (Int.negOfNat 8101063146493898756), (Int.ofNat 68672924602518608), (Int.ofNat 20402996671942617), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(730726448109475478535031110167849/1125899906842624000000000000000000), (-96815148825531174683177438847571/1125899906842624000000000000000000), (-3394842117130290763687997009551/281474976710656000000000000000000), (366174360176313805696022765057/281474976710656000000000000000000), (155281938488598668371575921721/1125899906842624000000000000000000), (-8367709748568049618633262113/281474976710656000000000000000000), (-474126898518548484639451337/1125899906842624000000000000000000), (304768681143970392777530509/1125899906842624000000000000000000), (39515933157598070025769/28147497671065600000000000000000), (-137938615406364791385053/112589990684262400000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial138.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial138.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial138.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial138 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 495917983252377374035088725192351), (Int.negOfNat 131221354437984368807172375005719), (Int.negOfNat 3655471797362322400815892608978), (Int.ofNat 1457216666479907693429263316262), (Int.negOfNat 127270584701518035831937625132), (Int.negOfNat 16155746783035315703128877641), (Int.ofNat 2850296827515658394174019468), (Int.ofNat 88273099017361737991112163), (Int.negOfNat 27335139652574073600631233), (Int.negOfNat 870720136458974578617342), (Int.ofNat 176759101620798932841272), (Int.ofNat 11779826994228561605669), (Int.negOfNat 930775363108192991227), (Int.negOfNat 96760184599262587840), (Int.ofNat 4175790621235727792), (Int.ofNat 507060043315657215), (Int.ofNat 7621243841600297), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(495917983252377374035088725192351/1125899906842624000000000000000000), (-131221354437984368807172375005719/1125899906842624000000000000000000), (-1827735898681161200407946304489/562949953421312000000000000000000), (728608333239953846714631658131/562949953421312000000000000000000), (-31817646175379508957984406283/281474976710656000000000000000000), (-16155746783035315703128877641/1125899906842624000000000000000000), (712574206878914598543504867/281474976710656000000000000000000), (88273099017361737991112163/1125899906842624000000000000000000), (-27335139652574073600631233/1125899906842624000000000000000000), (-435360068229487289308671/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial138.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial138.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial138.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial138 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 228144282220465958616387832029625), (Int.negOfNat 133163943806089169907599744795795), (Int.ofNat 1433559912367413197092836406771), (Int.ofNat 247720366515724245918412698372), (Int.negOfNat 124494479156210922173489865509), (Int.ofNat 13114346655071214016483185687), (Int.ofNat 1135563537575922174260871423), (Int.negOfNat 274260545418441895552587641), (Int.negOfNat 5852064433362225281210045), (Int.ofNat 2907307444306063951381673), (Int.ofNat 72293137401911982554635), (Int.negOfNat 20941460745529379881620), (Int.negOfNat 826583873221858794011), (Int.ofNat 112093245165855413818), (Int.ofNat 5607913884192176665), (Int.negOfNat 528547343904753037), (Int.negOfNat 13988968096613007), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(1825154257763727668931102656237/9007199254740992000000000000000), (-26632788761217833981519948959159/225179981368524800000000000000000), (1433559912367413197092836406771/1125899906842624000000000000000000), (61930091628931061479603174593/281474976710656000000000000000000), (-124494479156210922173489865509/1125899906842624000000000000000000), (13114346655071214016483185687/1125899906842624000000000000000000), (1135563537575922174260871423/1125899906842624000000000000000000), (-274260545418441895552587641/1125899906842624000000000000000000), (-1170412886672445056242009/225179981368524800000000000000000), (2907307444306063951381673/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial138.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial138.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial138.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial138 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 32002265505685244790855142467343), (Int.negOfNat 127295749529799900569473837965208), (Int.ofNat 1072511286032150477708901720236), (Int.negOfNat 190245742048761834785632851950), (Int.ofNat 3185458968528146795089224530), (Int.ofNat 6863701097093827085091806537), (Int.negOfNat 1493782819876296714984247052), (Int.ofNat 2546732525777594914176685), (Int.ofNat 30558502795874119465279801), (Int.negOfNat 239881503999673762898693), (Int.negOfNat 312891627476265677870427), (Int.negOfNat 1586218303466578301979), (Int.ofNat 2087693077616151300126), (Int.ofNat 34446940345934487222), (Int.negOfNat 9877025317058256425), (Int.negOfNat 250837104194944494), (Int.ofNat 20159021266215163), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-32002265505685244790855142467343/1125899906842624000000000000000000), (-15911968691224987571184229745651/140737488355328000000000000000000), (268127821508037619427225430059/281474976710656000000000000000000), (-3804914840975236695712657039/22517998136852480000000000000000), (318545896852814679508922453/112589990684262400000000000000000), (6863701097093827085091806537/1125899906842624000000000000000000), (-373445704969074178746061763/281474976710656000000000000000000), (509346505155518982835337/225179981368524800000000000000000), (30558502795874119465279801/1125899906842624000000000000000000), (-239881503999673762898693/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial138.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial138.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial138.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial138 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 283642970525889281360136310286707), (Int.negOfNat 124894116579070049858254245081937), (Int.ofNat 249936481650008228001215854970), (Int.negOfNat 78957380659417511286989736601), (Int.ofNat 12161156393978437964920131179), (Int.ofNat 1117281022352959940221331), (Int.ofNat 851487390342182581700199744), (Int.ofNat 200317492842654725652725323), (Int.negOfNat 16213041907056276700874071), (Int.negOfNat 3438908172382073528486109), (Int.ofNat 118944198990303910066951), (Int.ofNat 30355942269220671264193), (Int.negOfNat 401911028524641740038), (Int.negOfNat 176023664575462518272), (Int.ofNat 126526670888140489), (Int.ofNat 798552570140988976), (Int.negOfNat 10232567375556953), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-283642970525889281360136310286707/1125899906842624000000000000000000), (-124894116579070049858254245081937/1125899906842624000000000000000000), (24993648165000822800121585497/112589990684262400000000000000000), (-78957380659417511286989736601/1125899906842624000000000000000000), (12161156393978437964920131179/1125899906842624000000000000000000), (1117281022352959940221331/1125899906842624000000000000000000), (13304490474096602839065621/17592186044416000000000000000000), (200317492842654725652725323/1125899906842624000000000000000000), (-16213041907056276700874071/1125899906842624000000000000000000), (-3438908172382073528486109/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial138.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial138.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial138.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial138 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 532794097069384440777077920558109), (Int.negOfNat 124222978549290212683916132299456), (Int.ofNat 364389857967807079778511569904), (Int.ofNat 222264852511074793984669836643), (Int.ofNat 90093837133813816633902747982), (Int.ofNat 14609722424022609503077327494), (Int.ofNat 317095144873511618543820691), (Int.negOfNat 308094006922691496616408929), (Int.negOfNat 26447563313029245615217031), (Int.ofNat 3134052599507408844701353), (Int.ofNat 347477610430411773537219), (Int.negOfNat 18903674561862077018212), (Int.negOfNat 2563578841852467825099), (Int.ofNat 73059601844245533512), (Int.ofNat 12793255486619132061), (Int.negOfNat 119971044755822997), (Int.negOfNat 35828518637945643), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-532794097069384440777077920558109/1125899906842624000000000000000000), (-1940984039832659573186189567179/17592186044416000000000000000000), (22774366122987942486156973119/70368744177664000000000000000000), (222264852511074793984669836643/1125899906842624000000000000000000), (45046918566906908316951373991/562949953421312000000000000000000), (7304861212011304751538663747/562949953421312000000000000000000), (317095144873511618543820691/1125899906842624000000000000000000), (-308094006922691496616408929/1125899906842624000000000000000000), (-26447563313029245615217031/1125899906842624000000000000000000), (3134052599507408844701353/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial138.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial138.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial138.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial138 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 776119363888838207493833464484502), (Int.negOfNat 116141957164338576508883279869271), (Int.ofNat 4868433736399169071130954127219), (Int.ofNat 1379342018960625098500656585254), (Int.ofNat 155551403855212770009022421081), (Int.negOfNat 10975872845252150764588676840), (Int.negOfNat 4090786023714455091252090776), (Int.negOfNat 98084106777150583609617419), (Int.ofNat 52422905184307533708061191), (Int.ofNat 2944898711099913720154382), (Int.negOfNat 412838009396946279906154), (Int.negOfNat 30227078448907724467755), (Int.ofNat 2161260857836114746743), (Int.ofNat 188274177210019013852), (Int.negOfNat 7996861922669051688), (Int.negOfNat 844691936211847615), (Int.ofNat 42288851533592153), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-388059681944419103746916732242251/562949953421312000000000000000000), (-116141957164338576508883279869271/1125899906842624000000000000000000), (4868433736399169071130954127219/1125899906842624000000000000000000), (689671009480312549250328292627/562949953421312000000000000000000), (155551403855212770009022421081/1125899906842624000000000000000000), (-274396821131303769114716921/28147497671065600000000000000000), (-511348252964306886406511347/140737488355328000000000000000000), (-98084106777150583609617419/1125899906842624000000000000000000), (52422905184307533708061191/1125899906842624000000000000000000), (1472449355549956860077191/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial138.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial138.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial138.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial138 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 976017124021767633611455639768412), (Int.negOfNat 76787841564317004567847735107083), (Int.ofNat 15054025909846167238207119280236), (Int.ofNat 1577712336505380778462724377709), (Int.negOfNat 163023349986796962566316695501), (Int.negOfNat 42834179886428419841082078101), (Int.ofNat 713537411995499129209983397), (Int.ofNat 679604011663906044497129545), (Int.ofNat 13988806881330298037103470), (Int.negOfNat 6729479927151066415893252), (Int.negOfNat 265580706914322784521612), (Int.ofNat 44193048466884162596228), (Int.ofNat 2248464091020824394177), (Int.negOfNat 202844538613490033115), (Int.negOfNat 12055520654987069702), (Int.ofNat 638049639306871018), (Int.ofNat 29414490062616033), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-244004281005441908402863909942103/281474976710656000000000000000000), (-76787841564317004567847735107083/1125899906842624000000000000000000), (3763506477461541809551779820059/281474976710656000000000000000000), (1577712336505380778462724377709/1125899906842624000000000000000000), (-163023349986796962566316695501/1125899906842624000000000000000000), (-42834179886428419841082078101/1125899906842624000000000000000000), (713537411995499129209983397/1125899906842624000000000000000000), (135920802332781208899425909/225179981368524800000000000000000), (1398880688133029803710347/112589990684262400000000000000000), (-1682369981787766603973313/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial138.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial138.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial138.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial138 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 1060601454897634374745800020098915), (Int.negOfNat 5843208596398115077622247573720), (Int.ofNat 17801307237166963000613711848000), (Int.negOfNat 958233427282893801232471128019), (Int.negOfNat 371231735170873514892161177130), (Int.ofNat 14831637026621178299473746455), (Int.ofNat 7114749592707097042739314094), (Int.negOfNat 56473538649119943924888424), (Int.negOfNat 88787956291552025594311034), (Int.negOfNat 1182281382576001318147066), (Int.ofNat 726447339167407156727653), (Int.ofNat 19215823456791616755782), (Int.negOfNat 4071397912277294446247), (Int.negOfNat 142909761016080047274), (Int.ofNat 16349852928207550633), (Int.ofNat 704564236526646405), (Int.negOfNat 72207126166517483), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-212120290979526874949160004019783/225179981368524800000000000000000), (-146080214909952876940556189343/28147497671065600000000000000000), (2225163404645870375076713981/140737488355328000000000000000), (-958233427282893801232471128019/1125899906842624000000000000000000), (-37123173517087351489216117713/112589990684262400000000000000000), (2966327405324235659894749291/225179981368524800000000000000000), (3557374796353548521369657047/562949953421312000000000000000000), (-7059192331139992990611053/140737488355328000000000000000000), (-44393978145776012797155517/562949953421312000000000000000000), (-591140691288000659073533/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial138.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial138.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial138.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial138 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 1013788059945587329409619455233095), (Int.ofNat 44421253801656064235768950369650), (Int.ofNat 5842528091349351044374611952765), (Int.negOfNat 2382068353885927802907399004701), (Int.ofNat 93972721118918291805176254137), (Int.ofNat 59289181413127268394392485471), (Int.negOfNat 1947946779851674988760080894), (Int.negOfNat 959370203446950360941946496), (Int.ofNat 11448620549434256488589838), (Int.ofNat 9957598828386219306370414), (Int.ofNat 45538532800496571348391), (Int.negOfNat 68709327802927617913271), (Int.negOfNat 1079938486505946549703), (Int.ofNat 331106519234370650839), (Int.ofNat 7717323681956233253), (Int.negOfNat 1113990752533443309), (Int.negOfNat 23000461487286423), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-202757611989117465881923891046619/225179981368524800000000000000000), (888425076033121284715379007393/22517998136852480000000000000000), (1168505618269870208874922390553/225179981368524800000000000000000), (-2382068353885927802907399004701/1125899906842624000000000000000000), (93972721118918291805176254137/1125899906842624000000000000000000), (59289181413127268394392485471/1125899906842624000000000000000000), (-973973389925837494380040447/562949953421312000000000000000000), (-7495079714429299694858957/8796093022208000000000000000000), (5724310274717128244294919/562949953421312000000000000000000), (4978799414193109653185207/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial138.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial138.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial138.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial138 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 917470704017479443332486260656636), (Int.ofNat 46187120459085570797923440835472), (Int.negOfNat 2498634204574016376592100107585), (Int.negOfNat 35814190221290922202803309338), (Int.ofNat 352034117993082476265781509638), (Int.negOfNat 21130463230576576449521837045), (Int.negOfNat 8256574976768510839822760282), (Int.ofNat 348950920565441712982945801), (Int.ofNat 113716068084473401432803686), (Int.negOfNat 2270174979731659388861202), (Int.negOfNat 991381879773024053891991), (Int.ofNat 3611355661243624997543), (Int.ofNat 5793678406614103497387), (Int.ofNat 40480153273978437431), (Int.negOfNat 24075214964785239930), (Int.negOfNat 349934584427934185), (Int.ofNat 102125400799442813), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-229367676004369860833121565164159/281474976710656000000000000000000), (2886695028692848174870215052217/70368744177664000000000000000000), (-499726840914803275318420021517/225179981368524800000000000000000), (-17907095110645461101401654669/562949953421312000000000000000000), (176017058996541238132890754819/562949953421312000000000000000000), (-4226092646115315289904367409/225179981368524800000000000000000), (-4128287488384255419911380141/562949953421312000000000000000000), (348950920565441712982945801/1125899906842624000000000000000000), (56858034042236700716401843/562949953421312000000000000000000), (-1135087489865829694430601/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial138.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial138.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial138.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial138 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 830877932587218237002296384498956), (Int.ofNat 44014857011145546161626646403722), (Int.ofNat 2480167589999475488292488131740), (Int.ofNat 986746658423079043575735840300), (Int.negOfNat 151197753404077746289291446149), (Int.negOfNat 51841407226745338321643798739), (Int.ofNat 4894506476816756652764047084), (Int.ofNat 1049450640162469707486182153), (Int.negOfNat 57924354694443058828218549), (Int.negOfNat 12180098684789905861801954), (Int.ofNat 331917052681844192953764), (Int.ofNat 88606793978458313240639), (Int.negOfNat 914907623325127045457), (Int.negOfNat 438887395249849349402), (Int.negOfNat 13296498096059687), (Int.ofNat 1585472928670559610), (Int.ofNat 6613674700981703), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-207719483146804559250574096124739/281474976710656000000000000000000), (22007428505572773080813323201861/562949953421312000000000000000000), (124008379499973774414624406587/56294995342131200000000000000000), (9867466584230790435757358403/11258999068426240000000000000000), (-151197753404077746289291446149/1125899906842624000000000000000000), (-51841407226745338321643798739/1125899906842624000000000000000000), (1223626619204189163191011771/281474976710656000000000000000000), (1049450640162469707486182153/1125899906842624000000000000000000), (-57924354694443058828218549/1125899906842624000000000000000000), (-6090049342394952930900977/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial138.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial138.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial138.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial138 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 728684636714278082798879260043823), (Int.ofNat 58116020239244460708049017824653), (Int.ofNat 2350763177999202094137725825980), (Int.negOfNat 1086346598423705352104516678713), (Int.negOfNat 188149211543481956598040630743), (Int.ofNat 49605295707276984967604824769), (Int.ofNat 7192963063281202914302723172), (Int.negOfNat 913609792086248412873168305), (Int.negOfNat 124503222842060442439591627), (Int.ofNat 7814061640418563510816120), (Int.ofNat 1181773787878864919175530), (Int.negOfNat 37763111619762273058299), (Int.negOfNat 7123279930208037353801), (Int.ofNat 110030102647684368230), (Int.ofNat 29940575229884272673), (Int.negOfNat 109131344008645274), (Int.negOfNat 117794898171173293), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-728684636714278082798879260043823/1125899906842624000000000000000000), (58116020239244460708049017824653/1125899906842624000000000000000000), (117538158899960104706886291299/56294995342131200000000000000000), (-1086346598423705352104516678713/1125899906842624000000000000000000), (-188149211543481956598040630743/1125899906842624000000000000000000), (49605295707276984967604824769/1125899906842624000000000000000000), (1798240765820300728575680793/281474976710656000000000000000000), (-182721958417249682574633661/225179981368524800000000000000000), (-124503222842060442439591627/1125899906842624000000000000000000), (195351541010464087770403/28147497671065600000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial138.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial138.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial138.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial138 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 612846693673181675456743502229095), (Int.ofNat 53298286148455532173020943543039), (Int.negOfNat 3777113404360641846960727933647), (Int.negOfNat 133368794546340066714197725761), (Int.ofNat 389188638363318252818318191666), (Int.ofNat 26910131505142186101998676911), (Int.negOfNat 11253599444848801145454408224), (Int.negOfNat 1001401127767648636684953689), (Int.ofNat 132465274902294780744707048), (Int.ofNat 13599206128327474532619876), (Int.negOfNat 859357445520376234788405), (Int.negOfNat 103011611586776704096243), (Int.ofNat 3552660278154781086493), (Int.ofNat 515197886748928404541), (Int.negOfNat 9942105490950757670), (Int.negOfNat 1922396661118445221), (Int.ofNat 17607860771188257), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-122569338734636335091348700445819/225179981368524800000000000000000), (53298286148455532173020943543039/1125899906842624000000000000000000), (-3777113404360641846960727933647/1125899906842624000000000000000000), (-133368794546340066714197725761/1125899906842624000000000000000000), (194594319181659126409159095833/562949953421312000000000000000000), (26910131505142186101998676911/1125899906842624000000000000000000), (-351674982651525035795450257/35184372088832000000000000000000), (-1001401127767648636684953689/1125899906842624000000000000000000), (16558159362786847593088381/140737488355328000000000000000000), (3399801532081868633154969/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial138.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial138.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial138.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial138 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 516145991134830114905418151624781), (Int.ofNat 48748465071782801405388436171952), (Int.ofNat 3829765663907248035773391685616), (Int.ofNat 1988661421984695448760598909350), (Int.negOfNat 109402672090863072125575918663), (Int.negOfNat 114951852114498400919910109505), (Int.negOfNat 5397761519284782669460579652), (Int.ofNat 1846796916748790965975643148), (Int.ofNat 132608433633984741048334516), (Int.negOfNat 15284351570103907735465810), (Int.negOfNat 1326487180698093453720775), (Int.ofNat 79634300440813684239781), (Int.ofNat 8013604907879144959651), (Int.negOfNat 288531581699697006507), (Int.negOfNat 33554525096442051947), (Int.ofNat 791206416968992683), (Int.ofNat 121353627806818793), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-516145991134830114905418151624781/1125899906842624000000000000000000), (3046779066986425087836777260747/70368744177664000000000000000000), (239360353994203002235836980351/70368744177664000000000000000000), (39773228439693908975211978187/22517998136852480000000000000000), (-109402672090863072125575918663/1125899906842624000000000000000000), (-22990370422899680183982021901/225179981368524800000000000000000), (-1349440379821195667365144913/281474976710656000000000000000000), (461699229187197741493910787/281474976710656000000000000000000), (33152108408496185262083629/281474976710656000000000000000000), (-1528435157010390773546581/112589990684262400000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial138.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial138.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial138.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial138 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 392933718831388674130693876499465), (Int.ofNat 75120285169557885991578875018321), (Int.ofNat 4040155895485601148300897469933), (Int.negOfNat 3174820049079200889939601221550), (Int.negOfNat 992374715667683032862933352879), (Int.negOfNat 3654740113247046409993336767), (Int.ofNat 22146247045438246650499125196), (Int.ofNat 1073119723843863984933932592), (Int.negOfNat 230079282610538209141821756), (Int.negOfNat 15257747458477615210900008), (Int.ofNat 1464447340083708625529887), (Int.ofNat 113482642270910762542188), (Int.negOfNat 6429850264752694427103), (Int.negOfNat 555664887632790485508), (Int.ofNat 20825165736928109013), (Int.ofNat 2024579746217713341), (Int.negOfNat 47526135404113587), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-78586743766277734826138775299893/225179981368524800000000000000000), (75120285169557885991578875018321/1125899906842624000000000000000000), (4040155895485601148300897469933/1125899906842624000000000000000000), (-63496400981584017798792024431/22517998136852480000000000000000), (-992374715667683032862933352879/1125899906842624000000000000000000), (-3654740113247046409993336767/1125899906842624000000000000000000), (5536561761359561662624781299/281474976710656000000000000000000), (67069982740241499058370787/70368744177664000000000000000000), (-57519820652634552285455439/281474976710656000000000000000000), (-1907218432309701901362501/140737488355328000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial138.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial138.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial138.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial138 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 266436324046225490608889842148474), (Int.ofNat 25605371551170566959583872873690), (Int.negOfNat 33544958706336039314737241000462), (Int.negOfNat 7583569215963406512773380052651), (Int.ofNat 304602027707832016631942906826), (Int.ofNat 232763810033758969764123157581), (Int.ofNat 7264336844391282445326462635), (Int.negOfNat 3012189959706182788595962157), (Int.negOfNat 159731492574755568088015958), (Int.ofNat 23185458175203746776289348), (Int.ofNat 1477370649628972053558924), (Int.negOfNat 121294682272345298371288), (Int.negOfNat 8495951146811074691627), (Int.ofNat 464575962760599466003), (Int.ofNat 34445094120793272778), (Int.negOfNat 1352432157683831832), (Int.negOfNat 114939599231489183), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-133218162023112745304444921074237/562949953421312000000000000000000), (2560537155117056695958387287369/112589990684262400000000000000000), (-16772479353168019657368620500231/562949953421312000000000000000000), (-7583569215963406512773380052651/1125899906842624000000000000000000), (152301013853916008315971453413/562949953421312000000000000000000), (232763810033758969764123157581/1125899906842624000000000000000000), (1452867368878256489065292527/225179981368524800000000000000000), (-3012189959706182788595962157/1125899906842624000000000000000000), (-79865746287377784044007979/562949953421312000000000000000000), (5796364543800936694072337/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial138.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial138.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial138.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial138 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 397700324261125577062162717799279), (Int.negOfNat 171267760976238337971484470863546), (Int.negOfNat 53561856434737058674479495584258), (Int.ofNat 3494443814388927430937385261282), (Int.ofNat 2153128276304687496582735257731), (Int.ofNat 49743199721210948385108211328), (Int.negOfNat 34423027903676341903476361908), (Int.negOfNat 1603301352482914876278882929), (Int.ofNat 320468519068194409027567933), (Int.ofNat 18050444229100015900126312), (Int.negOfNat 1994254272365901240326518), (Int.negOfNat 121103730065244861917095), (Int.ofNat 8959793800144866026009), (Int.ofNat 559461394882917222770), (Int.negOfNat 30544885164622776428), (Int.negOfNat 1961677262535716621), (Int.ofNat 77444410037038917), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-397700324261125577062162717799279/1125899906842624000000000000000000), (-85633880488119168985742235431773/562949953421312000000000000000000), (-26780928217368529337239747792129/562949953421312000000000000000000), (1747221907194463715468692630641/562949953421312000000000000000000), (2153128276304687496582735257731/1125899906842624000000000000000000), (388618747821960534258657901/8796093022208000000000000000000), (-8605756975919085475869090477/281474976710656000000000000000000), (-1603301352482914876278882929/1125899906842624000000000000000000), (320468519068194409027567933/1125899906842624000000000000000000), (2256305528637501987515789/140737488355328000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial138.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial138.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial138.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial138 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 892805150628306289027871553105605), (Int.negOfNat 277671381137601713960613060245205), (Int.ofNat 14352149842172642201636638586937), (Int.ofNat 16940383535606639739795766132955), (Int.ofNat 537344345453850297669146471678), (Int.negOfNat 336657071623237381410690637478), (Int.negOfNat 16712867312737821509077210407), (Int.ofNat 3842045237608051333610176221), (Int.ofNat 213425342743889591426205207), (Int.negOfNat 28734177759021860244995839), (Int.negOfNat 1634657789909170966829607), (Int.ofNat 152203633020554100187472), (Int.ofNat 8533088241396159434595), (Int.negOfNat 602915257924789610910), (Int.negOfNat 32612351408117783799), (Int.ofNat 1831629384230294811), (Int.ofNat 108525570656159573), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-178561030125661257805574310621121/225179981368524800000000000000000), (-55534276227520342792122612049041/225179981368524800000000000000000), (14352149842172642201636638586937/1125899906842624000000000000000000), (3388076707121327947959153226591/225179981368524800000000000000000), (268672172726925148834573235839/562949953421312000000000000000000), (-168328535811618690705345318739/562949953421312000000000000000000), (-16712867312737821509077210407/1125899906842624000000000000000000), (3842045237608051333610176221/1125899906842624000000000000000000), (213425342743889591426205207/1125899906842624000000000000000000), (-28734177759021860244995839/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial138.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial138.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial138.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial138 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 1257931011375293559234502627820611), (Int.negOfNat 28057496927890564784333644357177), (Int.ofNat 100764891781990928104808154562544), (Int.ofNat 7460410147256037214552940500439), (Int.negOfNat 2647753294892100212043693724126), (Int.negOfNat 184835325198369578066870826558), (Int.ofNat 38780297201486853687604345566), (Int.ofNat 2492733539566649258562634715), (Int.negOfNat 358855212725047769558598863), (Int.negOfNat 21208775452535289444426565), (Int.ofNat 2278917362250201165300125), (Int.ofNat 123536298031683068168447), (Int.negOfNat 10566891694903666499924), (Int.negOfNat 523513681888282123100), (Int.ofNat 37376546831943831759), (Int.ofNat 1686131516170775350), (Int.negOfNat 105224675144854377), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-1257931011375293559234502627820611/1125899906842624000000000000000000), (-28057496927890564784333644357177/1125899906842624000000000000000000), (6297805736374433006550509660159/70368744177664000000000000000000), (7460410147256037214552940500439/1125899906842624000000000000000000), (-1323876647446050106021846862063/562949953421312000000000000000000), (-92417662599184789033435413279/562949953421312000000000000000000), (19390148600743426843802172783/562949953421312000000000000000000), (498546707913329851712526943/225179981368524800000000000000000), (-358855212725047769558598863/1125899906842624000000000000000000), (-4241755090507057888885313/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial138.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial138.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial138.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial138.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial138 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial138 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial138 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 1514415751732572647932230316562990), (Int.ofNat 11412137685527195213480180595571), (Int.ofNat 111494205282721837075841222466342), (Int.negOfNat 11027243314439495511442632914050), (Int.negOfNat 2817007703044727296800271171380), (Int.ofNat 281067717638740557750140916818), (Int.ofNat 40537420162890639001159981766), (Int.negOfNat 3564615774388358791196213465), (Int.negOfNat 371399041455678595155637593), (Int.ofNat 28066693935318483942687985), (Int.ofNat 2341980762245247636368275), (Int.negOfNat 152518777342886443436837), (Int.negOfNat 10796205821370224320324), (Int.ofNat 611119350590363652440), (Int.ofNat 37956231049270688259), (Int.negOfNat 1860036781368832300), (Int.negOfNat 105224675144854377), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-151441575173257264793223031656299/112589990684262400000000000000000), (11412137685527195213480180595571/1125899906842624000000000000000000), (55747102641360918537920611233171/562949953421312000000000000000000), (-220544866288789910228852658281/22517998136852480000000000000000), (-140850385152236364840013558569/56294995342131200000000000000000), (140533858819370278875070458409/562949953421312000000000000000000), (20268710081445319500579990883/562949953421312000000000000000000), (-712923154877671758239242693/225179981368524800000000000000000), (-371399041455678595155637593/1125899906842624000000000000000000), (5613338787063696788537597/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial138.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial138.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial138.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 1167851094795603798182355172119540), (Int.ofNat 263283843841962192031261943246945), (Int.ofNat 7027386256735351355176037986100), (Int.negOfNat 18316936631081486437675939354676), (Int.ofNat 1148942739337549392275827054748), (Int.ofNat 371800026475363235396650403615), (Int.negOfNat 26969395783359980179182302177), (Int.negOfNat 4215810149770001437758124801), (Int.ofNat 299169669746778927729670147), (Int.ofNat 31053062505448489382089469), (Int.negOfNat 2078135475134152387338147), (Int.negOfNat 161788704990237104709202), (Int.ofNat 10113715716951226050065), (Int.ofNat 631469422447122297260), (Int.negOfNat 36782746799416494949), (Int.negOfNat 1889597805962980461), (Int.ofNat 108525570656159573), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-58392554739780189909117758605977/56294995342131200000000000000000), (52656768768392438406252388649389/225179981368524800000000000000000), (70273862567353513551760379861/11258999068426240000000000000000), (-4579234157770371609418984838669/281474976710656000000000000000000), (287235684834387348068956763687/281474976710656000000000000000000), (74360005295072647079330080723/225179981368524800000000000000000), (-26969395783359980179182302177/1125899906842624000000000000000000), (-4215810149770001437758124801/1125899906842624000000000000000000), (299169669746778927729670147/1125899906842624000000000000000000), (31053062505448489382089469/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial138.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial138.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial138.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 731604262295621574290794406276296), (Int.ofNat 131399223241662178814089087259942), (Int.negOfNat 54209807341187508934639531825169), (Int.negOfNat 263757794321083519743864338662), (Int.ofNat 2495334868082982802494142282532), (Int.negOfNat 129680872307200649694844485555), (Int.negOfNat 40285952217387588177703089618), (Int.ofNat 2500329561547343937263146999), (Int.ofNat 368345493614548644324612673), (Int.negOfNat 23875382880811950097861752), (Int.negOfNat 2234244045422984788507718), (Int.ofNat 146077604731188887709415), (Int.ofNat 9788570389044709973709), (Int.negOfNat 636112740122865770030), (Int.negOfNat 32662493892664811878), (Int.ofNat 2096936913245316471), (Int.ofNat 77444410037038917), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-91450532786952696786349300784537/140737488355328000000000000000000), (65699611620831089407044543629971/562949953421312000000000000000000), (-54209807341187508934639531825169/1125899906842624000000000000000000), (-131878897160541759871932169331/562949953421312000000000000000000), (623833717020745700623535570633/281474976710656000000000000000000), (-25936174461440129938968897111/225179981368524800000000000000000), (-20142976108693794088851544809/562949953421312000000000000000000), (2500329561547343937263146999/1125899906842624000000000000000000), (368345493614548644324612673/1125899906842624000000000000000000), (-2984422860101493762232719/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial138.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial138.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial138.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 654157678341466186850167523157184), (Int.negOfNat 25431022352312480727902745496833), (Int.negOfNat 13738212009203268931307256861975), (Int.ofNat 9970588014358304324908860006401), (Int.negOfNat 225134804168049659150311702039), (Int.negOfNat 299140027630882597592841749693), (Int.ofNat 15001578562435431078826125405), (Int.ofNat 3749913321551463745833538017), (Int.negOfNat 223774118685608416107637588), (Int.negOfNat 27807364126364563301882888), (Int.ofNat 1814961561642944438385954), (Int.ofNat 140302413583196946510878), (Int.negOfNat 9729344539014770766287), (Int.negOfNat 520549786247026786993), (Int.ofNat 37776612883695369828), (Int.ofNat 1429723386660746032), (Int.negOfNat 114939599231489183), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-10221213724085409169533867549331/17592186044416000000000000000000), (-25431022352312480727902745496833/1125899906842624000000000000000000), (-549528480368130757252290274479/45035996273704960000000000000000), (9970588014358304324908860006401/1125899906842624000000000000000000), (-225134804168049659150311702039/1125899906842624000000000000000000), (-299140027630882597592841749693/1125899906842624000000000000000000), (3000315712487086215765225081/225179981368524800000000000000000), (3749913321551463745833538017/1125899906842624000000000000000000), (-55943529671402104026909397/281474976710656000000000000000000), (-3475920515795570412735361/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial138.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial138.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial138.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 692011835926411655087150755167845), (Int.ofNat 12405332006245447443155511682481), (Int.ofNat 22366193318519103484472827792014), (Int.ofNat 186203109744379586901879205286), (Int.negOfNat 1600272947913770149253485871763), (Int.ofNat 57229904627968894623171582320), (Int.ofNat 31265804179426732512893240366), (Int.negOfNat 1636976066907857510629948012), (Int.negOfNat 302819124243068051780487066), (Int.ofNat 18999301115186330274614518), (Int.ofNat 1827659527601047622812597), (Int.negOfNat 130245208624981349552188), (Int.negOfNat 7685756220512884080643), (Int.ofNat 609538327984503124798), (Int.ofNat 24049885847101733563), (Int.negOfNat 2159839396927313191), (Int.negOfNat 47526135404113587), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-138402367185282331017430151033569/225179981368524800000000000000000), (12405332006245447443155511682481/1125899906842624000000000000000000), (11183096659259551742236413896007/562949953421312000000000000000000), (93101554872189793450939602643/562949953421312000000000000000000), (-1600272947913770149253485871763/1125899906842624000000000000000000), (715373807849611182789644779/14073748835532800000000000000000), (15632902089713366256446620183/562949953421312000000000000000000), (-409244016726964377657487003/281474976710656000000000000000000), (-151409562121534025890243533/562949953421312000000000000000000), (9499650557593165137307259/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial138.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial138.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial138.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 598294520888983167836277092773343), (Int.ofNat 62485293679831197757722136170378), (Int.negOfNat 4379132496279706235241579381218), (Int.negOfNat 6659575995105267659650991193450), (Int.ofNat 145398612757738304346216297378), (Int.ofNat 207879801568386900781078411467), (Int.negOfNat 8892547551491781801401396992), (Int.negOfNat 2800299678802885058208178428), (Int.ofNat 163225047492818800087339286), (Int.ofNat 21162853410475791701469760), (Int.negOfNat 1504309773624488375062415), (Int.negOfNat 103916282053499255185451), (Int.ofNat 8725737822532372405831), (Int.ofNat 360753914225707173417), (Int.negOfNat 35618638650048169747), (Int.negOfNat 926466067678592533), (Int.ofNat 121353627806818793), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-598294520888983167836277092773343/1125899906842624000000000000000000), (31242646839915598878861068085189/562949953421312000000000000000000), (-2189566248139853117620789690609/562949953421312000000000000000000), (-133191519902105353193019823869/22517998136852480000000000000000), (72699306378869152173108148689/562949953421312000000000000000000), (207879801568386900781078411467/1125899906842624000000000000000000), (-34736513873014772661724207/4398046511104000000000000000000), (-700074919700721264552044607/281474976710656000000000000000000), (81612523746409400043669643/562949953421312000000000000000000), (66133916907736849067093/3518437208883200000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial138.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial138.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial138.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 536015195573855986690802303913785), (Int.negOfNat 16417653412018702738696782485530), (Int.negOfNat 27862255143061694553087902593397), (Int.ofNat 207665476149218570436874411796), (Int.ofNat 1151292742419252307518526066713), (Int.negOfNat 32505060813201812630074092565), (Int.negOfNat 21618464524142702889823779294), (Int.ofNat 1110186884128798237908563189), (Int.ofNat 212936902562620646004900328), (Int.negOfNat 14715559707862179902490876), (Int.negOfNat 1263832857496201543061575), (Int.ofNat 109623582530264976572933), (Int.ofNat 4977340861494656030183), (Int.negOfNat 540591933230607165051), (Int.negOfNat 13686256849034328370), (Int.ofNat 1940577194520561421), (Int.ofNat 17607860771188257), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-107203039114771197338160460782757/225179981368524800000000000000000), (-1641765341201870273869678248553/112589990684262400000000000000000), (-27862255143061694553087902593397/1125899906842624000000000000000000), (51916369037304642609218602949/281474976710656000000000000000000), (1151292742419252307518526066713/1125899906842624000000000000000000), (-6501012162640362526014818513/225179981368524800000000000000000), (-10809232262071351444911889647/562949953421312000000000000000000), (1110186884128798237908563189/1125899906842624000000000000000000), (26617112820327580750612541/140737488355328000000000000000000), (-3678889926965544975622719/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial138.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial138.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial138.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 662453231413777853974733197784862), (Int.negOfNat 94608107682678598551507628546785), (Int.negOfNat 5725479354671146143371161646339), (Int.ofNat 5568641170395688020704702869795), (Int.ofNat 7211609804007668265812256443), (Int.negOfNat 139573540081651176482702401019), (Int.ofNat 5428494844474082947417210202), (Int.ofNat 1827641169295011209605730805), (Int.negOfNat 118601200585799857389166207), (Int.negOfNat 13554602564575585593928850), (Int.ofNat 1191223382623277218895130), (Int.ofNat 62214693490381729815419), (Int.negOfNat 7283586502159219435111), (Int.negOfNat 185125514143554749350), (Int.ofNat 30641811811815380823), (Int.ofNat 322824497537271674), (Int.negOfNat 117794898171173293), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-331226615706888926987366598892431/562949953421312000000000000000000), (-18921621536535719710301525709357/225179981368524800000000000000000), (-5725479354671146143371161646339/1125899906842624000000000000000000), (1113728234079137604140940573959/225179981368524800000000000000000), (7211609804007668265812256443/1125899906842624000000000000000000), (-139573540081651176482702401019/1125899906842624000000000000000000), (2714247422237041473708605101/562949953421312000000000000000000), (365528233859002241921146161/225179981368524800000000000000000), (-118601200585799857389166207/1125899906842624000000000000000000), (-271092051291511711878577/22517998136852480000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial138.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial138.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial138.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 833827826098564826139210885435876), (Int.negOfNat 59906451383581809334604980666054), (Int.ofNat 18964548349422420568480849767929), (Int.ofNat 1670101377620714084247760644779), (Int.negOfNat 720881094854654940735219046652), (Int.ofNat 9308751392056480954517111738), (Int.ofNat 13098075825750373862711443004), (Int.negOfNat 741187446980477356837090853), (Int.negOfNat 125471042816815350945086429), (Int.ofNat 10962392891328594776378444), (Int.ofNat 691396363071213154489254), (Int.negOfNat 86076137988479483758009), (Int.negOfNat 2247890364110402494867), (Int.ofNat 438049224053230007942), (Int.ofNat 3644425440273698013), (Int.negOfNat 1643441350403245260), (Int.ofNat 6613674700981703), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-208456956524641206534802721358969/281474976710656000000000000000000), (-29953225691790904667302490333027/562949953421312000000000000000000), (18964548349422420568480849767929/1125899906842624000000000000000000), (1670101377620714084247760644779/1125899906842624000000000000000000), (-180220273713663735183804761663/281474976710656000000000000000000), (4654375696028240477258555869/562949953421312000000000000000000), (3274518956437593465677860751/281474976710656000000000000000000), (-741187446980477356837090853/1125899906842624000000000000000000), (-125471042816815350945086429/1125899906842624000000000000000000), (2740598222832148694094611/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial138.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial138.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial138.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 874940518808115340577673076022868), (Int.ofNat 15751555704151838695070434993537), (Int.ofNat 14905300311828512273877735935885), (Int.negOfNat 2203021593770304497315021398588), (Int.negOfNat 140237348823701328919192435719), (Int.ofNat 73060773684739672476142389121), (Int.negOfNat 2951920647577803138486796112), (Int.negOfNat 970676428717583194346186821), (Int.ofNat 82365936603093132085641946), (Int.ofNat 6660518557445088868005112), (Int.negOfNat 876821484063488158002951), (Int.negOfNat 24004941597708281316353), (Int.ofNat 5520412417350217477407), (Int.ofNat 26473640975384298729), (Int.negOfNat 23652301905024755130), (Int.ofNat 176029319229877235), (Int.ofNat 102125400799442813), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-218735129702028835144418269005717/281474976710656000000000000000000), (15751555704151838695070434993537/1125899906842624000000000000000000), (2981060062365702454775547187177/225179981368524800000000000000000), (-550755398442576124328755349647/281474976710656000000000000000000), (-140237348823701328919192435719/1125899906842624000000000000000000), (73060773684739672476142389121/1125899906842624000000000000000000), (-184495040473612696155424757/70368744177664000000000000000000), (-970676428717583194346186821/1125899906842624000000000000000000), (41182968301546566042820973/562949953421312000000000000000000), (832564819680636108500639/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial138.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial138.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial138.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 801635829941871815402017764578617), (Int.ofNat 49387196031099558104932541760089), (Int.ofNat 2973463996928845921799513568772), (Int.negOfNat 1248838227485838764477351271414), (Int.ofNat 248458319223696314449407094251), (Int.negOfNat 806781311479645631430543885), (Int.negOfNat 5826473421833540029737426024), (Int.ofNat 470899334066211279564712096), (Int.ofNat 53368355982199307884189758), (Int.negOfNat 7501502299555419349356664), (Int.negOfNat 215859156715149403970059), (Int.ofNat 60500064985384157673831), (Int.negOfNat 4897277534301524243), (Int.negOfNat 311591847628409211249), (Int.ofNat 4574559744199653703), (Int.ofNat 1113990752533443309), (Int.negOfNat 23000461487286423), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-801635829941871815402017764578617/1125899906842624000000000000000000), (49387196031099558104932541760089/1125899906842624000000000000000000), (743365999232211480449878392193/281474976710656000000000000000000), (-624419113742919382238675635707/562949953421312000000000000000000), (248458319223696314449407094251/1125899906842624000000000000000000), (-161356262295929126286108777/225179981368524800000000000000000), (-728309177729192503717178253/140737488355328000000000000000000), (14715604189569102486397253/35184372088832000000000000000000), (26684177991099653942094879/562949953421312000000000000000000), (-937687787444427418669583/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial138.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial138.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial138.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 697311668859528143284375960748351), (Int.ofNat 53310323081978534192415453952818), (Int.ofNat 357221168440048816102983952668), (Int.ofNat 92486429424502277537800500585), (Int.ofNat 51727667178248555521866250241), (Int.negOfNat 22430075598114694435109026016), (Int.ofNat 1808885858725543610454980754), (Int.ofNat 326100218460372056456688324), (Int.negOfNat 51838657062370962873560704), (Int.negOfNat 1482839453355828482429644), (Int.ofNat 562709528254455942076553), (Int.negOfNat 4499938928079275760532), (Int.negOfNat 3564078499554893038227), (Int.ofNat 89252688446975518604), (Int.ofNat 15237030176865399783), (Int.negOfNat 589769666903387455), (Int.negOfNat 72207126166517483), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-697311668859528143284375960748351/1125899906842624000000000000000000), (26655161540989267096207726976409/562949953421312000000000000000000), (89305292110012204025745988167/281474976710656000000000000000000), (18497285884900455507560100117/225179981368524800000000000000000), (51727667178248555521866250241/1125899906842624000000000000000000), (-700939862441084201097157063/35184372088832000000000000000000), (904442929362771805227490377/562949953421312000000000000000000), (81525054615093014114172081/281474976710656000000000000000000), (-404989508299773147449693/8796093022208000000000000000000), (-370709863338957120607411/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial138.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial138.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial138.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 588268333357575888035455990096347), (Int.ofNat 56149573085148749668871455574541), (Int.ofNat 918876073687381369184100614250), (Int.negOfNat 11636033321998260319052265686), (Int.negOfNat 29802406962333602853377830281), (Int.ofNat 4542173849031989573892027120), (Int.ofNat 1214907823489362975174172867), (Int.negOfNat 275358698865015788682874515), (Int.negOfNat 5377069743950200899202720), (Int.ofNat 4278097761478196424490232), (Int.negOfNat 99179355175685355682052), (Int.negOfNat 34305676709289494018058), (Int.ofNat 1450931559673144241597), (Int.ofNat 173952289333014389405), (Int.negOfNat 9481114044207904552), (Int.negOfNat 580081217574185368), (Int.ofNat 29414490062616033), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-588268333357575888035455990096347/1125899906842624000000000000000000), (56149573085148749668871455574541/1125899906842624000000000000000000), (3675504294749525476736402457/4503599627370496000000000000000), (-5818016660999130159526132843/562949953421312000000000000000000), (-29802406962333602853377830281/1125899906842624000000000000000000), (56777173112899869673650339/14073748835532800000000000000000), (1214907823489362975174172867/1125899906842624000000000000000000), (-55071739773003157736574903/225179981368524800000000000000000), (-33606685899688755620017/7036874417766400000000000000000), (534762220184774553061279/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial138.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial138.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial138.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 472675102687339598819727956207253), (Int.ofNat 59208543567499040447693569338019), (Int.ofNat 611803862457102488139467159140), (Int.negOfNat 17586764198687636575635131392), (Int.ofNat 20094657571013803655230825586), (Int.ofNat 585640594509040413140586595), (Int.negOfNat 1092423588317774613932743606), (Int.ofNat 29238559634921329346037799), (Int.ofNat 24954585804925366142582561), (Int.negOfNat 1451701894743648335693272), (Int.negOfNat 261628921718245674546144), (Int.ofNat 19928177728746914434255), (Int.ofNat 1593423869766007234423), (Int.negOfNat 146586856326599324292), (Int.negOfNat 6410107180958085888), (Int.ofNat 709432285502247765), (Int.ofNat 42288851533592153), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-472675102687339598819727956207253/1125899906842624000000000000000000), (59208543567499040447693569338019/1125899906842624000000000000000000), (30590193122855124406973357957/56294995342131200000000000000000), (-17174574412780895093393683/1099511627776000000000000000000), (10047328785506901827615412793/562949953421312000000000000000000), (117128118901808082628117319/225179981368524800000000000000000), (-546211794158887306966371803/562949953421312000000000000000000), (29238559634921329346037799/1125899906842624000000000000000000), (24954585804925366142582561/1125899906842624000000000000000000), (-181462736842956041961659/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial138.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial138.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial138.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 351671988516504811035585775955303), (Int.ofNat 61959076194398661939054223980415), (Int.ofNat 828531878997462971618448993731), (Int.ofNat 42052528845386831361687551300), (Int.negOfNat 11842428753666325161709764755), (Int.negOfNat 3225954615550279498988755863), (Int.ofNat 610844621016551761403842271), (Int.ofNat 96218899580348496376996519), (Int.negOfNat 16001188884536717129592751), (Int.negOfNat 1345864624712424487379363), (Int.ofNat 230299832637400930054749), (Int.ofNat 9732861628362656526352), (Int.negOfNat 1945518537235800299529), (Int.negOfNat 41005828414113000762), (Int.ofNat 10723526411874133911), (Int.ofNat 42679815778908797), (Int.negOfNat 35828518637945643), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-351671988516504811035585775955303/1125899906842624000000000000000000), (12391815238879732387810844796083/225179981368524800000000000000000), (828531878997462971618448993731/1125899906842624000000000000000000), (420525288453868313616875513/11258999068426240000000000000000), (-2368485750733265032341952951/225179981368524800000000000000000), (-3225954615550279498988755863/1125899906842624000000000000000000), (610844621016551761403842271/1125899906842624000000000000000000), (96218899580348496376996519/1125899906842624000000000000000000), (-16001188884536717129592751/1125899906842624000000000000000000), (-1345864624712424487379363/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial138.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial138.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial138.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 224349125468983644232662330290375), (Int.ofNat 65282942117411177456905359315666), (Int.ofNat 717731434262574224542860575512), (Int.negOfNat 62291483565496825419989501670), (Int.negOfNat 602079455777316742720410578), (Int.ofNat 4249903512307355947482636265), (Int.ofNat 63173444360734259015985754), (Int.negOfNat 130294138607554693403629423), (Int.negOfNat 1009813895399593487780701), (Int.ofNat 2169378247958081758130659), (Int.negOfNat 1720563987324158393129), (Int.negOfNat 21733574719392345104273), (Int.ofNat 162008525996798270782), (Int.ofNat 141381005873803916082), (Int.negOfNat 1522548741124781691), (Int.negOfNat 663292919431389126), (Int.negOfNat 10232567375556953), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1794793003751869153861298642323/9007199254740992000000000000000), (32641471058705588728452679657833/562949953421312000000000000000000), (89716429282821778067857571939/140737488355328000000000000000000), (-6229148356549682541998950167/112589990684262400000000000000000), (-301039727888658371360205289/562949953421312000000000000000000), (849980702461471189496527253/225179981368524800000000000000000), (31586722180367129507992877/562949953421312000000000000000000), (-130294138607554693403629423/1125899906842624000000000000000000), (-1009813895399593487780701/1125899906842624000000000000000000), (2169378247958081758130659/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial138.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial138.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial138.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 91296110562237747900744689485109), (Int.ofNat 67684575068174033705516839631251), (Int.ofNat 604716333435232070185783061894), (Int.ofNat 48996877822650928058664417811), (Int.ofNat 15948694818187427601902298827), (Int.negOfNat 2612680303741719987538529483), (Int.negOfNat 705468873894848392300033062), (Int.ofNat 67476621709322437334919215), (Int.ofNat 15355274784217436252186431), (Int.negOfNat 1029648420424318007456757), (Int.negOfNat 192226864498637609410347), (Int.ofNat 10208585853294904461899), (Int.ofNat 1523773523094711289306), (Int.negOfNat 69089599047593089412), (Int.negOfNat 8227949905045334245), (Int.ofNat 386096754904544344), (Int.ofNat 20159021266215163), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-91296110562237747900744689485109/1125899906842624000000000000000000), (67684575068174033705516839631251/1125899906842624000000000000000000), (302358166717616035092891530947/562949953421312000000000000000000), (48996877822650928058664417811/1125899906842624000000000000000000), (15948694818187427601902298827/1125899906842624000000000000000000), (-2612680303741719987538529483/1125899906842624000000000000000000), (-352734436947424196150016531/562949953421312000000000000000000), (13495324341864487466983843/225179981368524800000000000000000), (15355274784217436252186431/1125899906842624000000000000000000), (-1029648420424318007456757/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial138.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial138.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial138.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 47022173668050694501817229161413), (Int.ofNat 70900041451267936934329122079872), (Int.ofNat 969417891341786915588240523794), (Int.ofNat 16597014838849171445413558583), (Int.negOfNat 22558213268583415655143765810), (Int.negOfNat 1730578846559495307955432808), (Int.ofNat 841814061432882031400849843), (Int.ofNat 62385438076098895313175231), (Int.negOfNat 16298438861854753766834325), (Int.negOfNat 1119119469511079594059683), (Int.ofNat 189470915194922826037105), (Int.ofNat 11770647812029959389760), (Int.negOfNat 1444644177838526319581), (Int.negOfNat 80039471735722881068), (Int.ofNat 7677642958937174815), (Int.ofNat 451256114927838837), (Int.negOfNat 13988968096613007), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(47022173668050694501817229161413/1125899906842624000000000000000000), (553906573838030757299446266249/8796093022208000000000000000000), (484708945670893457794120261897/562949953421312000000000000000000), (16597014838849171445413558583/1125899906842624000000000000000000), (-2255821326858341565514376581/112589990684262400000000000000000), (-216322355819936913494429101/140737488355328000000000000000000), (841814061432882031400849843/1125899906842624000000000000000000), (62385438076098895313175231/1125899906842624000000000000000000), (-651937554474190150673373/45035996273704960000000000000000), (-1119119469511079594059683/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial138.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial138.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial138.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 192473722051488724080714216149142), (Int.ofNat 74287940841214868745553550607535), (Int.ofNat 601158076576000337850647672395), (Int.negOfNat 95461411718287325391536752668), (Int.ofNat 8186161582899391185444390105), (Int.ofNat 5765514532278458383949660304), (Int.negOfNat 148065607881022083145327702), (Int.negOfNat 157118646159590992254691783), (Int.ofNat 133179726808093964847397), (Int.ofNat 2363916952815239963078452), (Int.ofNat 25550013942098327481262), (Int.negOfNat 22078727714389371639169), (Int.negOfNat 362938375038085478907), (Int.ofNat 138447505482682277400), (Int.ofNat 2589035879524761992), (Int.negOfNat 642319694025257065), (Int.ofNat 7621243841600297), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(96236861025744362040357108074571/562949953421312000000000000000000), (14857588168242973749110710121507/225179981368524800000000000000000), (120231615315200067570129534479/225179981368524800000000000000000), (-23865352929571831347884188167/281474976710656000000000000000000), (1637232316579878237088878021/225179981368524800000000000000000), (360344658267403648996853769/70368744177664000000000000000000), (-74032803940511041572663851/562949953421312000000000000000000), (-157118646159590992254691783/1125899906842624000000000000000000), (133179726808093964847397/1125899906842624000000000000000000), (590979238203809990769613/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial138.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial138.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial138.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 342977657446013904934041498222884), (Int.ofNat 76176880346415289673645694439579), (Int.ofNat 555781367633159501989579725126), (Int.ofNat 101378862478317324829461510329), (Int.ofNat 22060995464087627607149432515), (Int.negOfNat 4821167043142353963737202247), (Int.negOfNat 975497310008136311553421067), (Int.ofNat 99476631654919863036724521), (Int.ofNat 20946513951584421737336950), (Int.negOfNat 1071996011609222077552490), (Int.negOfNat 257543712523433496845380), (Int.ofNat 6537005676723821707980), (Int.ofNat 2008060958027879340851), (Int.negOfNat 22558561753202436825), (Int.negOfNat 10675469757273063906), (Int.negOfNat 10704502869832958), (Int.ofNat 20402996671942617), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(85744414361503476233510374555721/281474976710656000000000000000000), (76176880346415289673645694439579/1125899906842624000000000000000000), (277890683816579750994789862563/562949953421312000000000000000000), (101378862478317324829461510329/1125899906842624000000000000000000), (4412199092817525521429886503/225179981368524800000000000000000), (-4821167043142353963737202247/1125899906842624000000000000000000), (-975497310008136311553421067/1125899906842624000000000000000000), (99476631654919863036724521/1125899906842624000000000000000000), (418930279031688434746739/22517998136852480000000000000000), (-107199601160922207755249/112589990684262400000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial138.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial138.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial138.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 498519145250535628683458291715447), (Int.ofNat 79811862023672252761234964142698), (Int.ofNat 1170495835156671729708227188834), (Int.ofNat 12952732760875314393298258011), (Int.negOfNat 40638834874401371537247855070), (Int.negOfNat 2646071832189644921271135063), (Int.ofNat 1380114904201365007131539316), (Int.ofNat 111547344965169600275447010), (Int.negOfNat 22994957665172802876533246), (Int.negOfNat 2123752011331836430709296), (Int.ofNat 216961472131078015524319), (Int.ofNat 22647093540384704276946), (Int.negOfNat 1273695119098258441381), (Int.negOfNat 152411218533309772466), (Int.ofNat 4944121045238060995), (Int.ofNat 724544984951482335), (Int.negOfNat 37539518474525627), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(498519145250535628683458291715447/1125899906842624000000000000000000), (39905931011836126380617482071349/562949953421312000000000000000000), (585247917578335864854113594417/562949953421312000000000000000000), (12952732760875314393298258011/1125899906842624000000000000000000), (-4063883487440137153724785507/112589990684262400000000000000000), (-2646071832189644921271135063/1125899906842624000000000000000000), (345028726050341251782884829/281474976710656000000000000000000), (11154734496516960027544701/112589990684262400000000000000000), (-11497478832586401438266623/562949953421312000000000000000000), (-132734500708239776919331/70368744177664000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial138.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial138.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial138.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 662289472375533585955342953186759), (Int.ofNat 83424992262552556976599752717136), (Int.ofNat 419417764972146973404121088075), (Int.negOfNat 183234198260559299685058524739), (Int.ofNat 16285588719971290407970085919), (Int.ofNat 10949024839771044263579447845), (Int.negOfNat 100343661934735527491072648), (Int.negOfNat 280126290803529000695596386), (Int.negOfNat 7174560446418513214007766), (Int.ofNat 3723700396585504854353240), (Int.ofNat 165317308020735673893181), (Int.negOfNat 29168418605563932858453), (Int.negOfNat 1661770812330605539293), (Int.ofNat 147894047620418193853), (Int.ofNat 9996995621512737103), (Int.negOfNat 473230008868091991), (Int.negOfNat 26817025247272227), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(662289472375533585955342953186759/1125899906842624000000000000000000), (5214062016409534811037484544821/70368744177664000000000000000000), (16776710598885878936164843523/45035996273704960000000000000000), (-183234198260559299685058524739/1125899906842624000000000000000000), (16285588719971290407970085919/1125899906842624000000000000000000), (2189804967954208852715889569/225179981368524800000000000000000), (-12542957741841940936384081/140737488355328000000000000000000), (-140063145401764500347798193/562949953421312000000000000000000), (-3587280223209256607003883/562949953421312000000000000000000), (93092509914637621358831/28147497671065600000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial138.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial138.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial138.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 829920088373093087891377353626870), (Int.ofNat 84157869766433291553552453712100), (Int.ofNat 379760927176362345376193730757), (Int.ofNat 220417216706962577176217180524), (Int.ofNat 49140144110888066777545556348), (Int.negOfNat 9133715183068276559629631319), (Int.negOfNat 2258852594092710146835002672), (Int.ofNat 123425806803304332051116761), (Int.ofNat 45407565377798393332964290), (Int.negOfNat 197888376433415738160548), (Int.negOfNat 483812832988363765918973), (Int.negOfNat 9532658582385918124095), (Int.ofNat 3106934725125802341433), (Int.ofNat 103045740023638708033), (Int.negOfNat 13401085008608538166), (Int.negOfNat 583716285363757115), (Int.ofNat 67457793107450957), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(82992008837309308789137735362687/112589990684262400000000000000000), (841578697664332915535524537121/11258999068426240000000000000000), (379760927176362345376193730757/1125899906842624000000000000000000), (55104304176740644294054295131/281474976710656000000000000000000), (12285036027722016694386389087/281474976710656000000000000000000), (-9133715183068276559629631319/1125899906842624000000000000000000), (-141178287130794384177187667/70368744177664000000000000000000), (123425806803304332051116761/1125899906842624000000000000000000), (4540756537779839333296429/112589990684262400000000000000000), (-49472094108353934540137/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial138.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial138.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial138.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 1001894426111360388586424904650054), (Int.ofNat 88828839642649640646315214629878), (Int.ofNat 1766585566720031411391468779076), (Int.ofNat 28733598059208408195816321018), (Int.negOfNat 99598991416607038988960669323), (Int.negOfNat 9778002783125996850505323553), (Int.ofNat 2850226945527470088026916794), (Int.ofNat 390171620914411344996729485), (Int.negOfNat 31859201315279195712189391), (Int.negOfNat 6293929481086160266141612), (Int.ofNat 118436313540096701387932), (Int.ofNat 52748231637809322366973), (Int.ofNat 325790037751144707209), (Int.negOfNat 278076837878577247802), (Int.negOfNat 5367970189665963917), (Int.ofNat 1038225964520955750), (Int.ofNat 23258295611626727), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(500947213055680194293212452325027/562949953421312000000000000000000), (44414419821324820323157607314939/562949953421312000000000000000000), (441646391680007852847867194769/281474976710656000000000000000000), (14366799029604204097908160509/562949953421312000000000000000000), (-99598991416607038988960669323/1125899906842624000000000000000000), (-9778002783125996850505323553/1125899906842624000000000000000000), (1425113472763735044013458397/562949953421312000000000000000000), (78034324182882268999345897/225179981368524800000000000000000), (-31859201315279195712189391/1125899906842624000000000000000000), (-1573482370271540066535403/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial138.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial138.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial138.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 1185163042850888752482866908011869), (Int.ofNat 92946685955667370515175743903441), (Int.negOfNat 370646895139291749439574837908), (Int.negOfNat 571573365370379797743992753959), (Int.ofNat 25580076948143481885505922437), (Int.ofNat 32691609024867067912402652503), (Int.ofNat 1649494771840965834652288486), (Int.negOfNat 656537268648381246250983813), (Int.negOfNat 63206176118098732946186013), (Int.ofNat 5079249618991180173045946), (Int.ofNat 748270001321385567601706), (Int.negOfNat 17900327768235191822453), (Int.negOfNat 4921263115561894506147), (Int.ofNat 7971154512228720754), (Int.ofNat 21479775180361237083), (Int.ofNat 286580441246440954), (Int.negOfNat 91679328579620917), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(1185163042850888752482866908011869/1125899906842624000000000000000000), (92946685955667370515175743903441/1125899906842624000000000000000000), (-92661723784822937359893709477/281474976710656000000000000000000), (-571573365370379797743992753959/1125899906842624000000000000000000), (25580076948143481885505922437/1125899906842624000000000000000000), (32691609024867067912402652503/1125899906842624000000000000000000), (824747385920482917326144243/562949953421312000000000000000000), (-656537268648381246250983813/1125899906842624000000000000000000), (-63206176118098732946186013/1125899906842624000000000000000000), (2539624809495590086522973/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial138.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial138.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial138.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 1366465313500598525715625479179005), (Int.ofNat 88012174423891313394215267533047), (Int.negOfNat 698218344778906830347581943555), (Int.ofNat 761231961127762521035297987173), (Int.ofNat 226026155201277146701133884152), (Int.negOfNat 15709544811881366406651548947), (Int.negOfNat 9231034909492071182887297590), (Int.negOfNat 427033472741077595078006853), (Int.ofNat 104721256096762272298961968), (Int.ofNat 8883285301397719434344814), (Int.negOfNat 596608546720878173324279), (Int.negOfNat 75837673527870043889685), (Int.ofNat 1897430247052274647687), (Int.ofNat 398707821494641992515), (Int.negOfNat 2544234159599039506), (Int.negOfNat 1537079781288104659), (Int.negOfNat 7588798239896247), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(273293062700119705143125095835801/225179981368524800000000000000000), (88012174423891313394215267533047/1125899906842624000000000000000000), (-139643668955781366069516388711/225179981368524800000000000000000), (761231961127762521035297987173/1125899906842624000000000000000000), (28253269400159643337641735519/140737488355328000000000000000000), (-15709544811881366406651548947/1125899906842624000000000000000000), (-923103490949207118288729759/112589990684262400000000000000000), (-427033472741077595078006853/1125899906842624000000000000000000), (6545078506047642018685123/70368744177664000000000000000000), (4441642650698859717172407/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial138.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial138.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial138.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 1548285512775883190866384274098677), (Int.ofNat 98490348240357089166082311113360), (Int.ofNat 5754398512395361055279592106218), (Int.ofNat 448330602925978307272822885046), (Int.negOfNat 462237756531227284702304573093), (Int.negOfNat 104265853386597065260378987719), (Int.negOfNat 442919658850147712188214850), (Int.ofNat 1642866910321332340591815134), (Int.ofNat 86884166752021672475663856), (Int.negOfNat 12456037717324050505068104), (Int.negOfNat 1028240945368116967221393), (Int.ofNat 56742395906925267345523), (Int.ofNat 6591806268371084187773), (Int.negOfNat 165453416331193297705), (Int.negOfNat 28423925199240195097), (Int.ofNat 301980852198158997), (Int.ofNat 108066115365925637), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(1548285512775883190866384274098677/1125899906842624000000000000000000), (1231129353004463614576028888917/14073748835532800000000000000000), (2877199256197680527639796053109/562949953421312000000000000000000), (224165301462989153636411442523/562949953421312000000000000000000), (-462237756531227284702304573093/1125899906842624000000000000000000), (-104265853386597065260378987719/1125899906842624000000000000000000), (-8858393177002954243764297/22517998136852480000000000000000), (821433455160666170295907567/562949953421312000000000000000000), (5430260422001354529728991/70368744177664000000000000000000), (-1557004714665506313133513/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial138.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial138.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial138.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 1761335030162687392128079650127409), (Int.ofNat 104461792124639836701012271518203), (Int.negOfNat 9904426013343469232623612915213), (Int.negOfNat 6495057665112383546685495847492), (Int.negOfNat 1035056886119749839293238060615), (Int.ofNat 36204979853903475240923839495), (Int.ofNat 21634864504117406879505836674), (Int.ofNat 689230844188907156713021402), (Int.negOfNat 207051132102624639880193284), (Int.negOfNat 12430131725730390119825950), (Int.ofNat 1198128149230102927224465), (Int.ofNat 98566836414078175414544), (Int.negOfNat 4647237357666198695705), (Int.negOfNat 497916743676484192792), (Int.ofNat 12653159412065639915), (Int.ofNat 1853063818898359779), (Int.negOfNat 22329476393029083), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(1761335030162687392128079650127409/1125899906842624000000000000000000), (104461792124639836701012271518203/1125899906842624000000000000000000), (-9904426013343469232623612915213/1125899906842624000000000000000000), (-1623764416278095886671373961873/281474976710656000000000000000000), (-207011377223949967858647612123/225179981368524800000000000000000), (7240995970780695048184767899/225179981368524800000000000000000), (10817432252058703439752918337/562949953421312000000000000000000), (344615422094453578356510701/562949953421312000000000000000000), (-51762783025656159970048321/281474976710656000000000000000000), (-248602634514607802396519/22517998136852480000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial138.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial138.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial138.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 1864692987672008778280531469087846), (Int.negOfNat 39092910034256021280974412046868), (Int.negOfNat 65576331298194319254135339724330), (Int.negOfNat 9895715940548502582310346318775), (Int.ofNat 555566716281969854867550929746), (Int.ofNat 247859823776760544027410017047), (Int.ofNat 4854084440560575410557788195), (Int.negOfNat 2907060591123845432159192849), (Int.negOfNat 138555498055448034150694162), (Int.ofNat 20665731746895243455292134), (Int.ofNat 1352576033910268820528044), (Int.negOfNat 99072285434053891284400), (Int.negOfNat 8011424974861423466805), (Int.ofNat 341298484083288827597), (Int.ofNat 33186882394451740874), (Int.negOfNat 855213194401645488), (Int.negOfNat 114480143941255247), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(932346493836004389140265734543923/562949953421312000000000000000000), (-9773227508564005320243603011717/281474976710656000000000000000000), (-6557633129819431925413533972433/112589990684262400000000000000000), (-395828637621940103292413852751/45035996273704960000000000000000), (277783358140984927433775464873/562949953421312000000000000000000), (247859823776760544027410017047/1125899906842624000000000000000000), (970816888112115082111557639/225179981368524800000000000000000), (-2907060591123845432159192849/1125899906842624000000000000000000), (-69277749027724017075347081/562949953421312000000000000000000), (10332865873447621727646067/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial138.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial138.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial138.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 1461771517630765850142734550031503), (Int.negOfNat 382998917544568327739351740515716), (Int.negOfNat 92717551763388890673860013970522), (Int.ofNat 3490528795906530833703516144456), (Int.ofNat 2452709504320326873282226280133), (Int.ofNat 48813532584654003037187812196), (Int.negOfNat 34771963617405475648076207830), (Int.negOfNat 1525697769599658551485890389), (Int.ofNat 302066032867365103058718395), (Int.ofNat 17435014408279132138562654), (Int.negOfNat 1760259845468998378867134), (Int.negOfNat 119574756168162707675841), (Int.ofNat 7343613787702808478647), (Int.ofNat 564635796650143764878), (Int.negOfNat 22980047586946167988), (Int.negOfNat 2012514325827789539), (Int.ofNat 52247751025954413), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(1461771517630765850142734550031503/1125899906842624000000000000000000), (-95749729386142081934837935128929/281474976710656000000000000000000), (-46358775881694445336930006985261/562949953421312000000000000000000), (436316099488316354212939518057/140737488355328000000000000000000), (2452709504320326873282226280133/1125899906842624000000000000000000), (12203383146163500759296953049/281474976710656000000000000000000), (-3477196361740547564807620783/112589990684262400000000000000000), (-1525697769599658551485890389/1125899906842624000000000000000000), (60413206573473020611743679/225179981368524800000000000000000), (8717507204139566069281327/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial138.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial138.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial138.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 391296638485808271732961766208855), (Int.negOfNat 636611387990456884568632449034407), (Int.negOfNat 17776234611278907458029733521753), (Int.ofNat 19250757790746336109881238446101), (Int.ofNat 808343563441870093475822336276), (Int.negOfNat 342962902018322122013977042668), (Int.negOfNat 17730129079295833677173280919), (Int.ofNat 3731996204454441735925576617), (Int.ofNat 216825198746740866027084597), (Int.negOfNat 26686514515008017077328731), (Int.negOfNat 1678054934619505144121749), (Int.ofNat 134172486354666713256180), (Int.ofNat 8962730309837037003725), (Int.negOfNat 500678282045753997434), (Int.negOfNat 35132234378462166405), (Int.ofNat 1411937403441150609), (Int.ofNat 120894172516584857), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(78259327697161654346592353241771/225179981368524800000000000000000), (-636611387990456884568632449034407/1125899906842624000000000000000000), (-17776234611278907458029733521753/1125899906842624000000000000000000), (19250757790746336109881238446101/1125899906842624000000000000000000), (202085890860467523368955584069/281474976710656000000000000000000), (-85740725504580530503494260667/281474976710656000000000000000000), (-17730129079295833677173280919/1125899906842624000000000000000000), (3731996204454441735925576617/1125899906842624000000000000000000), (216825198746740866027084597/1125899906842624000000000000000000), (-26686514515008017077328731/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial138.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial138.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial138.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 797682929909532983752808356829519), (Int.negOfNat 479855868621234742286234441917031), (Int.ofNat 88194736470118432763704133258626), (Int.ofNat 11477903903207548519144953685885), (Int.negOfNat 2520854460750718616937617937182), (Int.negOfNat 207750785529766018160941733170), (Int.ofNat 37611754384373134757298784736), (Int.ofNat 2615491011151095745861377847), (Int.negOfNat 343373944613703296080959217), (Int.negOfNat 22342155771231566760274069), (Int.ofNat 2114015720115407948809299), (Int.ofNat 133598185843481636224401), (Int.negOfNat 9408660578753708938088), (Int.negOfNat 584881388862903646436), (Int.ofNat 31787932080219783905), (Int.ofNat 1947052152512702350), (Int.negOfNat 84304035183989613), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-797682929909532983752808356829519/1125899906842624000000000000000000), (-479855868621234742286234441917031/1125899906842624000000000000000000), (44097368235059216381852066629313/562949953421312000000000000000000), (2295580780641509703828990737177/225179981368524800000000000000000), (-1260427230375359308468808968591/562949953421312000000000000000000), (-20775078552976601816094173317/112589990684262400000000000000000), (1175367324511660461165587023/35184372088832000000000000000000), (2615491011151095745861377847/1125899906842624000000000000000000), (-343373944613703296080959217/1125899906842624000000000000000000), (-22342155771231566760274069/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial138.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial138.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial138.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial138.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial138.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial138.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial138.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial138.reflect := by
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

end Bin138
end
end ErdosOverlap.OuterNumerics
