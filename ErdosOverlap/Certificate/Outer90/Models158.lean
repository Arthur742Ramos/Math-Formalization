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

/-! # Exact integer weighted outer models for source bin 158

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin158

def weightDenominator : ℤ := (Int.ofNat 5000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 33053807079369945)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 797704222086142150)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 605621191096531850)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 237255194058346720)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 438707560779507800)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 353590920032851600)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 258056065979273725)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 200063097974975500)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 122300612714243485)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 68439823704861575)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial158.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial158.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 4622811902467260000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1834412001445173700)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 666913599727324500)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 578064147381005250)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 351527701961561000)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 164662552907197500)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 64892010824562035)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 18283762742182710)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 17117514276635212)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial158.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial158.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4622811902467260000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1834412001445173700)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 666913599727324500)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 578064147381005250)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 351527701961561000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 164662552907197500)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 64892010824562035)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 18283762742182710)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 17117514276635212)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial158.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial158.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial158.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 1457735659698002110986809287854126), (Int.ofNat 2266417374985477327563447256896099), (Int.ofNat 158322633688191397773586388296040), (Int.negOfNat 64867569937336134218409524971613), (Int.negOfNat 4823766304459395790933388187079), (Int.ofNat 1253315764216514620589833858458), (Int.ofNat 80807747458211916059027415303), (Int.negOfNat 15482574688197810789088708568), (Int.negOfNat 835078873624187208039703863), (Int.ofNat 129192182423968701265870979), (Int.ofNat 5815814020988450712277748), (Int.negOfNat 767694113713351466850503), (Int.negOfNat 29127195119060580902319), (Int.ofNat 3389166547543167150114), (Int.ofNat 110247933317218787840), (Int.negOfNat 11351990603721491010), (Int.negOfNat 343510882836557378), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-728867829849001055493404643927063/2814749767106560000000000000000000), (2266417374985477327563447256896099/5629499534213120000000000000000000), (3958065842204784944339659707401/140737488355328000000000000000000), (-64867569937336134218409524971613/5629499534213120000000000000000000), (-4823766304459395790933388187079/5629499534213120000000000000000000), (626657882108257310294916929229/2814749767106560000000000000000000), (80807747458211916059027415303/5629499534213120000000000000000000), (-1935321836024726348636088571/703687441776640000000000000000000), (-835078873624187208039703863/5629499534213120000000000000000000), (129192182423968701265870979/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial158.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial158.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial158.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial158 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 3155421494615413267862175045811897), (Int.ofNat 2075243845904431213255384107606258), (Int.negOfNat 238255507290445846801330053785113), (Int.negOfNat 49813321596988697978187102935222), (Int.ofNat 7851715465468622713861436879655), (Int.ofNat 831247242125427529419014448955), (Int.negOfNat 135393235344732108627197039567), (Int.negOfNat 9048275631526322164210423714), (Int.ofNat 1443764664746734193746362634), (Int.ofNat 67214394798196306612043649), (Int.negOfNat 10436873638898265096126513), (Int.negOfNat 359463453589467436366030), (Int.ofNat 54267718853203626340105), (Int.ofNat 1445610905908529724813), (Int.negOfNat 212249446912888585587), (Int.negOfNat 4474291577140025862), (Int.ofNat 688133198496998068), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(3155421494615413267862175045811897/5629499534213120000000000000000000), (1037621922952215606627692053803129/2814749767106560000000000000000000), (-238255507290445846801330053785113/5629499534213120000000000000000000), (-24906660798494348989093551467611/2814749767106560000000000000000000), (1570343093093724542772287375931/1125899906842624000000000000000000), (166249448425085505883802889791/1125899906842624000000000000000000), (-135393235344732108627197039567/5629499534213120000000000000000000), (-4524137815763161082105211857/2814749767106560000000000000000000), (721882332373367096873181317/2814749767106560000000000000000000), (67214394798196306612043649/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial158.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial158.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial158.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial158 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 6097177421869344495038165068316488), (Int.ofNat 813744679955841432606282831710580), (Int.negOfNat 317998892127741395743968079936863), (Int.ofNat 22299789262964876809373948227959), (Int.ofNat 7246827222044645111016182340165), (Int.negOfNat 860254978503717315599466434647), (Int.negOfNat 92223949886755856078133123446), (Int.ofNat 13250928633505822568473001853), (Int.ofNat 747561899700627979282078227), (Int.negOfNat 122610317148050824630698477), (Int.negOfNat 4200218609584020990974458), (Int.ofNat 770320660541126253166712), (Int.ofNat 17302909429826279118480), (Int.negOfNat 3512960742815501026455), (Int.negOfNat 54319092698744877855), (Int.ofNat 12140409452467397168), (Int.ofNat 121073897445337441), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(762147177733668061879770633539561/703687441776640000000000000000000), (40687233997792071630314141585529/281474976710656000000000000000000), (-317998892127741395743968079936863/5629499534213120000000000000000000), (22299789262964876809373948227959/5629499534213120000000000000000000), (1449365444408929022203236468033/1125899906842624000000000000000000), (-860254978503717315599466434647/5629499534213120000000000000000000), (-46111974943377928039066561723/2814749767106560000000000000000000), (13250928633505822568473001853/5629499534213120000000000000000000), (747561899700627979282078227/5629499534213120000000000000000000), (-122610317148050824630698477/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial158.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial158.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial158.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial158 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 6715410307244104709415980250369926), (Int.negOfNat 38875511012142502763474294051636), (Int.negOfNat 91577278719232202317040038348586), (Int.ofNat 39178299140946078215870770921553), (Int.negOfNat 2859022656158490977791465095154), (Int.negOfNat 776654306441070319705615086920), (Int.ofNat 92138605642058522827524206702), (Int.ofNat 7640025326719373067417550587), (Int.negOfNat 1206712627488601720235351937), (Int.negOfNat 46484639564042702140918736), (Int.ofNat 9560272740012684997367291), (Int.ofNat 189520005537087740986002), (Int.negOfNat 52053825926899102637708), (Int.negOfNat 532851181966331210499), (Int.ofNat 208425788144374827183), (Int.ofNat 860429688571980967), (Int.negOfNat 636780655667092432), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(3357705153622052354707990125184963/2814749767106560000000000000000000), (-9718877753035625690868573512909/1407374883553280000000000000000000), (-45788639359616101158520019174293/2814749767106560000000000000000000), (39178299140946078215870770921553/5629499534213120000000000000000000), (-1429511328079245488895732547577/2814749767106560000000000000000000), (-19416357661026757992640377173/140737488355328000000000000000000), (46069302821029261413762103351/2814749767106560000000000000000000), (7640025326719373067417550587/5629499534213120000000000000000000), (-1206712627488601720235351937/5629499534213120000000000000000000), (-2905289972752668883807421/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial158.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial158.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial158.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial158 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 6520731302288565267473350053553596), (Int.negOfNat 68845736879482001229554297598247), (Int.ofNat 37726305460070190440905393336698), (Int.ofNat 1997192451580283498027100062684), (Int.negOfNat 4367070548397031971766697471006), (Int.ofNat 413907217898520594003876550135), (Int.ofNat 64596286825119697475108340691), (Int.negOfNat 9470823600380550332058621583), (Int.negOfNat 467786747223542036825196321), (Int.ofNat 101475993591809524525850387), (Int.ofNat 1889568331684374408294479), (Int.negOfNat 681392720548489578983115), (Int.negOfNat 3497846942154089213519), (Int.ofNat 3211366075691468908245), (Int.negOfNat 5581427978741023069), (Int.negOfNat 11392434730631698519), (Int.ofNat 84245573669247284), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(1630182825572141316868337513388399/1407374883553280000000000000000000), (-68845736879482001229554297598247/5629499534213120000000000000000000), (18863152730035095220452696668349/2814749767106560000000000000000000), (499298112895070874506775015671/1407374883553280000000000000000000), (-2183535274198515985883348735503/2814749767106560000000000000000000), (82781443579704118800775310027/1125899906842624000000000000000000), (64596286825119697475108340691/5629499534213120000000000000000000), (-9470823600380550332058621583/5629499534213120000000000000000000), (-467786747223542036825196321/5629499534213120000000000000000000), (101475993591809524525850387/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial158.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial158.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial158.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial158 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 6496149142369269953117463969768797), (Int.ofNat 7308540477895226448290344005245), (Int.negOfNat 13216767822667993215737270036789), (Int.negOfNat 11643313879203786278184161055328), (Int.ofNat 878488069524945570982442836133), (Int.ofNat 384274885047482070527740096410), (Int.negOfNat 55453788905375069350591061368), (Int.negOfNat 3882760392923578672776462934), (Int.ofNat 894187406077365128458277670), (Int.ofNat 16229841484034273805156882), (Int.negOfNat 7750921142778896892669660), (Int.ofNat 4198459973224013534931), (Int.ofNat 44041928572529589433784), (Int.negOfNat 407772525263505668368), (Int.negOfNat 180254854543282743744), (Int.ofNat 2547961561873082838), (Int.ofNat 585428112837186796), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(6496149142369269953117463969768797/5629499534213120000000000000000000), (1461708095579045289658068801049/1125899906842624000000000000000000), (-13216767822667993215737270036789/5629499534213120000000000000000000), (-363853558725118321193255032979/175921860444160000000000000000000), (878488069524945570982442836133/5629499534213120000000000000000000), (38427488504748207052774009641/562949953421312000000000000000000), (-6931723613171883668823882671/703687441776640000000000000000000), (-1941380196461789336388231467/2814749767106560000000000000000000), (89418740607736512845827767/562949953421312000000000000000000), (8114920742017136902578441/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial158.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial158.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial158.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial158 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 6387288678146966781524216068403186), (Int.negOfNat 137896847522953913079077461737015), (Int.negOfNat 45578224929601082293715586233671), (Int.ofNat 1284106968107661597649580238967), (Int.ofNat 1275028250731335673693829337149), (Int.negOfNat 232228257208808642819425129470), (Int.negOfNat 22350948934552434491913767629), (Int.ofNat 6342019938914429092641019867), (Int.ofNat 97823040187644972434819192), (Int.negOfNat 75027659931269580082895475), (Int.ofNat 639739183880768487402930), (Int.ofNat 529781865714663152345648), (Int.negOfNat 9992725488350729531890), (Int.negOfNat 2558870015456245514213), (Int.ofNat 61325655457808200136), (Int.ofNat 9309898563252038794), (Int.negOfNat 289565044783832009), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(3193644339073483390762108034201593/2814749767106560000000000000000000), (-27579369504590782615815492347403/1125899906842624000000000000000000), (-45578224929601082293715586233671/5629499534213120000000000000000000), (1284106968107661597649580238967/5629499534213120000000000000000000), (1275028250731335673693829337149/5629499534213120000000000000000000), (-23222825720880864281942512947/562949953421312000000000000000000), (-22350948934552434491913767629/5629499534213120000000000000000000), (6342019938914429092641019867/5629499534213120000000000000000000), (12227880023455621554352399/703687441776640000000000000000000), (-3001106397250783203315819/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial158.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial158.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial158.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial158 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 5951793712743902942101782346862766), (Int.negOfNat 284091800160687059979627783458078), (Int.negOfNat 27102750128671266102787800876169), (Int.ofNat 1972922948739130975978487227814), (Int.negOfNat 776636262570302696335791804421), (Int.negOfNat 56085539827364539940069617671), (Int.ofNat 35871676247027859004220158364), (Int.ofNat 20391387286679046912137871), (Int.negOfNat 604527274333100060704338535), (Int.ofNat 13812862381347459403223680), (Int.ofNat 5482327286239750299702649), (Int.negOfNat 180997197867712000473502), (Int.negOfNat 31945831431901901990186), (Int.ofNat 1213393693945015701757), (Int.ofNat 131546385532513025594), (Int.negOfNat 5403426682531248453), (Int.negOfNat 465635746302419585), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(2975896856371951471050891173431383/2814749767106560000000000000000000), (-142045900080343529989813891729039/2814749767106560000000000000000000), (-27102750128671266102787800876169/5629499534213120000000000000000000), (986461474369565487989243613907/2814749767106560000000000000000000), (-776636262570302696335791804421/5629499534213120000000000000000000), (-56085539827364539940069617671/5629499534213120000000000000000000), (8967919061756964751055039591/1407374883553280000000000000000000), (20391387286679046912137871/5629499534213120000000000000000000), (-120905454866620012140867707/1125899906842624000000000000000000), (21582597470855405317537/8796093022208000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial158.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial158.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial158.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial158 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 5278917412877503210270888237393693), (Int.negOfNat 391832318883391714460135609837171), (Int.negOfNat 30731945588926691853194192265523), (Int.negOfNat 1668349291010876297122749351993), (Int.ofNat 261692312052044108857255748260), (Int.ofNat 169240690026741426025030257908), (Int.negOfNat 8060587198123862958977241756), (Int.negOfNat 3984810455825190026450264871), (Int.ofNat 208839522144653683293923415), (Int.ofNat 47568852701103729226088840), (Int.negOfNat 2714907370026937021305391), (Int.negOfNat 342064344168794366705988), (Int.ofNat 20510078302869275444044), (Int.ofNat 1664059065757279492233), (Int.negOfNat 102859398196696141356), (Int.negOfNat 6016171363145164017), (Int.ofNat 392209663640284735), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(5278917412877503210270888237393693/5629499534213120000000000000000000), (-391832318883391714460135609837171/5629499534213120000000000000000000), (-30731945588926691853194192265523/5629499534213120000000000000000000), (-1668349291010876297122749351993/5629499534213120000000000000000000), (13084615602602205442862787413/281474976710656000000000000000000), (42310172506685356506257564477/1407374883553280000000000000000000), (-2015146799530965739744310439/1407374883553280000000000000000000), (-3984810455825190026450264871/5629499534213120000000000000000000), (41767904428930736658784683/1125899906842624000000000000000000), (1189221317527593230652221/140737488355328000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial158.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial158.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial158.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial158 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 4367629477533844842591942007389294), (Int.negOfNat 515893434732639126586463169040494), (Int.negOfNat 24980365282132960167115298676434), (Int.ofNat 4250161828106156115538878870370), (Int.ofNat 732567425188087605001831698318), (Int.negOfNat 102250810650540453382698318655), (Int.negOfNat 21183014833583168198410836629), (Int.ofNat 2444326482136303222895222673), (Int.ofNat 332637902002339086209695862), (Int.negOfNat 34697353400496117002940845), (Int.negOfNat 3011686793210205750989520), (Int.ofNat 301447774802459345591242), (Int.ofNat 17523589791991990730900), (Int.negOfNat 1736667072683924420977), (Int.negOfNat 71357787291760672664), (Int.ofNat 7163733690304911776), (Int.ofNat 294521070339426011), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(2183814738766922421295971003694647/2814749767106560000000000000000000), (-257946717366319563293231584520247/2814749767106560000000000000000000), (-12490182641066480083557649338217/2814749767106560000000000000000000), (425016182810615611553887887037/562949953421312000000000000000000), (366283712594043802500915849159/2814749767106560000000000000000000), (-20450162130108090676539663731/1125899906842624000000000000000000), (-21183014833583168198410836629/5629499534213120000000000000000000), (2444326482136303222895222673/5629499534213120000000000000000000), (166318951001169543104847931/2814749767106560000000000000000000), (-6939470680099223400588169/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial158.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial158.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial158.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial158 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 3277393635547366079853483707436607), (Int.negOfNat 552273955742803007847018015211865), (Int.ofNat 6891705434126130312129304270514), (Int.ofNat 4377663029544938713177056616878), (Int.negOfNat 670066727873831269044551367860), (Int.negOfNat 86270436504538733936251705875), (Int.ofNat 21932996867052308589154691872), (Int.ofNat 1705049363302425429871683014), (Int.negOfNat 376298648245748047840607710), (Int.negOfNat 19766761530022483229256172), (Int.ofNat 3864996441268053226552540), (Int.ofNat 139360474044552014159029), (Int.negOfNat 26010961511399921748636), (Int.negOfNat 653245065722745792672), (Int.ofNat 122819234239745389206), (Int.ofNat 2175046507006113732), (Int.negOfNat 409296944515240674), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(3277393635547366079853483707436607/5629499534213120000000000000000000), (-110454791148560601569403603042373/1125899906842624000000000000000000), (3445852717063065156064652135257/2814749767106560000000000000000000), (2188831514772469356588528308439/2814749767106560000000000000000000), (-33503336393691563452227568393/281474976710656000000000000000000), (-690163492036309871490013647/45035996273704960000000000000000), (685406152095384643411084121/175921860444160000000000000000000), (852524681651212714935841507/2814749767106560000000000000000000), (-37629864824574804784060771/562949953421312000000000000000000), (-4941690382505620807314043/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial158.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial158.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial158.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial158 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 2223471766829661066162472877740661), (Int.negOfNat 495954123901376628663611436964972), (Int.ofNat 15865380837219434842889722351855), (Int.negOfNat 687949155822757136328537400625), (Int.negOfNat 186106068884968373834844262183), (Int.ofNat 144282450038656885188514770547), (Int.ofNat 3836319495055721469809244256), (Int.negOfNat 3391949842850746893017034577), (Int.negOfNat 61408289840529183685369551), (Int.ofNat 42866711829258512260126823), (Int.ofNat 524289410190157422868159), (Int.negOfNat 343147092958771512967645), (Int.negOfNat 2558665632495270222239), (Int.ofNat 1885044252613014883995), (Int.ofNat 7301815071842760731), (Int.negOfNat 7534518430021050301), (Int.negOfNat 89201599224841286), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(2223471766829661066162472877740661/5629499534213120000000000000000000), (-123988530975344157165902859241243/1407374883553280000000000000000000), (3173076167443886968577944470371/1125899906842624000000000000000000), (-1100718649316411418125659841/9007199254740992000000000000000), (-186106068884968373834844262183/5629499534213120000000000000000000), (144282450038656885188514770547/5629499534213120000000000000000000), (119884984220491295931538883/175921860444160000000000000000000), (-3391949842850746893017034577/5629499534213120000000000000000000), (-61408289840529183685369551/5629499534213120000000000000000000), (42866711829258512260126823/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial158.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial158.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial158.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial158 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 1290978211480380102291075894750273), (Int.negOfNat 435909070308562086079535967249497), (Int.ofNat 17539050198628200318670685740087), (Int.ofNat 2423041468036829550473758154221), (Int.ofNat 634117688399803241271123688499), (Int.negOfNat 41268774769414449326037481325), (Int.negOfNat 24784103977040263016900869570), (Int.ofNat 623243468654023090253944943), (Int.ofNat 404444147730940247827775433), (Int.negOfNat 6894005385526423525503514), (Int.negOfNat 3943607157358127937433209), (Int.ofNat 56250281264043116385308), (Int.ofNat 25611438216720156350122), (Int.negOfNat 337681281358933836311), (Int.negOfNat 118299680942954168617), (Int.ofNat 1534303907854426263), (Int.ofNat 357944401685335038), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(1290978211480380102291075894750273/5629499534213120000000000000000000), (-435909070308562086079535967249497/5629499534213120000000000000000000), (17539050198628200318670685740087/5629499534213120000000000000000000), (2423041468036829550473758154221/5629499534213120000000000000000000), (634117688399803241271123688499/5629499534213120000000000000000000), (-1650750990776577973041499253/225179981368524800000000000000000), (-2478410397704026301690086957/562949953421312000000000000000000), (623243468654023090253944943/5629499534213120000000000000000000), (404444147730940247827775433/5629499534213120000000000000000000), (-3447002692763211762751757/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial158.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial158.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial158.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial158 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 516115663318432372636984636584411), (Int.negOfNat 323786134978517747763680072859831), (Int.ofNat 39116041018384576007819085147353), (Int.ofNat 2860997810776381646102457911045), (Int.negOfNat 713545912646811627107892232689), (Int.negOfNat 146799194732875109958241945720), (Int.ofNat 13543681424767977259186938134), (Int.ofNat 3177440869970892797557426417), (Int.negOfNat 186591370513517247441203553), (Int.negOfNat 38738893045380668912257623), (Int.ofNat 1716982572034445153522162), (Int.ofNat 302822661139998848843998), (Int.negOfNat 11030578900734427214540), (Int.negOfNat 1639491571001643145885), (Int.ofNat 51763033582123895395), (Int.ofNat 6502271667086686902), (Int.negOfNat 116117871889743439), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(516115663318432372636984636584411/5629499534213120000000000000000000), (-323786134978517747763680072859831/5629499534213120000000000000000000), (39116041018384576007819085147353/5629499534213120000000000000000000), (572199562155276329220491582209/1125899906842624000000000000000000), (-713545912646811627107892232689/5629499534213120000000000000000000), (-3669979868321877748956048643/140737488355328000000000000000000), (6771840712383988629593469067/2814749767106560000000000000000000), (3177440869970892797557426417/5629499534213120000000000000000000), (-186591370513517247441203553/5629499534213120000000000000000000), (-38738893045380668912257623/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial158.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial158.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial158.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial158 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 32989458226255532212255369031194), (Int.negOfNat 163811994644072732617356674132968), (Int.ofNat 32313157743173373515645468623870), (Int.negOfNat 5278122440349751794585951741686), (Int.negOfNat 810472276730737230322468282658), (Int.ofNat 142151444385539840078866450875), (Int.ofNat 20385025473253129717670038553), (Int.negOfNat 2566877217847839807970533456), (Int.negOfNat 315538700639357085345603676), (Int.ofNat 29066612917171078715871401), (Int.ofNat 3031984849078612848924227), (Int.negOfNat 219468649122324972544550), (Int.negOfNat 19571353467490401642085), (Int.ofNat 1172752252842089352797), (Int.ofNat 90063855339950987563), (Int.negOfNat 4764424389772538868), (Int.negOfNat 306591858855429402), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(16494729113127766106127684515597/2814749767106560000000000000000000), (-20476499330509091577169584266621/703687441776640000000000000000000), (3231315774317337351564546862387/562949953421312000000000000000000), (-2639061220174875897292975870843/2814749767106560000000000000000000), (-405236138365368615161234141329/2814749767106560000000000000000000), (1137211555084318720630931607/45035996273704960000000000000000), (20385025473253129717670038553/5629499534213120000000000000000000), (-160429826115489987998158341/351843720888320000000000000000000), (-78884675159839271336400919/1407374883553280000000000000000000), (29066612917171078715871401/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial158.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial158.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial158.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial158 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 215112818241168005559256670542883), (Int.negOfNat 109939366313858130579670426401015), (Int.negOfNat 4671195773381610245444445808776), (Int.negOfNat 4625375980912792647333765035195), (Int.ofNat 908717672118698561435089789472), (Int.ofNat 104829949401006253160920604349), (Int.negOfNat 25260362522907957554676212517), (Int.negOfNat 2014682357689862669130648092), (Int.ofNat 369726194292164584539862327), (Int.ofNat 24340675896652615714796061), (Int.negOfNat 3396967389773834611568852), (Int.negOfNat 191523813858381318664577), (Int.ofNat 21328645539764087053741), (Int.ofNat 1048386220532337336576), (Int.negOfNat 96814306838112628360), (Int.negOfNat 4268825526539465310), (Int.ofNat 304319828727692952), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-215112818241168005559256670542883/5629499534213120000000000000000000), (-21987873262771626115934085280203/1125899906842624000000000000000000), (-583899471672701280680555726097/703687441776640000000000000000000), (-925075196182558529466753007039/1125899906842624000000000000000000), (28397427253709330044846555921/175921860444160000000000000000000), (104829949401006253160920604349/5629499534213120000000000000000000), (-25260362522907957554676212517/5629499534213120000000000000000000), (-503670589422465667282662023/1407374883553280000000000000000000), (369726194292164584539862327/5629499534213120000000000000000000), (24340675896652615714796061/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial158.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial158.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial158.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial158 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 474556507376367849724137011792756), (Int.negOfNat 152000168256539774469276584875393), (Int.negOfNat 8912430459352510921503256485913), (Int.ofNat 2403451658621449231861374178101), (Int.ofNat 338752158114055715989161496063), (Int.negOfNat 183477171268000201050108455938), (Int.negOfNat 8535709870026802676456741453), (Int.ofNat 3741981133977078394316682798), (Int.ofNat 134814002402386091715605513), (Int.negOfNat 43214248038483156042044719), (Int.negOfNat 1345468193204205327224748), (Int.ofNat 326134134550047643217853), (Int.ofNat 9057299352429368824769), (Int.negOfNat 1728379948205544105784), (Int.negOfNat 43462001834088855190), (Int.ofNat 6853290589115852770), (Int.ofNat 135477182892435828), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-118639126844091962431034252948189/1407374883553280000000000000000000), (-152000168256539774469276584875393/5629499534213120000000000000000000), (-8912430459352510921503256485913/5629499534213120000000000000000000), (2403451658621449231861374178101/5629499534213120000000000000000000), (338752158114055715989161496063/5629499534213120000000000000000000), (-91738585634000100525054227969/2814749767106560000000000000000000), (-8535709870026802676456741453/5629499534213120000000000000000000), (1870990566988539197158341399/2814749767106560000000000000000000), (134814002402386091715605513/5629499534213120000000000000000000), (-43214248038483156042044719/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial158.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial158.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial158.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial158 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 795485799947088192927035105252823), (Int.negOfNat 162573627605996371308563289161463), (Int.negOfNat 537336050423339899269697502769), (Int.negOfNat 1492950994967549785456493387367), (Int.negOfNat 987472715351609418240730185631), (Int.ofNat 816555547462250949391203430), (Int.ofNat 30352627036009301691836851847), (Int.ofNat 138752445127529555404953914), (Int.negOfNat 456713622303380527182042914), (Int.negOfNat 2728778302306187041480899), (Int.ofNat 4246599966251135949774173), (Int.ofNat 30276518350116733727680), (Int.negOfNat 26762019999271670939845), (Int.negOfNat 211814358488952878713), (Int.ofNat 121420309019472089787), (Int.ofNat 1145752378034081062), (Int.negOfNat 406964447584145678), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-795485799947088192927035105252823/5629499534213120000000000000000000), (-162573627605996371308563289161463/5629499534213120000000000000000000), (-537336050423339899269697502769/5629499534213120000000000000000000), (-1492950994967549785456493387367/5629499534213120000000000000000000), (-987472715351609418240730185631/5629499534213120000000000000000000), (81655554746225094939120343/562949953421312000000000000000000), (30352627036009301691836851847/5629499534213120000000000000000000), (69376222563764777702476957/2814749767106560000000000000000000), (-228356811151690263591021457/2814749767106560000000000000000000), (-2728778302306187041480899/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial158.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial158.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial158.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial158 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 1148653127195556338246484559940008), (Int.negOfNat 208734853941208219997102258038036), (Int.negOfNat 26534219376316191421664346542193), (Int.negOfNat 5195528810508933433756173249808), (Int.ofNat 413188071280053802874852646873), (Int.ofNat 199075248330937741525415917242), (Int.negOfNat 7510889166411665881233175554), (Int.negOfNat 3973946944602332939370992483), (Int.ofNat 100652091634498689409726073), (Int.ofNat 46840406209634219878106167), (Int.negOfNat 804391344834969352260592), (Int.negOfNat 358749073199937376235362), (Int.ofNat 4129324165384825368770), (Int.ofNat 1917055495379448438775), (Int.negOfNat 14958901551229972245), (Int.negOfNat 7641709437861758928), (Int.ofNat 86959802498784109), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-143581640899444542280810569992501/703687441776640000000000000000000), (-52183713485302054999275564509509/1407374883553280000000000000000000), (-26534219376316191421664346542193/5629499534213120000000000000000000), (-324720550656808339609760828113/351843720888320000000000000000000), (413188071280053802874852646873/5629499534213120000000000000000000), (99537624165468870762707958621/2814749767106560000000000000000000), (-3755444583205832940616587777/2814749767106560000000000000000000), (-3973946944602332939370992483/5629499534213120000000000000000000), (100652091634498689409726073/5629499534213120000000000000000000), (46840406209634219878106167/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial158.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial158.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial158.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial158 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 1701783665148581321333648730203074), (Int.negOfNat 351089429283638892564483713888318), (Int.negOfNat 35960550639685886995030613305976), (Int.ofNat 3051508807833914316320626440388), (Int.ofNat 1117398156778869187773716689387), (Int.negOfNat 101425617257778940816072998335), (Int.negOfNat 27767213523830720859093249257), (Int.ofNat 2012138827556567272666360513), (Int.ofNat 428487307534480960087766017), (Int.negOfNat 22130639000328888210677914), (Int.negOfNat 4105515474064929271069751), (Int.ofNat 153373251943277145763348), (Int.ofNat 26401100609177670271698), (Int.negOfNat 733065240771768754351), (Int.negOfNat 121022648148524011083), (Int.ofNat 2468109510533963833), (Int.ofNat 355611904754240042), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-850891832574290660666824365101537/2814749767106560000000000000000000), (-175544714641819446282241856944159/2814749767106560000000000000000000), (-4495068829960735874378826663247/703687441776640000000000000000000), (762877201958478579080156610097/1407374883553280000000000000000000), (1117398156778869187773716689387/5629499534213120000000000000000000), (-20285123451555788163214599667/1125899906842624000000000000000000), (-27767213523830720859093249257/5629499534213120000000000000000000), (2012138827556567272666360513/5629499534213120000000000000000000), (428487307534480960087766017/5629499534213120000000000000000000), (-11065319500164444105338957/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial158.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial158.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial158.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial158 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 2510184880768622809356440695498051), (Int.negOfNat 434731615206617921961518958606669), (Int.negOfNat 3635445640888531796515549147591), (Int.ofNat 5212681025528486440884876594402), (Int.negOfNat 654553515330777603248102701199), (Int.negOfNat 144515478765390645652137396292), (Int.ofNat 23311239056802966469699434009), (Int.ofNat 3091445824830435547331475363), (Int.negOfNat 347445441704859576521271329), (Int.negOfNat 38823050293739374096600627), (Int.ofNat 3051011927685013185808571), (Int.ofNat 309967492772393227447565), (Int.negOfNat 17838526745207820047831), (Int.negOfNat 1703173568491023667015), (Int.ofNat 74441599229953658369), (Int.ofNat 6893734716026060279), (Int.negOfNat 292279273613368834), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-2510184880768622809356440695498051/5629499534213120000000000000000000), (-434731615206617921961518958606669/5629499534213120000000000000000000), (-3635445640888531796515549147591/5629499534213120000000000000000000), (2606340512764243220442438297201/2814749767106560000000000000000000), (-654553515330777603248102701199/5629499534213120000000000000000000), (-36128869691347661413034349073/1407374883553280000000000000000000), (23311239056802966469699434009/5629499534213120000000000000000000), (3091445824830435547331475363/5629499534213120000000000000000000), (-347445441704859576521271329/5629499534213120000000000000000000), (-38823050293739374096600627/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial158.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial158.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial158.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial158 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 3365803322716396512688992577585027), (Int.negOfNat 413794089406943269015938498363615), (Int.ofNat 7283179779850894545106815625345), (Int.negOfNat 1117177785132068646052654624802), (Int.negOfNat 329794488701366052280152171574), (Int.ofNat 192471830046055227469592810307), (Int.ofNat 15065907463498847183522627648), (Int.negOfNat 4089477369885007708173615416), (Int.negOfNat 280387036422828771194455550), (Int.ofNat 46020039084753199195665068), (Int.ofNat 2950911006482460905584270), (Int.negOfNat 329424684779028845532381), (Int.negOfNat 20132850825252283704474), (Int.ofNat 1636254744241554665568), (Int.ofNat 96562788604338092444), (Int.negOfNat 5876500760979027638), (Int.negOfNat 304259361924334406), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-3365803322716396512688992577585027/5629499534213120000000000000000000), (-82758817881388653803187699672723/1125899906842624000000000000000000), (1456635955970178909021363125069/1125899906842624000000000000000000), (-558588892566034323026327312401/2814749767106560000000000000000000), (-164897244350683026140076085787/2814749767106560000000000000000000), (192471830046055227469592810307/5629499534213120000000000000000000), (235404804117169487242541057/87960930222080000000000000000000), (-511184671235625963521701927/703687441776640000000000000000000), (-5607740728456575423889111/112589990684262400000000000000000), (11505009771188299798916267/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial158.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial158.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial158.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial158 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 4171918990424981176431458884100033), (Int.negOfNat 392332698952341452300826322839996), (Int.ofNat 8663736272432137091197284942970), (Int.ofNat 3838409312868257013461731160766), (Int.ofNat 1249216791944127777968751761350), (Int.ofNat 9541164529648590554658386537), (Int.negOfNat 38394618719758650775695374121), (Int.negOfNat 1154992472404790881677553697), (Int.ofNat 564929648967382228162102208), (Int.ofNat 19726288791646232755202765), (Int.negOfNat 5024951806824250704917630), (Int.negOfNat 183730895260580225409848), (Int.ofNat 29909051683151941769390), (Int.ofNat 1108355182110560933033), (Int.negOfNat 127418479023083945736), (Int.negOfNat 4811198548646400554), (Int.ofNat 497598744727953559), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-4171918990424981176431458884100033/5629499534213120000000000000000000), (-98083174738085363075206580709999/1407374883553280000000000000000000), (866373627243213709119728494297/562949953421312000000000000000000), (1919204656434128506730865580383/2814749767106560000000000000000000), (24984335838882555559375035227/112589990684262400000000000000000), (9541164529648590554658386537/5629499534213120000000000000000000), (-38394618719758650775695374121/5629499534213120000000000000000000), (-1154992472404790881677553697/5629499534213120000000000000000000), (8827025765115347315032847/87960930222080000000000000000000), (3945257758329246551040553/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial158.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial158.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial158.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial158 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 4873385148039258254882254191144579), (Int.negOfNat 278170896450530774878142002151071), (Int.ofNat 53490164048088284755633571607090), (Int.ofNat 8460905753469907937988293586433), (Int.negOfNat 641429681166100354800334999968), (Int.negOfNat 298054525455800927691625227344), (Int.ofNat 4269383417964421254735381681), (Int.ofNat 5749064476681178173333529329), (Int.ofNat 28635575170620923801923815), (Int.negOfNat 64880285240079864089082730), (Int.negOfNat 894300311969591197997359), (Int.ofNat 470256416363229214555552), (Int.ofNat 8672567743516741730776), (Int.negOfNat 2360965835550634943507), (Int.negOfNat 49314158096496196844), (Int.ofNat 8731965881637193253), (Int.ofNat 184466995389567195), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-4873385148039258254882254191144579/5629499534213120000000000000000000), (-278170896450530774878142002151071/5629499534213120000000000000000000), (5349016404808828475563357160709/562949953421312000000000000000000), (8460905753469907937988293586433/5629499534213120000000000000000000), (-20044677536440636087510468749/175921860444160000000000000000000), (-18628407840987557980726576709/351843720888320000000000000000000), (4269383417964421254735381681/5629499534213120000000000000000000), (5749064476681178173333529329/5629499534213120000000000000000000), (5727115034124184760384763/1125899906842624000000000000000000), (-6488028524007986408908273/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial158.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial158.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial158.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial158 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 5166896362656258909635430523091145), (Int.negOfNat 3773539807261559795215412711920), (Int.ofNat 69660432443338973669452081790367), (Int.negOfNat 4981224266433502333788568503700), (Int.negOfNat 1977545981276699308206870572576), (Int.ofNat 124900824862141733421901095252), (Int.ofNat 48290758765865223327236068356), (Int.negOfNat 1557401248760189489740152049), (Int.negOfNat 710026372176891225621057765), (Int.ofNat 8682488963664619331941920), (Int.ofNat 6417153387785224656733241), (Int.negOfNat 5801790910034708773912), (Int.negOfNat 38560120937581289227694), (Int.negOfNat 211682348405579672603), (Int.ofNat 165054360678921569706), (Int.ofNat 1517471348539525777), (Int.negOfNat 600243363584406285), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-1033379272531251781927086104618229/1125899906842624000000000000000000), (-47169247590769497440192658899/70368744177664000000000000000000), (69660432443338973669452081790367/5629499534213120000000000000000000), (-49812242664335023337885685037/56294995342131200000000000000000), (-61798311914896853381464705393/175921860444160000000000000000000), (31225206215535433355475273813/1407374883553280000000000000000000), (12072689691466305831809017089/1407374883553280000000000000000000), (-1557401248760189489740152049/5629499534213120000000000000000000), (-142005274435378245124211553/1125899906842624000000000000000000), (54265556022903870824637/35184372088832000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial158.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial158.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial158.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial158 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 4960575073718856446170185577248382), (Int.ofNat 169702991330294754298458356931133), (Int.ofNat 11686083618050237357277487958757), (Int.negOfNat 10082832066695152896880486388782), (Int.ofNat 1053820935509440891366994714398), (Int.ofNat 320747066661795182530189459207), (Int.negOfNat 27925629458669143506194295041), (Int.negOfNat 6466307529938550508347903173), (Int.ofNat 310803264127346760041655158), (Int.ofNat 75747037335843772673390545), (Int.negOfNat 1855856719875582959369770), (Int.negOfNat 556767180942708898271142), (Int.ofNat 6506579849423666579360), (Int.ofNat 2806310211689226435277), (Int.negOfNat 12137700380791313336), (Int.negOfNat 10492272889410856576), (Int.negOfNat 13352319426573621), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-2480287536859428223085092788624191/2814749767106560000000000000000000), (169702991330294754298458356931133/5629499534213120000000000000000000), (11686083618050237357277487958757/5629499534213120000000000000000000), (-5041416033347576448440243194391/2814749767106560000000000000000000), (526910467754720445683497357199/2814749767106560000000000000000000), (320747066661795182530189459207/5629499534213120000000000000000000), (-27925629458669143506194295041/5629499534213120000000000000000000), (-6466307529938550508347903173/5629499534213120000000000000000000), (155401632063673380020827579/2814749767106560000000000000000000), (15149407467168754534678109/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial158.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial158.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial158.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial158 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 4630461943102686152059036715869367), (Int.ofNat 147054065355180848220408132559895), (Int.negOfNat 8037132307217206339044557228945), (Int.ofNat 4002063464758826345363532446837), (Int.ofNat 1382049688140779881043733047888), (Int.negOfNat 295472106899932234737405251420), (Int.negOfNat 46243013495330108168965958172), (Int.ofNat 5143952710865813924696000756), (Int.ofNat 761821612144166864016672010), (Int.negOfNat 44234654504961373260974838), (Int.negOfNat 7088697564121936551415190), (Int.ofNat 235059307745146423655821), (Int.ofNat 42763636723569521453186), (Int.negOfNat 859945916697882431408), (Int.negOfNat 182522133955125900106), (Int.ofNat 2323653507599524508), (Int.ofNat 617330644459362224), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-4630461943102686152059036715869367/5629499534213120000000000000000000), (29410813071036169644081626511979/1125899906842624000000000000000000), (-1607426461443441267808911445789/1125899906842624000000000000000000), (4002063464758826345363532446837/5629499534213120000000000000000000), (86378105508798742565233315493/351843720888320000000000000000000), (-14773605344996611736870262571/281474976710656000000000000000000), (-11560753373832527042241489543/1407374883553280000000000000000000), (1285988177716453481174000189/1407374883553280000000000000000000), (76182161214416686401667201/562949953421312000000000000000000), (-22117327252480686630487419/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial158.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial158.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial158.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial158 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 4325963507230349430842166241151759), (Int.ofNat 177589478735723136672014862243946), (Int.ofNat 18954081683619313755551504380273), (Int.negOfNat 245830939072988555216928298004), (Int.negOfNat 2312475086159746704910984912907), (Int.negOfNat 212513658246980981818597581164), (Int.ofNat 63237665296986849840976799602), (Int.ofNat 6315357375493064504934814927), (Int.negOfNat 728247668519436822744702419), (Int.negOfNat 79049127400563939895455123), (Int.ofNat 4971400583083369886142731), (Int.ofNat 583740418412256843945095), (Int.negOfNat 23199842910827418730871), (Int.negOfNat 2923124942646199769345), (Int.ofNat 79619670498274904969), (Int.ofNat 10863057629126995101), (Int.negOfNat 191967151688011104), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-4325963507230349430842166241151759/5629499534213120000000000000000000), (88794739367861568336007431121973/2814749767106560000000000000000000), (18954081683619313755551504380273/5629499534213120000000000000000000), (-61457734768247138804232074501/1407374883553280000000000000000000), (-2312475086159746704910984912907/5629499534213120000000000000000000), (-53128414561745245454649395291/1407374883553280000000000000000000), (31618832648493424920488399801/2814749767106560000000000000000000), (6315357375493064504934814927/5629499534213120000000000000000000), (-728247668519436822744702419/5629499534213120000000000000000000), (-79049127400563939895455123/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial158.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial158.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial158.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial158 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 3936100068327958225775114384444510), (Int.ofNat 173529910497212509853432185596568), (Int.negOfNat 37198004795318495226568192616022), (Int.negOfNat 15223912407728114794761699118920), (Int.ofNat 78157488866277494022199241893), (Int.ofNat 645357089023969742983070375185), (Int.ofNat 40374332507755032864419170770), (Int.negOfNat 9723002860807509261443910013), (Int.negOfNat 766718071579134084429789683), (Int.ofNat 82603841904822277419297524), (Int.ofNat 7135234522694871794591609), (Int.negOfNat 468825325566046805495708), (Int.negOfNat 42348716934749203644372), (Int.ofNat 1938027577668763417041), (Int.ofNat 178420403657096894317), (Int.negOfNat 6033003922460064503), (Int.negOfNat 565978101629456588), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-393610006832795822577511438444451/562949953421312000000000000000000), (21691238812151563731679023199571/703687441776640000000000000000000), (-18599002397659247613284096308011/2814749767106560000000000000000000), (-380597810193202869869042477973/140737488355328000000000000000000), (78157488866277494022199241893/5629499534213120000000000000000000), (129071417804793948596614075037/1125899906842624000000000000000000), (4037433250775503286441917077/562949953421312000000000000000000), (-9723002860807509261443910013/5629499534213120000000000000000000), (-766718071579134084429789683/5629499534213120000000000000000000), (20650960476205569354824381/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial158.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial158.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial158.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial158 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 3836530001423359173538313731791541), (Int.negOfNat 100987951649706742275499680358505), (Int.negOfNat 72807967345755701568749053464429), (Int.ofNat 11386472710056553810156367983094), (Int.ofNat 5777681214155069811829334024141), (Int.ofNat 176337553879016673359644045722), (Int.negOfNat 111028479680518096896564379854), (Int.negOfNat 6516233887833637188728658167), (Int.ofNat 1157666722966860044839109923), (Int.ofNat 78563012136447407177503473), (Int.negOfNat 7896021231859581560275952), (Int.negOfNat 557253341675000017178648), (Int.ofNat 38565374692447173726550), (Int.ofNat 2710939377962236946685), (Int.negOfNat 142395593209147725895), (Int.negOfNat 9830810866192631702), (Int.ofNat 397286622802595829), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-3836530001423359173538313731791541/5629499534213120000000000000000000), (-20197590329941348455099936071701/1125899906842624000000000000000000), (-72807967345755701568749053464429/5629499534213120000000000000000000), (5693236355028276905078183991547/2814749767106560000000000000000000), (5777681214155069811829334024141/5629499534213120000000000000000000), (88168776939508336679822022861/2814749767106560000000000000000000), (-55514239840259048448282189927/2814749767106560000000000000000000), (-6516233887833637188728658167/5629499534213120000000000000000000), (1157666722966860044839109923/5629499534213120000000000000000000), (78563012136447407177503473/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial158.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial158.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial158.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial158 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 4148172654203201540217964098108793), (Int.negOfNat 79505257226923030245561357841822), (Int.ofNat 119589359627635494381649139405612), (Int.ofNat 45604864773701896723338642696452), (Int.ofNat 544203998405299442063437080624), (Int.negOfNat 1101869471253612372589532579647), (Int.negOfNat 51826276927528056043692917503), (Int.ofNat 13996399068835478468504174026), (Int.ofNat 798268484250748218138226426), (Int.negOfNat 114567440276005163069737011), (Int.negOfNat 6723455098107901900584477), (Int.ofNat 660842400297339029579600), (Int.ofNat 37663709272042667629585), (Int.negOfNat 2834843309839321645777), (Int.negOfNat 152951925740030602963), (Int.ofNat 9263124404378177108), (Int.ofNat 514625558799550952), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-4148172654203201540217964098108793/5629499534213120000000000000000000), (-39752628613461515122780678920911/2814749767106560000000000000000000), (29897339906908873595412284851403/1407374883553280000000000000000000), (11401216193425474180834660674113/1407374883553280000000000000000000), (34012749900331215128964817539/351843720888320000000000000000000), (-1101869471253612372589532579647/5629499534213120000000000000000000), (-51826276927528056043692917503/5629499534213120000000000000000000), (6998199534417739234252087013/2814749767106560000000000000000000), (399134242125374109069113213/2814749767106560000000000000000000), (-114567440276005163069737011/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial158.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial158.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial158.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial158 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 3491924418042643076968588785572932), (Int.ofNat 872222513248881510289034419185331), (Int.ofNat 315942930154143030221454249087884), (Int.ofNat 6172038826922627893842735137133), (Int.negOfNat 9291792739610416891695836823706), (Int.negOfNat 453349374176983550231931628664), (Int.ofNat 145233351288918354853213501699), (Int.ofNat 7899389966022939436163988242), (Int.negOfNat 1440775277250559314689706547), (Int.negOfNat 76072536983565099788830011), (Int.ofNat 9894946635511107508109592), (Int.ofNat 482933386073935887592027), (Int.negOfNat 49623890024672470427051), (Int.negOfNat 2200186678518954903026), (Int.ofNat 188906704968064281410), (Int.ofNat 7597364725645410110), (Int.negOfNat 585488579640545342), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-872981104510660769242147196393233/1407374883553280000000000000000000), (872222513248881510289034419185331/5629499534213120000000000000000000), (78985732538535757555363562271971/1407374883553280000000000000000000), (6172038826922627893842735137133/5629499534213120000000000000000000), (-4645896369805208445847918411853/2814749767106560000000000000000000), (-56668671772122943778991453583/703687441776640000000000000000000), (145233351288918354853213501699/5629499534213120000000000000000000), (3949694983011469718081994121/2814749767106560000000000000000000), (-1440775277250559314689706547/5629499534213120000000000000000000), (-76072536983565099788830011/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial158.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial158.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial158.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial158.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial158 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial158 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial158 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 4948744759219392628049364524694024), (Int.negOfNat 1088005739232727146752965007000569), (Int.ofNat 359284928152243418655969927043920), (Int.negOfNat 4329121729641348876770134868537), (Int.negOfNat 9523727312600241566889428254141), (Int.ofNat 448019593871319849621251321332), (Int.ofNat 145752251852810035038020145837), (Int.negOfNat 7891385266856845743134406692), (Int.negOfNat 1441411887430411843779244497), (Int.ofNat 76065148510427121005169411), (Int.ofNat 9895437735552890540038042), (Int.negOfNat 482928541104407115337227), (Int.negOfNat 49623890024672470427051), (Int.ofNat 2200186678518954903026), (Int.ofNat 188906704968064281410), (Int.negOfNat 7597364725645410110), (Int.negOfNat 585488579640545342), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-618593094902424078506170565586753/703687441776640000000000000000000), (-1088005739232727146752965007000569/5629499534213120000000000000000000), (4491061601903042733199624088049/70368744177664000000000000000000), (-4329121729641348876770134868537/5629499534213120000000000000000000), (-9523727312600241566889428254141/5629499534213120000000000000000000), (112004898467829962405312830333/1407374883553280000000000000000000), (145752251852810035038020145837/5629499534213120000000000000000000), (-1972846316714211435783601673/1407374883553280000000000000000000), (-1441411887430411843779244497/5629499534213120000000000000000000), (76065148510427121005169411/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial158.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial158.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial158.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 5852295556720423622669238162557747), (Int.ofNat 51459288306574748437634027012612), (Int.ofNat 168124794249721832394618399265073), (Int.negOfNat 45744281561097575058891699635578), (Int.ofNat 291610946275109479087032121375), (Int.ofNat 1103142869449373013950514639155), (Int.negOfNat 51269871854187758433992927303), (Int.negOfNat 13999154600728738582995959876), (Int.ofNat 797591318122356849428252526), (Int.ofNat 114570421154249547774337661), (Int.negOfNat 6722934351999853266296327), (Int.negOfNat 660844217160912319175150), (Int.ofNat 37663709272042667629585), (Int.ofNat 2834843309839321645777), (Int.negOfNat 152951925740030602963), (Int.negOfNat 9263124404378177108), (Int.ofNat 514625558799550952), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-5852295556720423622669238162557747/5629499534213120000000000000000000), (12864822076643687109408506753153/1407374883553280000000000000000000), (168124794249721832394618399265073/5629499534213120000000000000000000), (-22872140780548787529445849817789/2814749767106560000000000000000000), (2332887570200875832696256971/45035996273704960000000000000000), (220628573889874602790102927831/1125899906842624000000000000000000), (-51269871854187758433992927303/5629499534213120000000000000000000), (-3499788650182184645748989969/1407374883553280000000000000000000), (398795659061178424714126263/2814749767106560000000000000000000), (114570421154249547774337661/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial158.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial158.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial158.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 5407684091767694121782489014642348), (Int.ofNat 257534525338781255510488516248430), (Int.negOfNat 30938903165147332058567036399007), (Int.negOfNat 13409405845629464890910970456179), (Int.ofNat 5569695372741693083431341011435), (Int.negOfNat 168912007206367108485621857643), (Int.negOfNat 110582787009476421058638331254), (Int.ofNat 6503555607170473827511313617), (Int.ofNat 1157132217065321905931687323), (Int.negOfNat 78550519079932403375412323), (Int.negOfNat 7895612747127014901691302), (Int.ofNat 557245468599515762264598), (Int.ofNat 38565374692447173726550), (Int.negOfNat 2710939377962236946685), (Int.negOfNat 142395593209147725895), (Int.ofNat 9830810866192631702), (Int.ofNat 397286622802595829), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-1351921022941923530445622253660587/1407374883553280000000000000000000), (25753452533878125551048851624843/562949953421312000000000000000000), (-30938903165147332058567036399007/5629499534213120000000000000000000), (-13409405845629464890910970456179/5629499534213120000000000000000000), (1113939074548338616686268202287/1125899906842624000000000000000000), (-168912007206367108485621857643/5629499534213120000000000000000000), (-55291393504738210529319165627/2814749767106560000000000000000000), (6503555607170473827511313617/5629499534213120000000000000000000), (1157132217065321905931687323/5629499534213120000000000000000000), (-78550519079932403375412323/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial158.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial158.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial158.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 5045931604150533565001370589487566), (Int.ofNat 120235595664299957210076429778346), (Int.negOfNat 11766605254535001854638270002214), (Int.ofNat 11897440635212338207766557898487), (Int.negOfNat 32924396557032659729532067826), (Int.negOfNat 633859444277194345873751238070), (Int.ofNat 40592301059387550212389507408), (Int.ofNat 9703915985311602508628110013), (Int.negOfNat 766966355187064950749296883), (Int.negOfNat 82585281619604200359084374), (Int.ofNat 7135418927586732736391759), (Int.ofNat 468813818763415971390558), (Int.negOfNat 42348716934749203644372), (Int.negOfNat 1938027577668763417041), (Int.ofNat 178420403657096894317), (Int.ofNat 6033003922460064503), (Int.negOfNat 565978101629456588), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-2522965802075266782500685294743783/2814749767106560000000000000000000), (60117797832149978605038214889173/2814749767106560000000000000000000), (-5883302627267500927319135001107/2814749767106560000000000000000000), (11897440635212338207766557898487/5629499534213120000000000000000000), (-16462198278516329864766033913/2814749767106560000000000000000000), (-63385944427719434587375123807/562949953421312000000000000000000), (2537018816211721888274344213/351843720888320000000000000000000), (9703915985311602508628110013/5629499534213120000000000000000000), (-766966355187064950749296883/5629499534213120000000000000000000), (-41292640809802100179542187/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial158.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial158.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial158.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 4774548139307876941178689607679236), (Int.ofNat 175382243936469540311229760579447), (Int.ofNat 22719625379094841102115284373792), (Int.negOfNat 3485546628484506531476103223824), (Int.negOfNat 2301048009402526479412299410894), (Int.ofNat 224950944266860063685543035995), (Int.ofNat 63173522707118052095174283589), (Int.negOfNat 6335631341806795040324502777), (Int.negOfNat 728144820407908140964009569), (Int.ofNat 79068667592513142739742823), (Int.ofNat 4971311468651984312857931), (Int.negOfNat 583753136457269871113945), (Int.negOfNat 23199842910827418730871), (Int.ofNat 2923124942646199769345), (Int.ofNat 79619670498274904969), (Int.negOfNat 10863057629126995101), (Int.negOfNat 191967151688011104), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-1193637034826969235294672401919809/1407374883553280000000000000000000), (175382243936469540311229760579447/5629499534213120000000000000000000), (709988293096713784441102636681/175921860444160000000000000000000), (-217846664280281658217256451489/351843720888320000000000000000000), (-1150524004701263239706149705447/2814749767106560000000000000000000), (44990188853372012737108607199/1125899906842624000000000000000000), (63173522707118052095174283589/5629499534213120000000000000000000), (-6335631341806795040324502777/5629499534213120000000000000000000), (-728144820407908140964009569/5629499534213120000000000000000000), (79068667592513142739742823/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial158.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial158.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial158.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 4387317813189529491027374701733867), (Int.ofNat 177542702255992138290136822968695), (Int.negOfNat 25419366643187276510949852064271), (Int.negOfNat 7165861741392512528900442248112), (Int.ofNat 1508516626527858301034180210757), (Int.ofNat 305521062098561064871499631980), (Int.negOfNat 46566818996845250010892725422), (Int.negOfNat 5159916126540993410866624556), (Int.ofNat 762244458245063190916591860), (Int.ofNat 44249840674027799296914638), (Int.negOfNat 7089034156165351488915390), (Int.negOfNat 235068997684203968165421), (Int.ofNat 42763636723569521453186), (Int.ofNat 859945916697882431408), (Int.negOfNat 182522133955125900106), (Int.negOfNat 2323653507599524508), (Int.ofNat 617330644459362224), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-4387317813189529491027374701733867/5629499534213120000000000000000000), (35508540451198427658027364593739/1125899906842624000000000000000000), (-25419366643187276510949852064271/5629499534213120000000000000000000), (-447866358837032033056277640507/351843720888320000000000000000000), (1508516626527858301034180210757/5629499534213120000000000000000000), (15276053104928053243574981599/281474976710656000000000000000000), (-23283409498422625005446362711/2814749767106560000000000000000000), (-1289979031635248352716656139/1407374883553280000000000000000000), (38112222912253159545829593/281474976710656000000000000000000), (22124920337013899648457319/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial158.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial158.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial158.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 4160754345768398068545777415251476), (Int.ofNat 52181261953234265546229736391035), (Int.negOfNat 20927434589579554207418209814309), (Int.ofNat 8272812943984899955899886573093), (Int.ofNat 1257409257062996855045488224121), (Int.negOfNat 315707629869915880864196637530), (Int.negOfNat 28416619084642894580198500491), (Int.ofNat 6458928001737892919950148923), (Int.ofNat 311427865784563020965751358), (Int.negOfNat 75740323845476968511813045), (Int.negOfNat 1856347715950629384790770), (Int.ofNat 556763547215562319080042), (Int.ofNat 6506579849423666579360), (Int.negOfNat 2806310211689226435277), (Int.negOfNat 12137700380791313336), (Int.ofNat 10492272889410856576), (Int.negOfNat 13352319426573621), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-1040188586442099517136444353812869/1407374883553280000000000000000000), (10436252390646853109245947278207/1125899906842624000000000000000000), (-20927434589579554207418209814309/5629499534213120000000000000000000), (8272812943984899955899886573093/5629499534213120000000000000000000), (1257409257062996855045488224121/5629499534213120000000000000000000), (-31570762986991588086419663753/562949953421312000000000000000000), (-28416619084642894580198500491/5629499534213120000000000000000000), (6458928001737892919950148923/5629499534213120000000000000000000), (155713932892281510482875679/2814749767106560000000000000000000), (-15148064769095393702362609/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial158.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial158.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial158.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 4064854883919354357623903242120286), (Int.ofNat 80304548489777513193369703353648), (Int.ofNat 31354422074017496665660863068999), (Int.ofNat 4919946003792209858941905440536), (Int.negOfNat 1754369053806484228411797529379), (Int.negOfNat 126083842051449257894606778339), (Int.ofNat 47769227805618917280859889106), (Int.ofNat 1560495779660666128268637699), (Int.negOfNat 709372619707903894595326515), (Int.negOfNat 8686027751913776666231670), (Int.ofNat 6416643454742321376915541), (Int.ofNat 5804819015990191433162), (Int.negOfNat 38560120937581289227694), (Int.ofNat 211682348405579672603), (Int.ofNat 165054360678921569706), (Int.negOfNat 1517471348539525777), (Int.negOfNat 600243363584406285), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-2032427441959677178811951621060143/2814749767106560000000000000000000), (5019034280611094574585606459603/351843720888320000000000000000000), (31354422074017496665660863068999/5629499534213120000000000000000000), (614993250474026232367738180067/703687441776640000000000000000000), (-1754369053806484228411797529379/5629499534213120000000000000000000), (-126083842051449257894606778339/5629499534213120000000000000000000), (23884613902809458640429944553/2814749767106560000000000000000000), (1560495779660666128268637699/5629499534213120000000000000000000), (-141874523941580778919065303/1125899906842624000000000000000000), (-868602775191377666623167/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial158.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial158.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial158.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 3768495762075590047033219970251583), (Int.ofNat 207691455923383195139783457979651), (Int.ofNat 19956150506103239145018808856633), (Int.negOfNat 6864656506737964656554015845337), (Int.negOfNat 459797102848092921904559073300), (Int.ofNat 291154807680155889370587585092), (Int.ofNat 3860354996070799888900717106), (Int.negOfNat 5736489876627186350837362979), (Int.ofNat 29139059060521115469888315), (Int.ofNat 64867532779527805045131030), (Int.negOfNat 894689889106399129886259), (Int.negOfNat 470247937666553863109652), (Int.ofNat 8672567743516741730776), (Int.ofNat 2360965835550634943507), (Int.negOfNat 49314158096496196844), (Int.negOfNat 8731965881637193253), (Int.ofNat 184466995389567195), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-3768495762075590047033219970251583/5629499534213120000000000000000000), (207691455923383195139783457979651/5629499534213120000000000000000000), (19956150506103239145018808856633/5629499534213120000000000000000000), (-6864656506737964656554015845337/5629499534213120000000000000000000), (-4597971028480929219045590733/56294995342131200000000000000000), (72788701920038972342646896273/1407374883553280000000000000000000), (1930177498035399944450358553/2814749767106560000000000000000000), (-5736489876627186350837362979/5629499534213120000000000000000000), (5827811812104223093977663/1125899906842624000000000000000000), (6486753277952780504513103/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial158.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial158.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial158.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 3326693661714307595715744670334524), (Int.ofNat 212060044554768636056201052938644), (Int.negOfNat 11574454784096532984854157103246), (Int.negOfNat 1122662848949017632395053577650), (Int.ofNat 1341338997531854305550058724532), (Int.negOfNat 20095982180979024268123221135), (Int.negOfNat 38580957308562242599177131971), (Int.ofNat 1173461043512187468516561497), (Int.ofNat 565145882517732485662947308), (Int.negOfNat 19744691955724808643651915), (Int.negOfNat 5025113641021108213129980), (Int.ofNat 183743007684402156046848), (Int.ofNat 29909051683151941769390), (Int.negOfNat 1108355182110560933033), (Int.negOfNat 127418479023083945736), (Int.ofNat 4811198548646400554), (Int.ofNat 497598744727953559), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-831673415428576898928936167583631/1407374883553280000000000000000000), (53015011138692159014050263234661/1407374883553280000000000000000000), (-5787227392048266492427078551623/2814749767106560000000000000000000), (-22453256978980352647901071553/112589990684262400000000000000000), (335334749382963576387514681133/1407374883553280000000000000000000), (-4019196436195804853624644227/1125899906842624000000000000000000), (-38580957308562242599177131971/5629499534213120000000000000000000), (1173461043512187468516561497/5629499534213120000000000000000000), (141286470629433121415736827/1407374883553280000000000000000000), (-3948938391144961728730383/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial158.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial158.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial158.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 2939223410091741590732733159725927), (Int.ofNat 187233828755056438215759387183475), (Int.ofNat 4674005806439668345703463304596), (Int.ofNat 4128523986050378058053810470082), (Int.negOfNat 349063265205819322074820296970), (Int.negOfNat 203652529405506195301965979895), (Int.ofNat 15149614278566452927141587498), (Int.ofNat 4108664086322209397026386916), (Int.negOfNat 280515152156372459839427200), (Int.negOfNat 46038990035753439221457368), (Int.ofNat 2951019308708930578277970), (Int.ofNat 329436797202850776169381), (Int.negOfNat 20132850825252283704474), (Int.negOfNat 1636254744241554665568), (Int.ofNat 96562788604338092444), (Int.ofNat 5876500760979027638), (Int.negOfNat 304259361924334406), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-2939223410091741590732733159725927/5629499534213120000000000000000000), (7489353150202257528630375487339/225179981368524800000000000000000), (1168501451609917086425865826149/1407374883553280000000000000000000), (2064261993025189029026905235041/2814749767106560000000000000000000), (-34906326520581932207482029697/562949953421312000000000000000000), (-40730505881101239060393195979/1125899906842624000000000000000000), (7574807139283226463570793749/2814749767106560000000000000000000), (1027166021580552349256596729/1407374883553280000000000000000000), (-87660985048866393699821/1759218604441600000000000000000), (-5754873754469179902682171/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial158.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial158.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial158.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 2523729727766271950861811097397561), (Int.ofNat 232384249471229714359695753284842), (Int.ofNat 10499218796395943513051942892365), (Int.negOfNat 2778904647447411110379299216045), (Int.negOfNat 775452530223405716502505610117), (Int.ofNat 135856572955773894364064752403), (Int.ofNat 23637016302250659168667566634), (Int.negOfNat 3076871409199012571318564063), (Int.negOfNat 347879741884023527192137679), (Int.ofNat 38808784446001623373359627), (Int.ofNat 3051361267145539278178571), (Int.negOfNat 309958408454526779469815), (Int.negOfNat 17838526745207820047831), (Int.ofNat 1703173568491023667015), (Int.ofNat 74441599229953658369), (Int.negOfNat 6893734716026060279), (Int.negOfNat 292279273613368834), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-2523729727766271950861811097397561/5629499534213120000000000000000000), (116192124735614857179847876642421/2814749767106560000000000000000000), (2099843759279188702610388578473/1125899906842624000000000000000000), (-555780929489482222075859843209/1125899906842624000000000000000000), (-775452530223405716502505610117/5629499534213120000000000000000000), (135856572955773894364064752403/5629499534213120000000000000000000), (11818508151125329584333783317/2814749767106560000000000000000000), (-3076871409199012571318564063/5629499534213120000000000000000000), (-347879741884023527192137679/5629499534213120000000000000000000), (38808784446001623373359627/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial158.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial158.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial158.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 2046203246908737243214262100248093), (Int.ofNat 229993159752710298824221187269437), (Int.negOfNat 10730375954357699783564021664817), (Int.negOfNat 1871843991849607362126069003631), (Int.ofNat 932998663442081880655350809451), (Int.ofNat 97680023155828740245075678545), (Int.negOfNat 27294328565918141248747067520), (Int.negOfNat 2006189851017386609861138763), (Int.ofNat 427869373078798877714233367), (Int.ofNat 22124980923052555282182564), (Int.negOfNat 4105024005707526483325301), (Int.negOfNat 153369618216130566572248), (Int.ofNat 26401100609177670271698), (Int.ofNat 733065240771768754351), (Int.negOfNat 121022648148524011083), (Int.negOfNat 2468109510533963833), (Int.ofNat 355611904754240042), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-2046203246908737243214262100248093/5629499534213120000000000000000000), (229993159752710298824221187269437/5629499534213120000000000000000000), (-10730375954357699783564021664817/5629499534213120000000000000000000), (-1871843991849607362126069003631/5629499534213120000000000000000000), (932998663442081880655350809451/5629499534213120000000000000000000), (19536004631165748049015135709/1125899906842624000000000000000000), (-42647388384247095701167293/8796093022208000000000000000000), (-2006189851017386609861138763/5629499534213120000000000000000000), (427869373078798877714233367/5629499534213120000000000000000000), (5531245230763138820545641/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial158.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial158.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial158.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 1627946616125432405504280339532921), (Int.ofNat 196607645430578928866285898004831), (Int.ofNat 1165071271716238237455050045677), (Int.ofNat 4828036848872718619337505645935), (Int.ofNat 220663270113017556552519475879), (Int.negOfNat 196930708444530610229789782640), (Int.negOfNat 7026041018043348340424028554), (Int.ofNat 3969678123341007430391927333), (Int.ofNat 100023372076443412821041623), (Int.negOfNat 46835923097114934497508017), (Int.negOfNat 803893436099593619977042), (Int.ofNat 358746045093981893576112), (Int.ofNat 4129324165384825368770), (Int.negOfNat 1917055495379448438775), (Int.negOfNat 14958901551229972245), (Int.ofNat 7641709437861758928), (Int.ofNat 86959802498784109), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-1627946616125432405504280339532921/5629499534213120000000000000000000), (196607645430578928866285898004831/5629499534213120000000000000000000), (1165071271716238237455050045677/5629499534213120000000000000000000), (965607369774543723867501129187/1125899906842624000000000000000000), (220663270113017556552519475879/5629499534213120000000000000000000), (-2461633855556632627872372283/70368744177664000000000000000000), (-3513020509021674170212014277/2814749767106560000000000000000000), (3969678123341007430391927333/5629499534213120000000000000000000), (100023372076443412821041623/5629499534213120000000000000000000), (-46835923097114934497508017/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial158.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial158.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial158.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1194157924822521547488377713015124), (Int.ofNat 250934995147252559360110567816088), (Int.ofNat 20620365333616370527031686111020), (Int.negOfNat 254867677684932634672420112034), (Int.negOfNat 1131336046492837262872303332922), (Int.ofNat 6518858868741726680853767425), (Int.ofNat 30711923607295497184747390897), (Int.negOfNat 151978844560589328742038214), (Int.negOfNat 457177863185937117871252264), (Int.ofNat 2742131733491631153746349), (Int.ofNat 4246967031437136703477173), (Int.negOfNat 30285602667983181705430), (Int.negOfNat 26762019999271670939845), (Int.ofNat 211814358488952878713), (Int.ofNat 121420309019472089787), (Int.negOfNat 1145752378034081062), (Int.negOfNat 406964447584145678), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-298539481205630386872094428253781/1407374883553280000000000000000000), (31366874393406569920013820977011/703687441776640000000000000000000), (1031018266680818526351584305551/281474976710656000000000000000000), (-127433838842466317336210056017/2814749767106560000000000000000000), (-565668023246418631436151666461/2814749767106560000000000000000000), (260754354749669067234150697/225179981368524800000000000000000), (30711923607295497184747390897/5629499534213120000000000000000000), (-75989422280294664371019107/2814749767106560000000000000000000), (-57147232898242139733906533/703687441776640000000000000000000), (2742131733491631153746349/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial158.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial158.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial158.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 627903530700951660442761708706607), (Int.ofNat 300064340495808920116049742830875), (Int.negOfNat 1030951280452144937797573147684), (Int.negOfNat 4959434611813702201122836024315), (Int.ofNat 285635813108385221720106728838), (Int.ofNat 193834755590915958882167202461), (Int.negOfNat 8403508632682240524753281303), (Int.negOfNat 3760410026470445080893198648), (Int.ofNat 134643442537794067436004813), (Int.ofNat 43232747590982707609132469), (Int.negOfNat 1345333523844652779842798), (Int.negOfNat 326146246973869573854853), (Int.ofNat 9057299352429368824769), (Int.ofNat 1728379948205544105784), (Int.negOfNat 43462001834088855190), (Int.negOfNat 6853290589115852770), (Int.ofNat 135477182892435828), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-627903530700951660442761708706607/5629499534213120000000000000000000), (2400514723966471360928397942647/45035996273704960000000000000000), (-257737820113036234449393286921/1407374883553280000000000000000000), (-991886922362740440224567204863/1125899906842624000000000000000000), (142817906554192610860053364419/2814749767106560000000000000000000), (193834755590915958882167202461/5629499534213120000000000000000000), (-8403508632682240524753281303/5629499534213120000000000000000000), (-470051253308805635111649831/703687441776640000000000000000000), (134643442537794067436004813/5629499534213120000000000000000000), (43232747590982707609132469/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial158.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial158.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial158.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 61765794916308002141662795899224), (Int.ofNat 258003538553228716361428398211143), (Int.negOfNat 12552674952226180184875982157437), (Int.ofNat 2069393027722964614592929571539), (Int.ofNat 961834017126062738547063706417), (Int.negOfNat 94472365078222611847442076892), (Int.negOfNat 25392563760252519706379672667), (Int.ofNat 1996253465196495982554132242), (Int.ofNat 369896754156756608819463027), (Int.negOfNat 24322176344153064147708311), (Int.negOfNat 3397102059133387158950802), (Int.ofNat 191511701434559388027577), (Int.ofNat 21328645539764087053741), (Int.negOfNat 1048386220532337336576), (Int.negOfNat 96814306838112628360), (Int.ofNat 4268825526539465310), (Int.ofNat 304319828727692952), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-7720724364538500267707849487403/703687441776640000000000000000000), (258003538553228716361428398211143/5629499534213120000000000000000000), (-12552674952226180184875982157437/5629499534213120000000000000000000), (2069393027722964614592929571539/5629499534213120000000000000000000), (961834017126062738547063706417/5629499534213120000000000000000000), (-23618091269555652961860519223/1407374883553280000000000000000000), (-25392563760252519706379672667/5629499534213120000000000000000000), (998126732598247991277066121/2814749767106560000000000000000000), (369896754156756608819463027/5629499534213120000000000000000000), (-24322176344153064147708311/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial158.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial158.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial158.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 431661583102388980049509056457173), (Int.ofNat 252173362185656012556091466248883), (Int.ofNat 11155456359197432687192592561529), (Int.ofNat 3530303767699471145321211897417), (Int.negOfNat 666608945589788659201163632459), (Int.negOfNat 134816029969172888889940574510), (Int.ofNat 20025728901966934224759499503), (Int.ofNat 2553650818414780034633449156), (Int.negOfNat 315074459756800494656394326), (Int.negOfNat 29053259485985634603605951), (Int.ofNat 3031617783892612095221227), (Int.ofNat 219459564804458524566800), (Int.negOfNat 19571353467490401642085), (Int.negOfNat 1172752252842089352797), (Int.ofNat 90063855339950987563), (Int.ofNat 4764424389772538868), (Int.negOfNat 306591858855429402), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(431661583102388980049509056457173/5629499534213120000000000000000000), (252173362185656012556091466248883/5629499534213120000000000000000000), (11155456359197432687192592561529/5629499534213120000000000000000000), (3530303767699471145321211897417/5629499534213120000000000000000000), (-666608945589788659201163632459/5629499534213120000000000000000000), (-13481602996917288888994057451/562949953421312000000000000000000), (20025728901966934224759499503/5629499534213120000000000000000000), (638412704603695008658362289/1407374883553280000000000000000000), (-157537229878400247328197163/2814749767106560000000000000000000), (-29053259485985634603605951/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial158.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial158.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial158.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 995409152249918550914983150416708), (Int.ofNat 311658926468459999406065370070426), (Int.ofNat 11416750370398201820902713161433), (Int.negOfNat 3228489772418448697353738699502), (Int.negOfNat 521021111480511189412471865833), (Int.ofNat 148943734619321141276283540738), (Int.ofNat 13058833276399659718377791134), (Int.negOfNat 3181709691232218306536491567), (Int.negOfNat 185962650955461970852519103), (Int.ofNat 38743376157899954292855773), (Int.ofNat 1716484663299069421238612), (Int.negOfNat 302825689245954331503248), (Int.negOfNat 11030578900734427214540), (Int.ofNat 1639491571001643145885), (Int.ofNat 51763033582123895395), (Int.negOfNat 6502271667086686902), (Int.negOfNat 116117871889743439), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(248852288062479637728745787604177/1407374883553280000000000000000000), (155829463234229999703032685035213/2814749767106560000000000000000000), (11416750370398201820902713161433/5629499534213120000000000000000000), (-1614244886209224348676869349751/2814749767106560000000000000000000), (-521021111480511189412471865833/5629499534213120000000000000000000), (74471867309660570638141770369/2814749767106560000000000000000000), (6529416638199829859188895567/2814749767106560000000000000000000), (-3181709691232218306536491567/5629499534213120000000000000000000), (-185962650955461970852519103/5629499534213120000000000000000000), (38743376157899954292855773/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial158.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial158.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial158.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 1635397793243389195100618934667984), (Int.ofNat 314812800778279604806715715628258), (Int.negOfNat 7691124486714629764258047580154), (Int.negOfNat 1243376652062290543830923373918), (Int.ofNat 818517181737434210123700607893), (Int.ofNat 37523180667630600302173651025), (Int.negOfNat 25256988934918607598693780883), (Int.negOfNat 617294492114842427448723193), (Int.ofNat 405062082186622330201308083), (Int.ofNat 6888347308250090597008164), (Int.negOfNat 3944098625715530725177659), (Int.negOfNat 56246647536896537194208), (Int.ofNat 25611438216720156350122), (Int.ofNat 337681281358933836311), (Int.negOfNat 118299680942954168617), (Int.negOfNat 1534303907854426263), (Int.ofNat 357944401685335038), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(102212362077711824693788683416749/351843720888320000000000000000000), (157406400389139802403357857814129/2814749767106560000000000000000000), (-3845562243357314882129023790077/2814749767106560000000000000000000), (-621688326031145271915461686959/2814749767106560000000000000000000), (818517181737434210123700607893/5629499534213120000000000000000000), (1500927226705224012086946041/225179981368524800000000000000000), (-25256988934918607598693780883/5629499534213120000000000000000000), (-617294492114842427448723193/5629499534213120000000000000000000), (405062082186622330201308083/5629499534213120000000000000000000), (1722086827062522649252041/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial158.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial158.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial158.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 2237016613831329134540767472818421), (Int.ofNat 293606758166478228938371977116669), (Int.ofNat 1730716399882575694284816063221), (Int.ofNat 3121725533900971610627010541368), (Int.negOfNat 65207053992294315028263082931), (Int.negOfNat 152941355848278301470449604428), (Int.ofNat 3510542249608028770841111631), (Int.ofNat 3406524258482169869029945877), (Int.negOfNat 60973989661365233014503201), (Int.negOfNat 42880977676996262983367823), (Int.ofNat 523940070729631330498159), (Int.ofNat 343156177276637960945395), (Int.negOfNat 2558665632495270222239), (Int.negOfNat 1885044252613014883995), (Int.ofNat 7301815071842760731), (Int.ofNat 7534518430021050301), (Int.negOfNat 89201599224841286), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(2237016613831329134540767472818421/5629499534213120000000000000000000), (293606758166478228938371977116669/5629499534213120000000000000000000), (1730716399882575694284816063221/5629499534213120000000000000000000), (390215691737621451328376317671/703687441776640000000000000000000), (-65207053992294315028263082931/5629499534213120000000000000000000), (-38235338962069575367612401107/1407374883553280000000000000000000), (3510542249608028770841111631/5629499534213120000000000000000000), (3406524258482169869029945877/5629499534213120000000000000000000), (-60973989661365233014503201/5629499534213120000000000000000000), (-42880977676996262983367823/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial158.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial158.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial158.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 2850813722927491824523188715562097), (Int.ofNat 325713695091171202995957289849835), (Int.ofNat 9500879407477756169847990210705), (Int.negOfNat 1366316828628580066425044990218), (Int.negOfNat 650797951368862041854059926136), (Int.ofNat 75089737144757395506542652303), (Int.ofNat 21849290051984702845535732022), (Int.negOfNat 1685862646865223741018911514), (Int.negOfNat 376170532512204359195636060), (Int.ofNat 19747810579022243203463872), (Int.ofNat 3864888139041583553858840), (Int.negOfNat 139348361620730083522029), (Int.negOfNat 26010961511399921748636), (Int.ofNat 653245065722745792672), (Int.ofNat 122819234239745389206), (Int.negOfNat 2175046507006113732), (Int.negOfNat 409296944515240674), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(2850813722927491824523188715562097/5629499534213120000000000000000000), (65142739018234240599191457969967/1125899906842624000000000000000000), (1900175881495551233969598042141/1125899906842624000000000000000000), (-683158414314290033212522495109/2814749767106560000000000000000000), (-81349743921107755231757490767/703687441776640000000000000000000), (75089737144757395506542652303/5629499534213120000000000000000000), (10924645025992351422767866011/2814749767106560000000000000000000), (-842931323432611870509455757/2814749767106560000000000000000000), (-18808526625610217959781803/281474976710656000000000000000000), (308559540297222550054123/87960930222080000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial158.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial158.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial158.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 3522404148828191403135485599518553), (Int.ofNat 335620780335050669115960354924956), (Int.negOfNat 4742174225684436577152660661950), (Int.negOfNat 1534415364191274022923290583766), (Int.ofNat 640445219598397648276295853030), (Int.ofNat 91695992999578244797463339473), (Int.negOfNat 20996676244779576374929078779), (Int.negOfNat 2425857911028906636056214873), (Int.ofNat 332421668451988828708850762), (Int.ofNat 34678950236417541114491695), (Int.negOfNat 3011524959013348242777170), (Int.negOfNat 301435662378637414954242), (Int.ofNat 17523589791991990730900), (Int.ofNat 1736667072683924420977), (Int.negOfNat 71357787291760672664), (Int.negOfNat 7163733690304911776), (Int.ofNat 294521070339426011), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(3522404148828191403135485599518553/5629499534213120000000000000000000), (83905195083762667278990088731239/1407374883553280000000000000000000), (-94843484513688731543053213239/112589990684262400000000000000000), (-767207682095637011461645291883/2814749767106560000000000000000000), (64044521959839764827629585303/562949953421312000000000000000000), (91695992999578244797463339473/5629499534213120000000000000000000), (-20996676244779576374929078779/5629499534213120000000000000000000), (-2425857911028906636056214873/5629499534213120000000000000000000), (166210834225994414354425381/2814749767106560000000000000000000), (6935790047283508222898339/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial158.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial158.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial158.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 4174028026918448595412657076836479), (Int.ofNat 321352878355828442612197319442261), (Int.ofNat 2802067952938043980769205135160), (Int.ofNat 3264598537735405129423800330917), (Int.ofNat 80059733734040319601253533408), (Int.negOfNat 176140407802185877770381140246), (Int.negOfNat 7651558776230241593142577181), (Int.ofNat 3997385055879181848946431221), (Int.ofNat 208336038254753491625958915), (Int.negOfNat 47581605161655788270040540), (Int.negOfNat 2714517792890129089416491), (Int.ofNat 342072822865469718151888), (Int.ofNat 20510078302869275444044), (Int.negOfNat 1664059065757279492233), (Int.negOfNat 102859398196696141356), (Int.ofNat 6016171363145164017), (Int.ofNat 392209663640284735), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(4174028026918448595412657076836479/5629499534213120000000000000000000), (321352878355828442612197319442261/5629499534213120000000000000000000), (70051698823451099519230128379/140737488355328000000000000000000), (3264598537735405129423800330917/5629499534213120000000000000000000), (2501866679188759987539172919/175921860444160000000000000000000), (-88070203901092938885190570123/2814749767106560000000000000000000), (-7651558776230241593142577181/5629499534213120000000000000000000), (3997385055879181848946431221/5629499534213120000000000000000000), (41667207650950698325191783/1125899906842624000000000000000000), (-2379080258082789413502027/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial158.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial158.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial158.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 4849752234010255640399790987666265), (Int.ofNat 360622808842244216794725186950040), (Int.ofNat 11203260240518234303971749186573), (Int.negOfNat 2034201211375898897914633613690), (Int.negOfNat 999813190037097018013570361794), (Int.ofNat 54902522638147899466597598238), (Int.ofNat 36393207207274165050596337614), (Int.negOfNat 17296856386202408383652221), (Int.negOfNat 605181026802087391730069785), (Int.negOfNat 13816401169596616737513430), (Int.ofNat 5482837219282653579520349), (Int.ofNat 181000225973667483132752), (Int.negOfNat 31945831431901901990186), (Int.negOfNat 1213393693945015701757), (Int.ofNat 131546385532513025594), (Int.ofNat 5403426682531248453), (Int.negOfNat 465635746302419585), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(969950446802051128079958197533253/1125899906842624000000000000000000), (9015570221056105419868129673751/140737488355328000000000000000000), (11203260240518234303971749186573/5629499534213120000000000000000000), (-203420121137589889791463361369/562949953421312000000000000000000), (-499906595018548509006785180897/2814749767106560000000000000000000), (27451261319073949733298799119/2814749767106560000000000000000000), (18196603603637082525298168807/2814749767106560000000000000000000), (-17296856386202408383652221/5629499534213120000000000000000000), (-121036205360417478346013957/1125899906842624000000000000000000), (-1381640116959661673751343/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial158.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial158.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial158.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 5587467950197404172922305231911362), (Int.ofNat 359781100805156630370265733867077), (Int.negOfNat 12964706722002709137235550471497), (Int.negOfNat 3094126090799198499462157659358), (Int.ofNat 1071439929178462841014701707392), (Int.ofNat 237267694000158032803916796233), (Int.negOfNat 21859959308578683417909562179), (Int.negOfNat 6349399467115086681038774117), (Int.ofNat 97198438530428711510722992), (Int.ofNat 75034373421636384244472975), (Int.ofNat 640230179955814912823930), (Int.negOfNat 529785499441809731536748), (Int.negOfNat 9992725488350729531890), (Int.ofNat 2558870015456245514213), (Int.ofNat 61325655457808200136), (Int.negOfNat 9309898563252038794), (Int.negOfNat 289565044783832009), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(2793733975098702086461152615955681/2814749767106560000000000000000000), (359781100805156630370265733867077/5629499534213120000000000000000000), (-12964706722002709137235550471497/5629499534213120000000000000000000), (-1547063045399599249731078829679/2814749767106560000000000000000000), (8370624446706740945427357089/43980465111040000000000000000000), (237267694000158032803916796233/5629499534213120000000000000000000), (-21859959308578683417909562179/5629499534213120000000000000000000), (-6349399467115086681038774117/5629499534213120000000000000000000), (6074902408151794469420187/351843720888320000000000000000000), (3001374936865455369778919/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial158.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial158.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial158.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 6253005012454394962070425487500867), (Int.ofNat 317288227132070294811411119428725), (Int.ofNat 4165466513394394824000292109275), (Int.ofNat 8479515602583004371737922773353), (Int.ofNat 752021131134553008452365014882), (Int.negOfNat 374225929848946456889810474500), (Int.negOfNat 55129983403859927508664294118), (Int.ofNat 3866796977248399186605839134), (Int.ofNat 893764559976468801558357820), (Int.negOfNat 16214655314967847769217082), (Int.negOfNat 7750584550735481955169460), (Int.negOfNat 4208149912281558044531), (Int.ofNat 44041928572529589433784), (Int.ofNat 407772525263505668368), (Int.negOfNat 180254854543282743744), (Int.negOfNat 2547961561873082838), (Int.ofNat 585428112837186796), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(6253005012454394962070425487500867/5629499534213120000000000000000000), (12691529085282811792456444777149/225179981368524800000000000000000), (166618660535775792960011684371/225179981368524800000000000000000), (8479515602583004371737922773353/5629499534213120000000000000000000), (376010565567276504226182507441/2814749767106560000000000000000000), (-748451859697892913779620949/11258999068426240000000000000000), (-27564991701929963754332147059/2814749767106560000000000000000000), (1933398488624199593302919567/2814749767106560000000000000000000), (44688227998823440077917891/281474976710656000000000000000000), (-8107327657483923884608541/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial158.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial158.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial158.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 6969315934362408427558930965706509), (Int.ofNat 421817459550927895993919714668784), (Int.ofNat 33960761764718251121403196136687), (Int.negOfNat 5728570019144489691905770239126), (Int.negOfNat 4378497625155584489886882590363), (Int.negOfNat 401469931878536474554340189036), (Int.ofNat 64660429415022730249464127128), (Int.ofNat 9450549634066819796668933733), (Int.negOfNat 467889595335070718605889171), (Int.negOfNat 101456453399860321681562687), (Int.ofNat 1889657446115759981579279), (Int.ofNat 681380002503476551814265), (Int.negOfNat 3497846942154089213519), (Int.negOfNat 3211366075691468908245), (Int.negOfNat 5581427978741023069), (Int.ofNat 11392434730631698519), (Int.ofNat 84245573669247284), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(6969315934362408427558930965706509/5629499534213120000000000000000000), (26363591221932993499619982166799/351843720888320000000000000000000), (33960761764718251121403196136687/5629499534213120000000000000000000), (-2864285009572244845952885119563/2814749767106560000000000000000000), (-4378497625155584489886882590363/5629499534213120000000000000000000), (-100367482969634118638585047259/1407374883553280000000000000000000), (8082553676877841281183015891/703687441776640000000000000000000), (9450549634066819796668933733/5629499534213120000000000000000000), (-467889595335070718605889171/5629499534213120000000000000000000), (-101456453399860321681562687/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial158.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial158.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial158.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 7825241843061898590875083200895960), (Int.ofNat 332641017173262152884412358197792), (Int.negOfNat 117008678259956845168910376059818), (Int.negOfNat 42504770913473033510646656285370), (Int.negOfNat 2747940770735570990818029438253), (Int.ofNat 788151951187938933311098982685), (Int.ofNat 91920637090391770451000599640), (Int.negOfNat 7659112202215279820233350587), (Int.negOfNat 1206464343880670853915844737), (Int.ofNat 46503199849260779201131886), (Int.ofNat 9560088335120824055567141), (Int.negOfNat 189531512339718575091152), (Int.negOfNat 52053825926899102637708), (Int.ofNat 532851181966331210499), (Int.ofNat 208425788144374827183), (Int.negOfNat 860429688571980967), (Int.negOfNat 636780655667092432), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(195631046076547464771877080022399/140737488355328000000000000000000), (10395031786664442277637886193681/175921860444160000000000000000000), (-58504339129978422584455188029909/2814749767106560000000000000000000), (-4250477091347303351064665628537/562949953421312000000000000000000), (-2747940770735570990818029438253/5629499534213120000000000000000000), (157630390237587786662219796537/1125899906842624000000000000000000), (2298015927259794261275014991/140737488355328000000000000000000), (-7659112202215279820233350587/5629499534213120000000000000000000), (-1206464343880670853915844737/5629499534213120000000000000000000), (23251599924630389600565943/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial158.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial158.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial158.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 7668331512208237055604123629402491), (Int.negOfNat 657198106267055888793722151524605), (Int.negOfNat 359867956308344564778204887594081), (Int.negOfNat 24322722398541161527953922241954), (Int.ofNat 7454813063459782625636925919869), (Int.ofNat 867680525176225275365413351038), (Int.negOfNat 92669642557797531916059172046), (Int.negOfNat 13263606914168985929690346403), (Int.ofNat 748096405602166118189500827), (Int.ofNat 122622810204565828432789627), (Int.negOfNat 4200627094316587649559108), (Int.negOfNat 770328533616610508080762), (Int.ofNat 17302909429826279118480), (Int.ofNat 3512960742815501026455), (Int.negOfNat 54319092698744877855), (Int.negOfNat 12140409452467397168), (Int.ofNat 121073897445337441), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(7668331512208237055604123629402491/5629499534213120000000000000000000), (-131439621253411177758744430304921/1125899906842624000000000000000000), (-359867956308344564778204887594081/5629499534213120000000000000000000), (-12161361199270580763976961120977/2814749767106560000000000000000000), (7454813063459782625636925919869/5629499534213120000000000000000000), (433840262588112637682706675519/2814749767106560000000000000000000), (-46334821278898765958029586023/2814749767106560000000000000000000), (-13263606914168985929690346403/5629499534213120000000000000000000), (748096405602166118189500827/5629499534213120000000000000000000), (122622810204565828432789627/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial158.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial158.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial158.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 4859544397126638614641786620356553), (Int.negOfNat 2103289814825035141340162268062508), (Int.negOfNat 286790941912502657764180336472722), (Int.ofNat 49673904809598695478075062500748), (Int.ofNat 8104308517600248513395782558936), (Int.negOfNat 829973843929725869525643877673), (Int.negOfNat 135949640418072406236897029767), (Int.ofNat 9045520099633062049718637864), (Int.ofNat 1444441830875125562456336534), (Int.negOfNat 67211413919951921907442999), (Int.negOfNat 10437394385006313730414663), (Int.ofNat 359461636725894146770480), (Int.ofNat 54267718853203626340105), (Int.negOfNat 1445610905908529724813), (Int.negOfNat 212249446912888585587), (Int.ofNat 4474291577140025862), (Int.ofNat 688133198496998068), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(4859544397126638614641786620356553/5629499534213120000000000000000000), (-525822453706258785335040567015627/1407374883553280000000000000000000), (-143395470956251328882090168236361/2814749767106560000000000000000000), (12418476202399673869518765625187/1407374883553280000000000000000000), (1013038564700031064174472819867/703687441776640000000000000000000), (-829973843929725869525643877673/5629499534213120000000000000000000), (-135949640418072406236897029767/5629499534213120000000000000000000), (1130690012454132756214829733/703687441776640000000000000000000), (722220915437562781228168267/2814749767106560000000000000000000), (-67211413919951921907442999/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial158.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial158.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial158.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 915318527649909444706552778868), (Int.negOfNat 2482200600969437110048516945348971), (Int.ofNat 114980635690142823359435759295036), (Int.ofNat 66710487034621223800392705739807), (Int.negOfNat 4591831731470637971230843774234), (Int.negOfNat 1258645544522200735142641288596), (Int.ofNat 80288846894286000845667500741), (Int.ofNat 15490579387363904482118290118), (Int.negOfNat 834442263444334678950165913), (Int.negOfNat 129199570897106680049531579), (Int.ofNat 5815322920946667680349298), (Int.ofNat 767698958682880239105303), (Int.negOfNat 29127195119060580902319), (Int.negOfNat 3389166547543167150114), (Int.ofNat 110247933317218787840), (Int.ofNat 11351990603721491010), (Int.negOfNat 343510882836557378), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-228829631912477361176638194717/1407374883553280000000000000000000), (-2482200600969437110048516945348971/5629499534213120000000000000000000), (28745158922535705839858939823759/1407374883553280000000000000000000), (66710487034621223800392705739807/5629499534213120000000000000000000), (-2295915865735318985615421887117/2814749767106560000000000000000000), (-314661386130550183785660322149/1407374883553280000000000000000000), (80288846894286000845667500741/5629499534213120000000000000000000), (7745289693681952241059145059/2814749767106560000000000000000000), (-834442263444334678950165913/5629499534213120000000000000000000), (-129199570897106680049531579/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial158.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial158.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial158.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial158.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial158.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial158.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial158.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial158.reflect := by
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

end Bin158
end
end ErdosOverlap.OuterNumerics
