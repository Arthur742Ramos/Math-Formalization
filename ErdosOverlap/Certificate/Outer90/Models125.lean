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

/-! # Exact integer weighted outer models for source bin 125

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin125

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 5442766680961796000)⟩, ⟨(5980904522613/1000000000000), (Int.negOfNat 3950578822783844500)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 4381672472231990500)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 475580906239102400)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 417408401883769000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 318196740066978000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 30266453692479530)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 479572206469831700)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 263994880267127100)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial125.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial125.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 2382073677105484300)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 13777084016481748)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 241721379421658380)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 323236993234441900)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 68248952280714640)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 197022240372410800)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 17513876398544941)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 41600518883297600)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 16760344539536842)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial125.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial125.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 2382073677105484300)⟩, ⟨(314159265359/50000000000), (Int.ofNat 13777084016481748)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 241721379421658380)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 323236993234441900)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 68248952280714640)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 197022240372410800)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 17513876398544941)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 41600518883297600)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 16760344539536842)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial125.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial125.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial125.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 17019446325015535109560642605113221), (Int.ofNat 1438364994772328912482402422439372), (Int.ofNat 683572395519279744224515309461102), (Int.negOfNat 43643709245152639340380034204632), (Int.negOfNat 12790411987264708425324561447129), (Int.ofNat 1029742225276030944291648860569), (Int.ofNat 178462434354712941236444447683), (Int.negOfNat 13776812855618593480557863502), (Int.negOfNat 1594306445477451277943456739), (Int.ofNat 111419399390572562201921064), (Int.ofNat 9338352317636673161334663), (Int.negOfNat 600426785480495171642016), (Int.negOfNat 37893541830256293237720), (Int.ofNat 2319413325814640901418), (Int.ofNat 111267729978867141393), (Int.negOfNat 6926733048469099548), (Int.negOfNat 205033331913203648), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-17019446325015535109560642605113221/11258999068426240000000000000000000), (359591248693082228120600605609843/2814749767106560000000000000000000), (341786197759639872112257654730551/5629499534213120000000000000000000), (-5455463655644079917547504275579/1407374883553280000000000000000000), (-12790411987264708425324561447129/11258999068426240000000000000000000), (1029742225276030944291648860569/11258999068426240000000000000000000), (178462434354712941236444447683/11258999068426240000000000000000000), (-6888406427809296740278931751/5629499534213120000000000000000000), (-1594306445477451277943456739/11258999068426240000000000000000000), (13927424923821570275240133/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial125.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial125.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial125.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial125 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.negOfNat 11919956001738599529877228325447596), (Int.ofNat 3348773428407456071912595277432419), (Int.ofNat 228437534278833958856276282538273), (Int.negOfNat 86081793058209116751538241885832), (Int.ofNat 3117154630384637373117277950340), (Int.ofNat 1578976464553784424158552065506), (Int.negOfNat 97266146154695673105510306968), (Int.negOfNat 18115794638440095638098909807), (Int.ofNat 1110198203212693329728222174), (Int.ofNat 130641224755897968938179350), (Int.negOfNat 7519389599300820749330791), (Int.negOfNat 630671173541336822948468), (Int.ofNat 34544190871250955596078), (Int.ofNat 2149643717653102368508), (Int.negOfNat 115942271026584663252), (Int.negOfNat 5401219656027053033), (Int.ofNat 289435739541976868), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-2979989000434649882469307081361899/2814749767106560000000000000000000), (3348773428407456071912595277432419/11258999068426240000000000000000000), (228437534278833958856276282538273/11258999068426240000000000000000000), (-10760224132276139593942280235729/1407374883553280000000000000000000), (155857731519231868655863897517/562949953421312000000000000000000), (789488232276892212079276032753/5629499534213120000000000000000000), (-12158268269336959138188788371/1407374883553280000000000000000000), (-18115794638440095638098909807/11258999068426240000000000000000000), (555099101606346664864111087/5629499534213120000000000000000000), (2612824495117959378763587/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial125.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial125.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial125.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial125 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.negOfNat 4905113221773125815325448570302848), (Int.ofNat 3430211324204625067105044732957399), (Int.negOfNat 119951367310024743984881290854980), (Int.negOfNat 21138835399735837627966363799699), (Int.ofNat 9646027908855976061290653950817), (Int.negOfNat 424409064436530945583725701682), (Int.negOfNat 170928545045320580722113482774), (Int.ofNat 8964808871514145804106623920), (Int.ofNat 1612247140496537462610168310), (Int.negOfNat 81770329688900779747014943), (Int.negOfNat 9558247778035287422823562), (Int.ofNat 461287758905452943800883), (Int.ofNat 38604820827067730424221), (Int.negOfNat 1812207924984998990601), (Int.negOfNat 111350999547252895800), (Int.ofNat 5148832456619716945), (Int.ofNat 188272987373666806), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-38321197045102545432230066955491/87960930222080000000000000000000), (3430211324204625067105044732957399/11258999068426240000000000000000000), (-5997568365501237199244064542749/562949953421312000000000000000000), (-21138835399735837627966363799699/11258999068426240000000000000000000), (9646027908855976061290653950817/11258999068426240000000000000000000), (-212204532218265472791862850841/5629499534213120000000000000000000), (-85464272522660290361056741387/5629499534213120000000000000000000), (112060110893926822551332799/140737488355328000000000000000000), (161224714049653746261016831/1125899906842624000000000000000000), (-81770329688900779747014943/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial125.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial125.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial125.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial125 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 1437718866892629520695312709037332), (Int.ofNat 2944077592600766964465264009087155), (Int.negOfNat 81813423397841830101867819722470), (Int.ofNat 19050715960943338065864805551117), (Int.negOfNat 972457769816010603291380366672), (Int.negOfNat 1225288121646000054159125919773), (Int.ofNat 56719024268497411695301742865), (Int.ofNat 16985722696628613810984673199), (Int.negOfNat 756552174944673124348520343), (Int.negOfNat 129425317124382670421735871), (Int.ofNat 5445975376381152741923328), (Int.ofNat 635733612301920408124092), (Int.negOfNat 25611961710625087696632), (Int.negOfNat 2168606669159862150499), (Int.ofNat 85925698858404898471), (Int.ofNat 5132300611535455462), (Int.negOfNat 239154705923366342), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(359429716723157380173828177259333/2814749767106560000000000000000000), (588815518520153392893052801817431/2251799813685248000000000000000000), (-8181342339784183010186781972247/1125899906842624000000000000000000), (19050715960943338065864805551117/11258999068426240000000000000000000), (-60778610613500662705711272917/703687441776640000000000000000000), (-1225288121646000054159125919773/11258999068426240000000000000000000), (11343804853699482339060348573/2251799813685248000000000000000000), (16985722696628613810984673199/11258999068426240000000000000000000), (-756552174944673124348520343/11258999068426240000000000000000000), (-129425317124382670421735871/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial125.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial125.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial125.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial125 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 7101808546476909517581644102759004), (Int.ofNat 2733751853682259523683904859305439), (Int.negOfNat 65717726996170596172046609598437), (Int.negOfNat 21097897875696629261008695409736), (Int.negOfNat 6339267154924414777607729841216), (Int.ofNat 341789471697081742116214483042), (Int.ofNat 148595713049426190473688329887), (Int.negOfNat 6013571321261323427358870879), (Int.negOfNat 1538760502779996353614921714), (Int.ofNat 56340170638089877727999862), (Int.ofNat 9473409948327886445992196), (Int.negOfNat 323868423567609588410993), (Int.negOfNat 38851824061786899712598), (Int.ofNat 1275949163321435108308), (Int.ofNat 112743297521023152859), (Int.negOfNat 3767455880401489931), (Int.negOfNat 188272987373666806), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(1775452136619227379395411025689751/2814749767106560000000000000000000), (2733751853682259523683904859305439/11258999068426240000000000000000000), (-65717726996170596172046609598437/11258999068426240000000000000000000), (-2637237234462078657626086926217/1407374883553280000000000000000000), (-99051049295693980900120778769/175921860444160000000000000000000), (170894735848540871058107241521/5629499534213120000000000000000000), (148595713049426190473688329887/11258999068426240000000000000000000), (-6013571321261323427358870879/11258999068426240000000000000000000), (-769380251389998176807460857/5629499534213120000000000000000000), (28170085319044938863999931/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial125.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial125.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial125.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial125 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 12055551353967627189785280288486046), (Int.ofNat 2066627174752610163972637920920851), (Int.negOfNat 287882730301149308268749077573019), (Int.negOfNat 40059411167445595371668484321708), (Int.ofNat 2923612113681296671596798207984), (Int.ofNat 1107416687916967824804813021391), (Int.negOfNat 44974006262683657329681045143), (Int.negOfNat 15938563486144046465792832287), (Int.ofNat 515888746280598681523252787), (Int.ofNat 126530971816125725452783096), (Int.negOfNat 3635178958745146639064623), (Int.negOfNat 635926079873800484730820), (Int.ofNat 16959358523905603266395), (Int.ofNat 2198736780562791521642), (Int.negOfNat 56171940285244217089), (Int.negOfNat 5678160664304426431), (Int.ofNat 188873672304755816), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(6027775676983813594892640144243023/5629499534213120000000000000000000), (2066627174752610163972637920920851/11258999068426240000000000000000000), (-287882730301149308268749077573019/11258999068426240000000000000000000), (-10014852791861398842917121080427/2814749767106560000000000000000000), (182725757105081041974799887999/703687441776640000000000000000000), (1107416687916967824804813021391/11258999068426240000000000000000000), (-44974006262683657329681045143/11258999068426240000000000000000000), (-15938563486144046465792832287/11258999068426240000000000000000000), (515888746280598681523252787/11258999068426240000000000000000000), (15816371477015715681597887/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial125.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial125.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial125.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial125 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 14794288061209861796477753408484235), (Int.ofNat 601551305040076815135283832939431), (Int.negOfNat 389534433063071458854846278303133), (Int.ofNat 13029225105448582995329118891099), (Int.ofNat 7851673376486409198997007634892), (Int.negOfNat 330652323836635515093159026182), (Int.negOfNat 145491157392330384019470246387), (Int.ofNat 4327285833354615148772080620), (Int.ofNat 1509836276435047144588281427), (Int.negOfNat 36167457550877660013270867), (Int.negOfNat 9451040518254051181300818), (Int.ofNat 199836051731582295342995), (Int.ofNat 39352646346600117648875), (Int.negOfNat 765419764930531236582), (Int.negOfNat 115570136240909771542), (Int.ofNat 1940027786792504901), (Int.ofNat 188272987373666806), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(2958857612241972359295550681696847/2251799813685248000000000000000000), (601551305040076815135283832939431/11258999068426240000000000000000000), (-389534433063071458854846278303133/11258999068426240000000000000000000), (13029225105448582995329118891099/11258999068426240000000000000000000), (1962918344121602299749251908723/2814749767106560000000000000000000), (-165326161918317757546579513091/5629499534213120000000000000000000), (-145491157392330384019470246387/11258999068426240000000000000000000), (216364291667730757438604031/562949953421312000000000000000000), (1509836276435047144588281427/11258999068426240000000000000000000), (-36167457550877660013270867/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial125.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial125.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial125.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial125 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 14650133982902936288126444627041310), (Int.negOfNat 600012524122737872381957277766151), (Int.negOfNat 178942834294267204236741334981458), (Int.ofNat 44139804483170991191392935289635), (Int.negOfNat 1541475524442285815274387319617), (Int.negOfNat 1176238769312211082243977161050), (Int.ofNat 33163956518382651718402834891), (Int.ofNat 16125807848128872610208616618), (Int.negOfNat 318253243394623473198018702), (Int.negOfNat 127151208661958013418046329), (Int.ofNat 2040264387806587960583466), (Int.ofNat 643747332380539380942716), (Int.negOfNat 9071817955061368336674), (Int.negOfNat 2259864557761732757963), (Int.ofNat 27971121360972584502), (Int.ofNat 5569816741231991310), (Int.negOfNat 138592638686145290), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(1465013398290293628812644462704131/1125899906842624000000000000000000), (-600012524122737872381957277766151/11258999068426240000000000000000000), (-89471417147133602118370667490729/5629499534213120000000000000000000), (8827960896634198238278587057927/2251799813685248000000000000000000), (-1541475524442285815274387319617/11258999068426240000000000000000000), (-23524775386244221644879543221/225179981368524800000000000000000), (33163956518382651718402834891/11258999068426240000000000000000000), (8062903924064436305104308309/5629499534213120000000000000000000), (-159126621697311736599009351/5629499534213120000000000000000000), (-127151208661958013418046329/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial125.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial125.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial125.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial125 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 13029196159307918254272166465611520), (Int.negOfNat 916542173319260091632771264796159), (Int.negOfNat 27518178684624904528299938313328), (Int.negOfNat 2101861640250824285288899397960), (Int.negOfNat 7615236248623326006966408343242), (Int.ofNat 211251075536374382846488961028), (Int.ofNat 153210740661565156707942196819), (Int.negOfNat 2375063802212680992191883134), (Int.negOfNat 1545017567297081342937149902), (Int.ofNat 16973742302192498548933549), (Int.ofNat 9589659101251384463679686), (Int.negOfNat 86967863345706484221096), (Int.negOfNat 40264417139046479451234), (Int.ofNat 311292775634907320803), (Int.ofNat 121450716862497655982), (Int.negOfNat 760528876907728090), (Int.negOfNat 221793676452740490), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(10179059499459311136150130051259/8796093022208000000000000000000), (-916542173319260091632771264796159/11258999068426240000000000000000000), (-1719886167789056533018746144583/703687441776640000000000000000000), (-52546541006270607132222484949/281474976710656000000000000000000), (-3807618124311663003483204171621/5629499534213120000000000000000000), (52812768884093595711622240257/2814749767106560000000000000000000), (153210740661565156707942196819/11258999068426240000000000000000000), (-1187531901106340496095941567/5629499534213120000000000000000000), (-772508783648540671468574951/5629499534213120000000000000000000), (16973742302192498548933549/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial125.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial125.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial125.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial125 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 10963264585812347491940886520406643), (Int.negOfNat 1251768098456976407995034742966429), (Int.negOfNat 173405457664340847740810634024774), (Int.negOfNat 33928179245865635346078740818796), (Int.ofNat 1483262974324544763587987811891), (Int.ofNat 1263225781136340781434640332744), (Int.negOfNat 12963719526339715351310495691), (Int.negOfNat 16839965612800216044021653272), (Int.ofNat 87629928541920014818566175), (Int.ofNat 129487083026886210177488071), (Int.negOfNat 500559862101391748951938), (Int.negOfNat 654429888921454659743775), (Int.ofNat 2093714935349823054755), (Int.ofNat 2335288604310605228582), (Int.negOfNat 5405553468397740142), (Int.negOfNat 6209210537261977361), (Int.ofNat 105071949607071606), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(10963264585812347491940886520406643/11258999068426240000000000000000000), (-1251768098456976407995034742966429/11258999068426240000000000000000000), (-86702728832170423870405317012387/5629499534213120000000000000000000), (-8482044811466408836519685204699/2814749767106560000000000000000000), (1483262974324544763587987811891/11258999068426240000000000000000000), (157903222642042597679330041593/1407374883553280000000000000000000), (-12963719526339715351310495691/11258999068426240000000000000000000), (-2104995701600027005502706659/1407374883553280000000000000000000), (3505197141676800592742647/450359962737049600000000000000000), (129487083026886210177488071/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial125.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial125.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial125.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial125 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 7555938268433488580450141870782569), (Int.negOfNat 2213660630518363726505080428278080), (Int.negOfNat 254015887382095065379455227124137), (Int.ofNat 17781108101803628749895538012888), (Int.ofNat 9209471907724703374011058765391), (Int.negOfNat 29020817344323415265166888106), (Int.negOfNat 162633064812786110149298459775), (Int.negOfNat 430326889767332092719126317), (Int.ofNat 1571291066343447035018999211), (Int.ofNat 3674426297516778493589192), (Int.negOfNat 9645914564721161438334435), (Int.negOfNat 15332727760355278811120), (Int.ofNat 40938107612824999572855), (Int.ofNat 61334923841995608198), (Int.negOfNat 126644935477892574789), (Int.negOfNat 630376726814290949), (Int.ofNat 272074710071351016), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(7555938268433488580450141870782569/11258999068426240000000000000000000), (-6917689470369886645328376338369/35184372088832000000000000000000), (-254015887382095065379455227124137/11258999068426240000000000000000000), (2222638512725453593736942251611/1407374883553280000000000000000000), (9209471907724703374011058765391/11258999068426240000000000000000000), (-14510408672161707632583444053/5629499534213120000000000000000000), (-6505322592511444405971938391/450359962737049600000000000000000), (-430326889767332092719126317/11258999068426240000000000000000000), (1571291066343447035018999211/11258999068426240000000000000000000), (459303287189597311698649/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial125.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial125.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial125.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial125 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 2391155998180525848703227922151511), (Int.negOfNat 2753818879019669503486644171554535), (Int.ofNat 34779168632903118422890497049241), (Int.ofNat 66725011059015666344206177872252), (Int.ofNat 690242221540917835989297630131), (Int.negOfNat 1379615098747131557507747322470), (Int.negOfNat 20502352865426323564141308409), (Int.ofNat 16888137741508996706241183515), (Int.ofNat 184002957230307785179806706), (Int.negOfNat 127664225734243232162353374), (Int.negOfNat 947605008619740396252560), (Int.ofNat 650587129001643944746693), (Int.ofNat 3538576333428555333562), (Int.negOfNat 2380217346212640277908), (Int.negOfNat 11699575529575700061), (Int.ofNat 6537389104076508231), (Int.negOfNat 105071949607071606), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(2391155998180525848703227922151511/11258999068426240000000000000000000), (-550763775803933900697328834310907/2251799813685248000000000000000000), (34779168632903118422890497049241/11258999068426240000000000000000000), (16681252764753916586051544468063/2814749767106560000000000000000000), (690242221540917835989297630131/11258999068426240000000000000000000), (-137961509874713155750774732247/1125899906842624000000000000000000), (-20502352865426323564141308409/11258999068426240000000000000000000), (3377627548301799341248236703/2251799813685248000000000000000000), (92001478615153892589903353/5629499534213120000000000000000000), (-63832112867121616081176687/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial125.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial125.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial125.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial125 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.negOfNat 2475837175672102003168571514395041), (Int.negOfNat 1898757376990530431963788253467159), (Int.ofNat 347502825212344160436056325036246), (Int.ofNat 22895366659084812695796937888384), (Int.negOfNat 9901701752155443171513160934510), (Int.negOfNat 370799734156499152432108975247), (Int.ofNat 156878097990485307233882459807), (Int.ofNat 3807813160057845108132397725), (Int.negOfNat 1492652602522820840811208843), (Int.negOfNat 23173918482655523323742617), (Int.ofNat 9279364448285071182765372), (Int.ofNat 95891614873406452135628), (Int.negOfNat 40442650388488871573172), (Int.negOfNat 312356957410906406321), (Int.ofNat 130390550264034724951), (Int.ofNat 1176236779583261918), (Int.negOfNat 322355743689961542), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-2475837175672102003168571514395041/11258999068426240000000000000000000), (-1898757376990530431963788253467159/11258999068426240000000000000000000), (173751412606172080218028162518123/5629499534213120000000000000000000), (178870052024100099185913577253/87960930222080000000000000000000), (-990170175215544317151316093451/1125899906842624000000000000000000), (-370799734156499152432108975247/11258999068426240000000000000000000), (156878097990485307233882459807/11258999068426240000000000000000000), (152312526402313804325295909/450359962737049600000000000000000), (-1492652602522820840811208843/11258999068426240000000000000000000), (-23173918482655523323742617/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial125.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial125.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial125.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial125 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.negOfNat 4860327368433279992188933829880120), (Int.negOfNat 550227890011446868384056854644823), (Int.ofNat 255105043501278509462757114504768), (Int.negOfNat 46574750378570314195870854676447), (Int.negOfNat 4772374308245308367473840560488), (Int.ofNat 1189761343866598795111192054856), (Int.ofNat 57673355093302769872716394274), (Int.negOfNat 14999667548242459008644705476), (Int.negOfNat 421382287881555794719018826), (Int.ofNat 116919136272802256022972335), (Int.ofNat 2006449449217515537063586), (Int.negOfNat 617460430212339576603543), (Int.negOfNat 6957892102268193779919), (Int.ofNat 2352174685801556612401), (Int.ofNat 19736752156998464000), (Int.negOfNat 6419516153500281085), (Int.ofNat 105071949607071606), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-121508184210831999804723345747003/281474976710656000000000000000000), (-550227890011446868384056854644823/11258999068426240000000000000000000), (3986016304707476710355579914137/175921860444160000000000000000000), (-46574750378570314195870854676447/11258999068426240000000000000000000), (-596546788530663545934230070061/1407374883553280000000000000000000), (148720167983324849388899006857/1407374883553280000000000000000000), (28836677546651384936358197137/5629499534213120000000000000000000), (-3749916887060614752161176369/2814749767106560000000000000000000), (-210691143940777897359509413/5629499534213120000000000000000000), (23383827254560451204594467/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial125.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial125.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial125.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial125 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.negOfNat 5349522696471923725624774590549571), (Int.negOfNat 142045198718155162747676933164522), (Int.negOfNat 40148425942701567901013765915365), (Int.negOfNat 36457282928721719650054228347584), (Int.ofNat 6386069385504658738368671832060), (Int.ofNat 666791419018007145352877352583), (Int.negOfNat 123230839151566269164991751792), (Int.negOfNat 6159820015149486567236676041), (Int.ofNat 1269320638165519172110044122), (Int.ofNat 34998609924774064129505186), (Int.negOfNat 8352599956710370923680411), (Int.negOfNat 135619985184791177570912), (Int.ofNat 38277707355374874798078), (Int.ofNat 398910860843360368152), (Int.negOfNat 129521873762713770532), (Int.negOfNat 907317735091664347), (Int.ofNat 372636777308572068), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-5349522696471923725624774590549571/11258999068426240000000000000000000), (-71022599359077581373838466582261/5629499534213120000000000000000000), (-8029685188540313580202753183073/2251799813685248000000000000000000), (-569645045761276869532097317931/175921860444160000000000000000000), (319303469275232936918433591603/562949953421312000000000000000000), (666791419018007145352877352583/11258999068426240000000000000000000), (-7701927446972891822811984487/703687441776640000000000000000000), (-6159820015149486567236676041/11258999068426240000000000000000000), (634660319082759586055022061/5629499534213120000000000000000000), (17499304962387032064752593/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial125.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial125.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial125.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial125 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 5970691663706366087741349052205054), (Int.negOfNat 507511608958360861688188110687087), (Int.negOfNat 83659487612617956004609973514876), (Int.ofNat 20469577903688298725966422158108), (Int.ofNat 5385013488137976958604958985503), (Int.negOfNat 757676741570832043125497782432), (Int.negOfNat 71603081022468307157892927869), (Int.ofNat 11411960431950964952920563598), (Int.ofNat 511812908590778888113186701), (Int.negOfNat 98078636224423335263007524), (Int.negOfNat 2316847809505954483775097), (Int.ofNat 554766525141276327781796), (Int.ofNat 7327384062448510286700), (Int.negOfNat 2236732718327866218618), (Int.negOfNat 18197176642223982627), (Int.ofNat 6698167218555209528), (Int.negOfNat 121832294146608448), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-2985345831853183043870674526102527/5629499534213120000000000000000000), (-507511608958360861688188110687087/11258999068426240000000000000000000), (-20914871903154489001152493378719/2814749767106560000000000000000000), (5117394475922074681491605539527/2814749767106560000000000000000000), (5385013488137976958604958985503/11258999068426240000000000000000000), (-23677398174088501347671805701/351843720888320000000000000000000), (-71603081022468307157892927869/11258999068426240000000000000000000), (5705980215975482476460281799/5629499534213120000000000000000000), (511812908590778888113186701/11258999068426240000000000000000000), (-24519659056105833815751881/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial125.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial125.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial125.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial125 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 7097723931838891140196823103867426), (Int.negOfNat 493150995072064233551375181119464), (Int.ofNat 98722553788843622622552742389962), (Int.ofNat 28554735181752134145042544234019), (Int.negOfNat 3122407292049831975132773536725), (Int.negOfNat 629014835846336721278715340365), (Int.ofNat 79941111204995327746371273429), (Int.ofNat 6125865666327494480971188498), (Int.negOfNat 970376631683998312890794921), (Int.negOfNat 34084042961104674930926284), (Int.ofNat 7048127620383057589578917), (Int.ofNat 121347045372035541548916), (Int.negOfNat 34647635267505343149380), (Int.negOfNat 299072278479736881918), (Int.ofNat 123480830010716206407), (Int.ofNat 769257897126218948), (Int.negOfNat 406157466387645752), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-3548861965919445570098411551933713/5629499534213120000000000000000000), (-61643874384008029193921897639933/1407374883553280000000000000000000), (49361276894421811311276371194981/5629499534213120000000000000000000), (28554735181752134145042544234019/11258999068426240000000000000000000), (-124896291681993279005310941469/450359962737049600000000000000000), (-125802967169267344255743068073/2251799813685248000000000000000000), (79941111204995327746371273429/11258999068426240000000000000000000), (3062932833163747240485594249/5629499534213120000000000000000000), (-970376631683998312890794921/11258999068426240000000000000000000), (-8521010740276168732731571/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial125.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial125.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial125.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial125 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 7525143018854634033620096336174600), (Int.ofNat 111215307950627953436748934685443), (Int.ofNat 166280745467935830102184136190903), (Int.negOfNat 7176718096061932940883863987242), (Int.negOfNat 4029616501057178309219504194988), (Int.ofNat 398348101523176093176354038622), (Int.ofNat 57571753869411823689392610292), (Int.negOfNat 7758823621486600401176147081), (Int.negOfNat 418561772109964095363921282), (Int.ofNat 76817310133460700768187926), (Int.ofNat 1759280540042942973734731), (Int.negOfNat 475255908742626923283832), (Int.negOfNat 4452775488477651475778), (Int.ofNat 2045567837645227906892), (Int.ofNat 6627449757470026152), (Int.negOfNat 6296121942665864167), (Int.ofNat 155352983225682132), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-37625715094273170168100481680873/56294995342131200000000000000000), (111215307950627953436748934685443/11258999068426240000000000000000000), (166280745467935830102184136190903/11258999068426240000000000000000000), (-3588359048030966470441931993621/5629499534213120000000000000000000), (-1007404125264294577304876048747/2814749767106560000000000000000000), (199174050761588046588177019311/5629499534213120000000000000000000), (14392938467352955922348152573/2814749767106560000000000000000000), (-7758823621486600401176147081/11258999068426240000000000000000000), (-209280886054982047681960641/5629499534213120000000000000000000), (38408655066730350384093963/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial125.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial125.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial125.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial125 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 6744105422558396889415856050512612), (Int.ofNat 600467649192504062997416431355143), (Int.ofNat 66591598213963497248340092312569), (Int.negOfNat 18943241599148257356518752268099), (Int.ofNat 1080380273828656236174878700803), (Int.ofNat 405159701220031553856376937488), (Int.negOfNat 47250039253062551537034431534), (Int.negOfNat 4110480658040685788303591316), (Int.ofNat 698466806492696445890989166), (Int.ofNat 21411823135121137677969035), (Int.negOfNat 5682049007480954505345526), (Int.negOfNat 56559020867274341352883), (Int.ofNat 30153706374071427731079), (Int.ofNat 28147539692449311601), (Int.negOfNat 114257118862697815900), (Int.ofNat 529070488253331955), (Int.ofNat 422917810927182594), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-1686026355639599222353964012628153/2814749767106560000000000000000000), (600467649192504062997416431355143/11258999068426240000000000000000000), (66591598213963497248340092312569/11258999068426240000000000000000000), (-18943241599148257356518752268099/11258999068426240000000000000000000), (1080380273828656236174878700803/11258999068426240000000000000000000), (25322481326251972116023558593/703687441776640000000000000000000), (-23625019626531275768517215767/5629499534213120000000000000000000), (-1027620164510171447075897829/2814749767106560000000000000000000), (349233403246348222945494583/5629499534213120000000000000000000), (4282364627024227535593807/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial125.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial125.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial125.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial125 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 5401464655323268659212305127712283), (Int.ofNat 696322148220712529796076979667924), (Int.negOfNat 1542932126513797297754316110299), (Int.negOfNat 2675268005545136480340424840567), (Int.ofNat 1939617416305823562523855501057), (Int.negOfNat 195581265695720843671165642026), (Int.negOfNat 30402616821654721852617001069), (Int.ofNat 5114409251703885218454624965), (Int.ofNat 205779557048477800062961363), (Int.negOfNat 58037546398923680550692777), (Int.negOfNat 542301587267628699771432), (Int.ofNat 392404844933027215394108), (Int.negOfNat 1033333612223211934068), (Int.negOfNat 1800404342621084349401), (Int.ofNat 13712150555588094529), (Int.ofNat 6085468780687630038), (Int.negOfNat 205634016844292658), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-5401464655323268659212305127712283/11258999068426240000000000000000000), (174080537055178132449019244916981/2814749767106560000000000000000000), (-1542932126513797297754316110299/11258999068426240000000000000000000), (-2675268005545136480340424840567/11258999068426240000000000000000000), (1939617416305823562523855501057/11258999068426240000000000000000000), (-97790632847860421835582821013/5629499534213120000000000000000000), (-30402616821654721852617001069/11258999068426240000000000000000000), (1022881850340777043690924993/2251799813685248000000000000000000), (205779557048477800062961363/11258999068426240000000000000000000), (-58037546398923680550692777/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial125.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial125.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial125.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial125 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 4012886882261671857578103792403510), (Int.ofNat 701000937586924371725524030775063), (Int.ofNat 9555806964093037048892172870354), (Int.ofNat 3082441044822476177347938390511), (Int.negOfNat 403325201053033622064690608964), (Int.negOfNat 149053530677369276161721615874), (Int.ofNat 28792905812715482126289159809), (Int.ofNat 1392143465337658594885759215), (Int.negOfNat 493651442347395312084124666), (Int.negOfNat 2338806610932504065001414), (Int.ofNat 4431474160185287283619900), (Int.negOfNat 41763235152762922292607), (Int.negOfNat 25279216437174452943702), (Int.ofNat 363458819159650899392), (Int.ofNat 100823582149336985141), (Int.negOfNat 1430874858001727269), (Int.negOfNat 422917810927182594), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-401288688226167185757810379240351/1125899906842624000000000000000000), (701000937586924371725524030775063/11258999068426240000000000000000000), (4777903482046518524446086435177/5629499534213120000000000000000000), (3082441044822476177347938390511/11258999068426240000000000000000000), (-100831300263258405516172652241/2814749767106560000000000000000000), (-74526765338684638080860807937/5629499534213120000000000000000000), (28792905812715482126289159809/11258999068426240000000000000000000), (278428693067531718977151843/2251799813685248000000000000000000), (-246825721173697656042062333/5629499534213120000000000000000000), (-1169403305466252032500707/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial125.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial125.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial125.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial125 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 2557327445665880941215814440710100), (Int.ofNat 757045427406318864049700285604503), (Int.ofNat 13445042851493211394235835536780), (Int.negOfNat 1553400181222010386629666216718), (Int.negOfNat 283984363516229125515765691493), (Int.ofNat 119684004828006625251278882634), (Int.ofNat 4350668783136379820969400635), (Int.negOfNat 3370052777226524753525083017), (Int.ofNat 38726948972992003956694589), (Int.ofNat 42331987163578336436384312), (Int.negOfNat 1000250158613751753574265), (Int.negOfNat 311412869996619038878380), (Int.ofNat 8060653734623378002905), (Int.ofNat 1518716386643652000558), (Int.negOfNat 37762976228955576711), (Int.negOfNat 5060036521448827369), (Int.ofNat 255915050462903184), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-25573274456658809412158144407101/112589990684262400000000000000000), (757045427406318864049700285604503/11258999068426240000000000000000000), (672252142574660569711791776839/562949953421312000000000000000000), (-776700090611005193314833108359/5629499534213120000000000000000000), (-283984363516229125515765691493/11258999068426240000000000000000000), (59842002414003312625639441317/5629499534213120000000000000000000), (870133756627275964193880127/2251799813685248000000000000000000), (-3370052777226524753525083017/11258999068426240000000000000000000), (38726948972992003956694589/11258999068426240000000000000000000), (5291498395447292054548039/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial125.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial125.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial125.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial125 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 1002720435803010139122173195325833), (Int.ofNat 792126395747042804029804265940198), (Int.ofNat 5908163507368089378720728023510), (Int.ofNat 40735099888098199153476721866), (Int.ofNat 419264922535866159772372564348), (Int.negOfNat 24511805119747731208895293804), (Int.negOfNat 17241649353558451390523932589), (Int.ofNat 1087456987393786989412481068), (Int.ofNat 324851224955019712220922865), (Int.negOfNat 18504346055438486563418109), (Int.negOfNat 3274644954364585042648642), (Int.ofNat 155773200403175021724905), (Int.ofNat 20228633737037925677125), (Int.negOfNat 813132941843567148518), (Int.negOfNat 85133821580489920658), (Int.ofNat 2778730745140880599), (Int.ofNat 422917810927182594), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-1002720435803010139122173195325833/11258999068426240000000000000000000), (396063197873521402014902132970099/5629499534213120000000000000000000), (590816350736808937872072802351/1125899906842624000000000000000000), (20367549944049099576738360933/5629499534213120000000000000000000), (104816230633966539943093141087/2814749767106560000000000000000000), (-6127951279936932802223823451/2814749767106560000000000000000000), (-17241649353558451390523932589/11258999068426240000000000000000000), (271864246848446747353120267/2814749767106560000000000000000000), (64970244991003942444184573/2251799813685248000000000000000000), (-18504346055438486563418109/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial125.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial125.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial125.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial125 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.ofNat 610521208835144184520887887814379), (Int.ofNat 825155635125431946743370956613096), (Int.ofNat 11311499549470190355887358005295), (Int.ofNat 705613044963398373937954248364), (Int.negOfNat 301883337151985966274243828872), (Int.negOfNat 51930843663850456240415950983), (Int.ofNat 14192927905876905149108163121), (Int.ofNat 1691444072496447326211331286), (Int.negOfNat 278508316168741322795183858), (Int.negOfNat 27612572444421459775387751), (Int.ofNat 2661738317364294563155814), (Int.ofNat 232487912560467973619184), (Int.negOfNat 15680411618313819980326), (Int.negOfNat 1216735648816869023837), (Int.ofNat 64011912179467653598), (Int.ofNat 4209236031581599090), (Int.negOfNat 306196084081513710), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(610521208835144184520887887814379/11258999068426240000000000000000000), (103144454390678993342921369576637/1407374883553280000000000000000000), (2262299909894038071177471601059/2251799813685248000000000000000000), (176403261240849593484488562091/2814749767106560000000000000000000), (-37735417143998245784280478609/1407374883553280000000000000000000), (-51930843663850456240415950983/11258999068426240000000000000000000), (14192927905876905149108163121/11258999068426240000000000000000000), (845722036248223663105665643/5629499534213120000000000000000000), (-139254158084370661397591929/5629499534213120000000000000000000), (-27612572444421459775387751/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial125.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial125.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial125.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial125 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.ofNat 2306274006444435998249143382679887), (Int.ofNat 868204057754873249266832318515854), (Int.ofNat 8098120770250148210845131050659), (Int.negOfNat 1167505642700210117817071495241), (Int.ofNat 123962657095607924624238457641), (Int.ofNat 106451829438827456564778452079), (Int.negOfNat 630903651935844284563565731), (Int.negOfNat 3455140159934792559640142562), (Int.negOfNat 148683408133694336383863338), (Int.ofNat 40417949729126617492031471), (Int.ofNat 2178916277581267122443234), (Int.negOfNat 274895028903420782616304), (Int.negOfNat 15257383069875887396866), (Int.ofNat 1269267762357420767697), (Int.ofNat 67401397100726035018), (Int.negOfNat 3958229655025657410), (Int.negOfNat 389397121848108910), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(2306274006444435998249143382679887/11258999068426240000000000000000000), (434102028877436624633416159257927/5629499534213120000000000000000000), (8098120770250148210845131050659/11258999068426240000000000000000000), (-1167505642700210117817071495241/11258999068426240000000000000000000), (123962657095607924624238457641/11258999068426240000000000000000000), (106451829438827456564778452079/11258999068426240000000000000000000), (-630903651935844284563565731/11258999068426240000000000000000000), (-1727570079967396279820071281/5629499534213120000000000000000000), (-74341704066847168191931669/5629499534213120000000000000000000), (40417949729126617492031471/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial125.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial125.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial125.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial125 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.ofNat 4070626033291397676426034793380700), (Int.ofNat 897349018188525366061722189955624), (Int.ofNat 10047423976853746846426182061179), (Int.ofNat 2017843140843153611034692126060), (Int.ofNat 195887429089719935271285063749), (Int.negOfNat 168109753516616067399403039501), (Int.negOfNat 35821358849870227774697974233), (Int.ofNat 400780728618843473412552360), (Int.ofNat 548542306452859059651422733), (Int.ofNat 13915320394946935831919153), (Int.negOfNat 4397947679348056101778402), (Int.negOfNat 161064225007921147218025), (Int.ofNat 23193404863726926583245), (Int.ofNat 923366316929408777218), (Int.negOfNat 87674085788551952658), (Int.negOfNat 3569842235551613039), (Int.ofNat 339716773160587394), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(40706260332913976764260347933807/112589990684262400000000000000000), (112168627273565670757715273744453/1407374883553280000000000000000000), (10047423976853746846426182061179/11258999068426240000000000000000000), (100892157042157680551734606303/562949953421312000000000000000000), (195887429089719935271285063749/11258999068426240000000000000000000), (-168109753516616067399403039501/11258999068426240000000000000000000), (-35821358849870227774697974233/11258999068426240000000000000000000), (10019518215471086835313809/281474976710656000000000000000000), (548542306452859059651422733/11258999068426240000000000000000000), (13915320394946935831919153/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial125.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial125.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial125.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial125 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.ofNat 5917312749548885534398775156332345), (Int.ofNat 948444342870450188723425343610823), (Int.ofNat 6072788532514491482646177309952), (Int.negOfNat 7660175378989892752408124686428), (Int.negOfNat 2914532154838865784612078636121), (Int.negOfNat 328171035860565455417942949970), (Int.ofNat 24918928781162917853222280383), (Int.ofNat 6755140151004642324982116713), (Int.negOfNat 2403636703158013641621387), (Int.negOfNat 64446534598240572312031784), (Int.negOfNat 1306042956103033646106777), (Int.ofNat 391340271394658558886520), (Int.ofNat 10968167930956256792045), (Int.negOfNat 1682860432397907724998), (Int.negOfNat 51622995795114589911), (Int.ofNat 5349135258747676449), (Int.ofNat 339116088229498384), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(1183462549909777106879755031266469/2251799813685248000000000000000000), (948444342870450188723425343610823/11258999068426240000000000000000000), (23721830205134732354086630117/43980465111040000000000000000000), (-1915043844747473188102031171607/2814749767106560000000000000000000), (-2914532154838865784612078636121/11258999068426240000000000000000000), (-32817103586056545541794294997/1125899906842624000000000000000000), (24918928781162917853222280383/11258999068426240000000000000000000), (6755140151004642324982116713/11258999068426240000000000000000000), (-2403636703158013641621387/11258999068426240000000000000000000), (-8055816824780071539003973/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial125.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial125.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial125.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial125 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.ofNat 7722502550758637670024761497090542), (Int.ofNat 768952368234586529910144059036445), (Int.negOfNat 125875565269656014341295558098165), (Int.negOfNat 36686954151581258580066085616601), (Int.negOfNat 3072493415511209302724861358262), (Int.ofNat 408848962370766041252872931068), (Int.ofNat 77565470627786439046491536271), (Int.negOfNat 1670823254231321604963150679), (Int.negOfNat 868394239241103090053984626), (Int.negOfNat 5808518449457256472526178), (Int.ofNat 6098553048666035309796464), (Int.ofNat 110276173231184540543507), (Int.negOfNat 29842143312929005767462), (Int.negOfNat 675879799694595149492), (Int.ofNat 108221747957539224861), (Int.ofNat 2282519255797418769), (Int.negOfNat 339716773160587394), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(3861251275379318835012380748545271/5629499534213120000000000000000000), (153790473646917305982028811807289/2251799813685248000000000000000000), (-25175113053931202868259111619633/2251799813685248000000000000000000), (-36686954151581258580066085616601/11258999068426240000000000000000000), (-1536246707755604651362430679131/5629499534213120000000000000000000), (102212240592691510313218232767/2814749767106560000000000000000000), (77565470627786439046491536271/11258999068426240000000000000000000), (-1670823254231321604963150679/11258999068426240000000000000000000), (-434197119620551545026992313/5629499534213120000000000000000000), (-2904259224728628236263089/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial125.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial125.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial125.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial125 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.ofNat 8431864051770183845186567110657669), (Int.negOfNat 227132081732238768259280277159854), (Int.negOfNat 371047945779226624548780128279142), (Int.negOfNat 34930661345170451793384039725319), (Int.ofNat 4288781681382172388380316023095), (Int.ofNat 847842149409044467379996641548), (Int.negOfNat 26694204296472544189273095203), (Int.negOfNat 10745393397618026415987722361), (Int.ofNat 28004677429508504579047423), (Int.ofNat 87446246064376193628073069), (Int.ofNat 913172311207572812988832), (Int.negOfNat 490866525182881651075628), (Int.negOfNat 8053412988797692098028), (Int.ofNat 2007458612177938520821), (Int.ofNat 36899153838011091849), (Int.negOfNat 6374567517986479118), (Int.negOfNat 288835054610887858), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(8431864051770183845186567110657669/11258999068426240000000000000000000), (-113566040866119384129640138579927/5629499534213120000000000000000000), (-185523972889613312274390064139571/5629499534213120000000000000000000), (-34930661345170451793384039725319/11258999068426240000000000000000000), (857756336276434477676063204619/2251799813685248000000000000000000), (211960537352261116844999160387/2814749767106560000000000000000000), (-26694204296472544189273095203/11258999068426240000000000000000000), (-10745393397618026415987722361/11258999068426240000000000000000000), (28004677429508504579047423/11258999068426240000000000000000000), (87446246064376193628073069/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial125.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial125.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial125.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial125 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.ofNat 6306682286014682618285180963906660), (Int.negOfNat 1935133427733026979391422509164646), (Int.negOfNat 423051676444773066557299280852510), (Int.ofNat 23518069367474226729899469734714), (Int.ofNat 8532062871018998776737730421828), (Int.negOfNat 193550215230075783794030122668), (Int.negOfNat 119441121077635192766037864496), (Int.ofNat 601947185481532269216219580), (Int.ofNat 1139209786859396513198190150), (Int.ofNat 6831586398459988609110257), (Int.negOfNat 7441077651676259246423198), (Int.negOfNat 89191839560754011133957), (Int.ofNat 34744853904608708351619), (Int.ofNat 508323049699933045999), (Int.negOfNat 121002713071815524600), (Int.negOfNat 1920819999903814215), (Int.ofNat 339716773160587394), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(315334114300734130914259048195333/562949953421312000000000000000000), (-967566713866513489695711254582323/5629499534213120000000000000000000), (-42305167644477306655729928085251/1125899906842624000000000000000000), (11759034683737113364949734867357/5629499534213120000000000000000000), (2133015717754749694184432605457/2814749767106560000000000000000000), (-48387553807518945948507530667/2814749767106560000000000000000000), (-7465070067352199547877366531/703687441776640000000000000000000), (30097359274076613460810979/562949953421312000000000000000000), (22784195737187930263963803/225179981368524800000000000000000), (6831586398459988609110257/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial125.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial125.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial125.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial125 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.ofNat 1055392973867079634224080205382413), (Int.negOfNat 3109100274674670577426556106481599), (Int.negOfNat 118932034565487265884309362279601), (Int.ofNat 67223173529679800904562178372898), (Int.ofNat 802785475775751522870647759348), (Int.negOfNat 1111220556307221617800112317427), (Int.negOfNat 3080829908174546879508292432), (Int.ofNat 13080840581050324222618522153), (Int.ofNat 77480838354168479210772786), (Int.negOfNat 102504768940527882322516510), (Int.negOfNat 1013406540292465173570829), (Int.ofNat 556819179797542600825112), (Int.ofNat 6773473576593093243622), (Int.negOfNat 2205539167856019432152), (Int.negOfNat 28090858484210402168), (Int.ofNat 6585220679964713247), (Int.ofNat 238554020992277332), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(1055392973867079634224080205382413/11258999068426240000000000000000000), (-3109100274674670577426556106481599/11258999068426240000000000000000000), (-118932034565487265884309362279601/11258999068426240000000000000000000), (33611586764839900452281089186449/5629499534213120000000000000000000), (200696368943937880717661939837/2814749767106560000000000000000000), (-1111220556307221617800112317427/11258999068426240000000000000000000), (-192551869260909179969268277/703687441776640000000000000000000), (13080840581050324222618522153/11258999068426240000000000000000000), (38740419177084239605386393/5629499534213120000000000000000000), (-10250476894052788232251651/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial125.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial125.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial125.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial125 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 5122020176479699385690031466973838), (Int.negOfNat 2836245842354447616237566730435785), (Int.ofNat 222497749393690501735087518543890), (Int.ofNat 35624816005339949587612587263519), (Int.negOfNat 7148214191804715184535729100988), (Int.negOfNat 213094123012426841228306644464), (Int.ofNat 124584405512473149020101198899), (Int.ofNat 1455202690554610184415511398), (Int.negOfNat 1252060039584246633526500041), (Int.negOfNat 13234970088848155373415096), (Int.ofNat 8168802676529011868172217), (Int.ofNat 93260401365413977620804), (Int.negOfNat 37387331895087720115600), (Int.negOfNat 434879883266042728382), (Int.ofNat 127169887008438579327), (Int.ofNat 1162596728379054072), (Int.negOfNat 322956428621050552), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-2561010088239849692845015733486919/5629499534213120000000000000000000), (-567249168470889523247513346087157/2251799813685248000000000000000000), (22249774939369050173508751854389/1125899906842624000000000000000000), (35624816005339949587612587263519/11258999068426240000000000000000000), (-1787053547951178796133932275247/2814749767106560000000000000000000), (-13318382688276677576769165279/703687441776640000000000000000000), (124584405512473149020101198899/11258999068426240000000000000000000), (727601345277305092207755699/5629499534213120000000000000000000), (-1252060039584246633526500041/11258999068426240000000000000000000), (-1654371261106019421676887/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial125.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial125.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial125.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial125.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial125 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial125 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial125 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 17037604942903365218166150655482179), (Int.ofNat 1366577591172429067123815101976808), (Int.ofNat 604925571113961123972325111420498), (Int.negOfNat 66892312965235051254489274438548), (Int.negOfNat 10612097349088790772298588812911), (Int.ofNat 1418773086084017097422885294911), (Int.ofNat 155505493908535747809981691257), (Int.negOfNat 16798148950675352194287880898), (Int.negOfNat 1496023833845521736000970141), (Int.ofNat 123076860559359743517678196), (Int.ofNat 9513449333519658120951417), (Int.negOfNat 604743792517190812728304), (Int.negOfNat 42550524547977576053400), (Int.ofNat 2111592635993977206282), (Int.ofNat 141557053202533530327), (Int.negOfNat 5478746586607539372), (Int.negOfNat 322956428621050552), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-17037604942903365218166150655482179/11258999068426240000000000000000000), (170822198896553633390476887747101/1407374883553280000000000000000000), (302462785556980561986162555710249/5629499534213120000000000000000000), (-16723078241308762813622318609637/2814749767106560000000000000000000), (-10612097349088790772298588812911/11258999068426240000000000000000000), (1418773086084017097422885294911/11258999068426240000000000000000000), (155505493908535747809981691257/11258999068426240000000000000000000), (-8399074475337676097143940449/5629499534213120000000000000000000), (-1496023833845521736000970141/11258999068426240000000000000000000), (30769215139839935879419549/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial125.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial125.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial125.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 12536788228483594096501694526517864), (Int.ofNat 2778610954934296345945444836801521), (Int.ofNat 86392503871920141141427096961327), (Int.negOfNat 81466965035621533919325363001708), (Int.ofNat 7121004952808182581953757642360), (Int.ofNat 1507041249436037670158286856814), (Int.negOfNat 143451501686629754730804199732), (Int.negOfNat 17866906624688673867819738753), (Int.ofNat 1405107635022722083201694286), (Int.ofNat 136426348916057433859194910), (Int.negOfNat 8605842383367414781785929), (Int.negOfNat 714381000218340157070112), (Int.ofNat 36224637479611835701622), (Int.ofNat 2722038434224028173052), (Int.negOfNat 111056850203491286268), (Int.negOfNat 8023937299374208347), (Int.ofNat 238554020992277332), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-1567098528560449262062711815814733/1407374883553280000000000000000000), (2778610954934296345945444836801521/11258999068426240000000000000000000), (86392503871920141141427096961327/11258999068426240000000000000000000), (-20366741258905383479831340750427/2814749767106560000000000000000000), (178025123820204564548843941059/281474976710656000000000000000000), (753520624718018835079143428407/5629499534213120000000000000000000), (-35862875421657438682701049933/2814749767106560000000000000000000), (-17866906624688673867819738753/11258999068426240000000000000000000), (702553817511361041600847143/5629499534213120000000000000000000), (13642634891605743385919491/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial125.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial125.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial125.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 7134619033318677115691324846887152), (Int.ofNat 2461167854426188324187864921002521), (Int.negOfNat 154346604585989642399546134589300), (Int.ofNat 5918817617896878987263905936999), (Int.ofNat 10565000212228326626083414164243), (Int.negOfNat 896759828147552631804184685178), (Int.negOfNat 181377705606589030551953395166), (Int.ofNat 13383728872178726079156019220), (Int.ofNat 1740954410598551735020754950), (Int.negOfNat 107125785401547098637081857), (Int.negOfNat 10897518153568078932926898), (Int.ofNat 556342790224346330945757), (Int.ofNat 48166179698347634765519), (Int.negOfNat 2040201004773747621199), (Int.negOfNat 158888917382932228900), (Int.ofNat 5277825445192636115), (Int.ofNat 339716773160587394), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-445913689582417319730707802930447/703687441776640000000000000000000), (2461167854426188324187864921002521/11258999068426240000000000000000000), (-1543466045859896423995461345893/112589990684262400000000000000000), (5918817617896878987263905936999/11258999068426240000000000000000000), (10565000212228326626083414164243/11258999068426240000000000000000000), (-448379914073776315902092342589/5629499534213120000000000000000000), (-90688852803294515275976697583/5629499534213120000000000000000000), (669186443608936303957800961/562949953421312000000000000000000), (34819088211971034700415099/225179981368524800000000000000000), (-107125785401547098637081857/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial125.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial125.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial125.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 2651489574409829986806040851403252), (Int.ofNat 2153805308321963202884052837711565), (Int.ofNat 30967893776141454714347245086510), (Int.ofNat 35447598852773173093126341755263), (Int.negOfNat 4137629416044504972947104919428), (Int.negOfNat 1452436755867048014978866806907), (Int.ofNat 102897329623208606634547393555), (Int.ofNat 19226810554763613107695606661), (Int.negOfNat 1141857491816178960005435577), (Int.negOfNat 149147234022245753339280969), (Int.ofNat 7549872317921958373183432), (Int.ofNat 779218578335401486172528), (Int.negOfNat 33745890857119110626728), (Int.negOfNat 2953841066956674653021), (Int.ofNat 109314557014955678549), (Int.ofNat 8292856343865805918), (Int.negOfNat 288835054610887858), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-662872393602457496701510212850813/2814749767106560000000000000000000), (430761061664392640576810567542313/2251799813685248000000000000000000), (3096789377614145471434724508651/1125899906842624000000000000000000), (35447598852773173093126341755263/11258999068426240000000000000000000), (-1034407354011126243236776229857/2814749767106560000000000000000000), (-1452436755867048014978866806907/11258999068426240000000000000000000), (20579465924641721326909478711/2251799813685248000000000000000000), (19226810554763613107695606661/11258999068426240000000000000000000), (-1141857491816178960005435577/11258999068426240000000000000000000), (-149147234022245753339280969/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial125.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial125.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial125.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.ofNat 1959580309799832023788370931057216), (Int.ofNat 2481352449311503568380731362779501), (Int.ofNat 63143949454970331165679638083117), (Int.negOfNat 31224034134911255104084521824664), (Int.negOfNat 8855731700885535395440056264424), (Int.ofNat 664813816237194171625066841178), (Int.ofNat 178304254170229313578174995613), (Int.negOfNat 10277358378297804814218925821), (Int.negOfNat 1800895530619640403162284226), (Int.ofNat 89347122421125213719294878), (Int.ofNat 11421194720494911852367764), (Int.negOfNat 497178006764192224386407), (Int.negOfNat 50488700784558013002562), (Int.ofNat 1942363841876603877192), (Int.ofNat 166249984940388860561), (Int.negOfNat 5639524701086240669), (Int.negOfNat 339716773160587394), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(30618442340622375371693295797769/175921860444160000000000000000000), (2481352449311503568380731362779501/11258999068426240000000000000000000), (63143949454970331165679638083117/11258999068426240000000000000000000), (-3903004266863906888010565228083/1407374883553280000000000000000000), (-1106966462610691924430007033053/1407374883553280000000000000000000), (332406908118597085812533420589/5629499534213120000000000000000000), (178304254170229313578174995613/11258999068426240000000000000000000), (-10277358378297804814218925821/11258999068426240000000000000000000), (-900447765309820201581142113/5629499534213120000000000000000000), (44673561210562606859647439/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial125.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial125.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial125.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.ofNat 6814342243635205877609724593064654), (Int.ofNat 2157085183739145827226725393574289), (Int.negOfNat 250367042026911169500915247569321), (Int.negOfNat 55301427772430706191885848780832), (Int.ofNat 4083210681605791924092895596056), (Int.ofNat 1387560341112403300965246052129), (Int.negOfNat 78661843830888097729751308017), (Int.negOfNat 18891262215775611308407755113), (Int.ofNat 913072379939258253631079613), (Int.ofNat 150057322219501954666952284), (Int.negOfNat 6462621738131223126672777), (Int.negOfNat 789058124334159199557120), (Int.ofNat 30878274827441018643945), (Int.ofNat 2985982444985612579298), (Int.negOfNat 107253371745615067111), (Int.negOfNat 8706140704036498349), (Int.ofNat 339116088229498384), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(3407171121817602938804862296532327/5629499534213120000000000000000000), (2157085183739145827226725393574289/11258999068426240000000000000000000), (-250367042026911169500915247569321/11258999068426240000000000000000000), (-1728169617888459568496432774401/351843720888320000000000000000000), (510401335200723990511611949507/1407374883553280000000000000000000), (1387560341112403300965246052129/11258999068426240000000000000000000), (-78661843830888097729751308017/11258999068426240000000000000000000), (-18891262215775611308407755113/11258999068426240000000000000000000), (913072379939258253631079613/11258999068426240000000000000000000), (37514330554875488666738071/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial125.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial125.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial125.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.ofNat 9787216374177013072073515056109705), (Int.ofNat 711340737293399208704165895075509), (Int.negOfNat 402513957795927906636301682545327), (Int.ofNat 12016266217745116054486130869141), (Int.ofNat 9461909784469412560489463572368), (Int.negOfNat 503140097690676354636647656158), (Int.negOfNat 171036259174595455599398155733), (Int.ofNat 8007201764661924340075743240), (Int.ofNat 1750319839821979678474659533), (Int.negOfNat 73369711434471950055969653), (Int.negOfNat 11192059019795225606245402), (Int.ofNat 436308800092491990980725), (Int.ofNat 49471314816781371110045), (Int.negOfNat 1823336857059524690018), (Int.negOfNat 161528205584906034458), (Int.ofNat 5488131061430939839), (Int.ofNat 339716773160587394), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(1957443274835402614414703011221941/2251799813685248000000000000000000), (711340737293399208704165895075509/11258999068426240000000000000000000), (-402513957795927906636301682545327/11258999068426240000000000000000000), (12016266217745116054486130869141/11258999068426240000000000000000000), (591369361529338285030591473273/703687441776640000000000000000000), (-251570048845338177318323828079/5629499534213120000000000000000000), (-171036259174595455599398155733/11258999068426240000000000000000000), (200180044116548108501893581/281474976710656000000000000000000), (1750319839821979678474659533/11258999068426240000000000000000000), (-73369711434471950055969653/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial125.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial125.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial125.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.ofNat 9821740956722952856871986949986210), (Int.negOfNat 519669732663379021325181918223949), (Int.negOfNat 176564759120591975351816110846142), (Int.ofNat 47297759465357864560301078425105), (Int.negOfNat 2051656039445859335522642867963), (Int.negOfNat 1319823009056461654444862579010), (Int.ofNat 59059118003060706670339474969), (Int.ofNat 18000282792043202515630546662), (Int.negOfNat 717551989197005205982306238), (Int.negOfNat 143070469133890433888831871), (Int.ofNat 5415438005086148316711034), (Int.ofNat 750827868900446575691404), (Int.negOfNat 27767418141481227344566), (Int.negOfNat 2826856125166848066597), (Int.ofNat 102410168173023749118), (Int.ofNat 7794807306784311010), (Int.negOfNat 389397121848108910), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(982174095672295285687198694998621/1125899906842624000000000000000000), (-519669732663379021325181918223949/11258999068426240000000000000000000), (-88282379560295987675908055423071/5629499534213120000000000000000000), (9459551893071572912060215685021/2251799813685248000000000000000000), (-2051656039445859335522642867963/11258999068426240000000000000000000), (-131982300905646165444486257901/1125899906842624000000000000000000), (59059118003060706670339474969/11258999068426240000000000000000000), (9000141396021601257815273331/5629499534213120000000000000000000), (-358775994598502602991153119/5629499534213120000000000000000000), (-143070469133890433888831871/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial125.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial125.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial125.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.ofNat 8385297520210606756054008992651560), (Int.negOfNat 811220054782195770137462082997201), (Int.negOfNat 23197285992730573618805732685552), (Int.negOfNat 4322761342584055997900884780720), (Int.negOfNat 7946707841269057282750123293618), (Int.ofNat 353268296711052436354087021912), (Int.ofNat 161684032222596049893033899121), (Int.negOfNat 5877212456888268965157140586), (Int.negOfNat 1638009003841312582537707758), (Int.ofNat 57870814779420108794625651), (Int.ofNat 10374202618622145031517414), (Int.negOfNat 373243873121041555143784), (Int.negOfNat 45504117048904936315126), (Int.ofNat 1677959783831674993837), (Int.ofNat 147457476105218369398), (Int.negOfNat 5647952650991094190), (Int.negOfNat 306196084081513710), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(209632438005265168901350224816289/281474976710656000000000000000000), (-811220054782195770137462082997201/11258999068426240000000000000000000), (-1449830374545660851175358292847/703687441776640000000000000000000), (-54034516782300699973761059759/140737488355328000000000000000000), (-3973353920634528641375061646809/5629499534213120000000000000000000), (44158537088881554544260877739/1407374883553280000000000000000000), (161684032222596049893033899121/11258999068426240000000000000000000), (-2938606228444134482578570293/5629499534213120000000000000000000), (-819004501920656291268853879/5629499534213120000000000000000000), (57870814779420108794625651/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial125.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial125.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial125.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.ofNat 6528858918741544124008915212666297), (Int.negOfNat 1155001267792946440096484946132931), (Int.negOfNat 179301098443540499071119015317726), (Int.negOfNat 33672638767478850497198397577804), (Int.ofNat 2158807361507291538053617042369), (Int.ofNat 1251322986171392309450338546176), (Int.negOfNat 38051229715428666443746062989), (Int.negOfNat 16678572859078890136098100868), (Int.ofNat 509835222776731304509410665), (Int.ofNat 129589662331792609164726409), (Int.negOfNat 4328226407359263405138442), (Int.negOfNat 671431950611622123239905), (Int.ofNat 24315836648794482968325), (Int.ofNat 2501040617203616544418), (Int.negOfNat 96643554535765881458), (Int.negOfNat 7094880603369365899), (Int.ofNat 422917810927182594), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(6528858918741544124008915212666297/11258999068426240000000000000000000), (-1155001267792946440096484946132931/11258999068426240000000000000000000), (-89650549221770249535559507658863/5629499534213120000000000000000000), (-8418159691869712624299599394451/2814749767106560000000000000000000), (2158807361507291538053617042369/11258999068426240000000000000000000), (2443990207366000604395192473/21990232555520000000000000000000), (-38051229715428666443746062989/11258999068426240000000000000000000), (-4169643214769722534024525217/2814749767106560000000000000000000), (101967044555346260901882133/2251799813685248000000000000000000), (129589662331792609164726409/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial125.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial125.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial125.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.ofNat 3302475175376821989263730589943251), (Int.negOfNat 2121075848619337398213794891869780), (Int.negOfNat 248316004922994463203374704291703), (Int.ofNat 19741385659900420957529281115052), (Int.ofNat 8729831950443880252792708346469), (Int.negOfNat 168217369034691086964952583574), (Int.negOfNat 149937077491882869496218270665), (Int.ofNat 3278276725080539418044904317), (Int.ofNat 1449397093068642894356593589), (Int.negOfNat 41230374128829087263746412), (Int.negOfNat 9005301479466170589332365), (Int.ofNat 306485592193078581527980), (Int.ofNat 39027608594262849865205), (Int.negOfNat 1503014831439319679858), (Int.negOfNat 124565545599995114411), (Int.ofNat 5060036521448827369), (Int.ofNat 255915050462903184), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(3302475175376821989263730589943251/11258999068426240000000000000000000), (-106053792430966869910689744593489/562949953421312000000000000000000), (-248316004922994463203374704291703/11258999068426240000000000000000000), (4935346414975105239382320278763/2814749767106560000000000000000000), (8729831950443880252792708346469/11258999068426240000000000000000000), (-84108684517345543482476291787/5629499534213120000000000000000000), (-29987415498376573899243654133/2251799813685248000000000000000000), (3278276725080539418044904317/11258999068426240000000000000000000), (1449397093068642894356593589/11258999068426240000000000000000000), (-10307593532207271815936603/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial125.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial125.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial125.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 1649549966766328704692609480695731), (Int.negOfNat 2637517859226222139337175487096225), (Int.ofNat 34723565322915183720072096210199), (Int.ofNat 62951412481390612553973910443768), (Int.ofNat 322633625533824497810672936109), (Int.negOfNat 1186082486232326228335273076770), (Int.ofNat 6755060049967298767326425509), (Int.ofNat 14283916752687090073781401385), (Int.negOfNat 280808747649423865690278766), (Int.negOfNat 108382070072186699297496886), (Int.ofNat 3224739245164725671295200), (Int.ofNat 555668569118931441672107), (Int.negOfNat 20631053210147177575602), (Int.negOfNat 2046215527857704271992), (Int.ofNat 87875132574651529241), (Int.ofNat 5747024716230212569), (Int.negOfNat 422917810927182594), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-1649549966766328704692609480695731/11258999068426240000000000000000000), (-105500714369048885573487019483849/450359962737049600000000000000000), (34723565322915183720072096210199/11258999068426240000000000000000000), (7868926560173826569246738805471/1407374883553280000000000000000000), (322633625533824497810672936109/11258999068426240000000000000000000), (-118608248623232622833527307677/1125899906842624000000000000000000), (6755060049967298767326425509/11258999068426240000000000000000000), (2856783350537418014756280277/2251799813685248000000000000000000), (-140404373824711932845139383/5629499534213120000000000000000000), (-54191035036093349648748443/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial125.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial125.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial125.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 6312734998613687723800270760717699), (Int.negOfNat 1820587900177065540861116994922361), (Int.ofNat 335557133502942397506181513576854), (Int.ofNat 26153268920400072649906198746776), (Int.negOfNat 7821340824622152566123525462690), (Int.negOfNat 209699645822650458952103657633), (Int.ofNat 119906965724089953891704938773), (Int.negOfNat 487720493546394674634634665), (Int.negOfNat 1144843301915194532569279037), (Int.ofNat 25639630661915711923362977), (Int.ofNat 7113673813537360689940068), (Int.negOfNat 242649010342979373129208), (Int.negOfNat 30667483818895928973668), (Int.ofNat 1310947611229144371801), (Int.ofNat 96678142274868978629), (Int.negOfNat 4646752161278134938), (Int.negOfNat 205634016844292658), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-6312734998613687723800270760717699/11258999068426240000000000000000000), (-1820587900177065540861116994922361/11258999068426240000000000000000000), (167778566751471198753090756788427/5629499534213120000000000000000000), (3269158615050009081238274843347/1407374883553280000000000000000000), (-782134082462215256612352546269/1125899906842624000000000000000000), (-209699645822650458952103657633/11258999068426240000000000000000000), (119906965724089953891704938773/11258999068426240000000000000000000), (-97544098709278934926926933/2251799813685248000000000000000000), (-1144843301915194532569279037/11258999068426240000000000000000000), (25639630661915711923362977/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial125.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial125.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial125.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 8526969616275013759989634366378500), (Int.negOfNat 409855609671778410568309227276597), (Int.ofNat 314578392103149756078739197838412), (Int.negOfNat 27711164921286657568568732355813), (Int.negOfNat 3957290611352696124686778453292), (Int.ofNat 774610487767501976846611496484), (Int.ofNat 20935583400102702353984272266), (Int.negOfNat 10165037863586301617388624584), (Int.ofNat 101937053359359553045996166), (Int.ofNat 79944119346604556784060865), (Int.negOfNat 2321041673452818208683126), (Int.negOfNat 414651948182467422037217), (Int.ofNat 17171939752725846526579), (Int.ofNat 1516199292749580887799), (Int.negOfNat 77809631170990606700), (Int.negOfNat 3886075933542153855), (Int.ofNat 422917810927182594), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-17053939232550027519979268732757/22517998136852480000000000000000), (-409855609671778410568309227276597/11258999068426240000000000000000000), (78644598025787439019684799459603/2814749767106560000000000000000000), (-27711164921286657568568732355813/11258999068426240000000000000000000), (-989322652838174031171694613323/2814749767106560000000000000000000), (193652621941875494211652874121/2814749767106560000000000000000000), (10467791700051351176992136133/5629499534213120000000000000000000), (-1270629732948287702173578073/1407374883553280000000000000000000), (50968526679679776522998083/5629499534213120000000000000000000), (15988823869320911356812173/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial125.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial125.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial125.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 8348483065569783513237409206704729), (Int.ofNat 450997727581365591603013398919442), (Int.ofNat 114012910947028315679875972698865), (Int.negOfNat 30166199632986488120371746061936), (Int.ofNat 2589174956611498914734115593540), (Int.ofNat 349982479124594352617162663137), (Int.negOfNat 68884121273306360756642351308), (Int.negOfNat 877312426710442261284481319), (Int.ofNat 756802482883024673965814618), (Int.negOfNat 16031945281280731890503526), (Int.negOfNat 4940124203629384104053469), (Int.ofNat 193255380663362715585132), (Int.ofNat 21513736936326679264022), (Int.negOfNat 1122391340190801884392), (Int.negOfNat 66747097832414223948), (Int.ofNat 4377833116786537367), (Int.ofNat 155352983225682132), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-8348483065569783513237409206704729/11258999068426240000000000000000000), (225498863790682795801506699459721/5629499534213120000000000000000000), (22802582189405663135975194539773/2251799813685248000000000000000000), (-1885387477061655507523234128871/703687441776640000000000000000000), (129458747830574945736705779677/562949953421312000000000000000000), (349982479124594352617162663137/11258999068426240000000000000000000), (-17221030318326590189160587827/2814749767106560000000000000000000), (-877312426710442261284481319/11258999068426240000000000000000000), (378401241441512336982907309/5629499534213120000000000000000000), (-8015972640640365945251763/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial125.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial125.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial125.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 7183479256623426204534202701844146), (Int.ofNat 643003759497663076678297781271587), (Int.ofNat 7264868028044345748422333567176), (Int.negOfNat 5761916309421191015798921135428), (Int.ofNat 2437311023236444162098633400517), (Int.negOfNat 275959752841625891810446563348), (Int.negOfNat 19933282969966062260490322871), (Int.ofNat 5601265221340464729656679602), (Int.negOfNat 50644872012688127085857821), (Int.negOfNat 50040620803908850712784816), (Int.ofNat 1815325241205161557871817), (Int.ofNat 270376793011866252908484), (Int.negOfNat 14377608418303968378580), (Int.negOfNat 984929009653760767082), (Int.ofNat 66829145842690003107), (Int.ofNat 2587747548162602952), (Int.negOfNat 406157466387645752), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-3591739628311713102267101350922073/5629499534213120000000000000000000), (643003759497663076678297781271587/11258999068426240000000000000000000), (908108503505543218552791695897/1407374883553280000000000000000000), (-1440479077355297753949730283857/2814749767106560000000000000000000), (2437311023236444162098633400517/11258999068426240000000000000000000), (-68989938210406472952611640837/2814749767106560000000000000000000), (-19933282969966062260490322871/11258999068426240000000000000000000), (2800632610670232364828339801/5629499534213120000000000000000000), (-50644872012688127085857821/11258999068426240000000000000000000), (-3127538800244303169549051/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial125.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial125.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial125.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 5884936338920134800458992340756114), (Int.ofNat 657364373384004268367989430332864), (Int.ofNat 7798198148200328700459377922938), (Int.ofNat 2323240968639493037130933128821), (Int.negOfNat 174704827149354198459098636615), (Int.negOfNat 147297847116978820484021362515), (Int.ofNat 28271313152493082848968668431), (Int.ofNat 315170455716994257707304502), (Int.negOfNat 407918851080531297691750399), (Int.ofNat 13953972459409809619296424), (Int.ofNat 2915954569671941547932003), (Int.negOfNat 163042686757374533324396), (Int.negOfNat 12942642786752864484100), (Int.ofNat 952731430194368569618), (Int.ofNat 38454507525802220673), (Int.negOfNat 3341161773266387628), (Int.negOfNat 121832294146608448), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-2942468169460067400229496170378057/5629499534213120000000000000000000), (10271318334125066693249834848951/175921860444160000000000000000000), (3899099074100164350229688961469/5629499534213120000000000000000000), (2323240968639493037130933128821/11258999068426240000000000000000000), (-34940965429870839691819727323/2251799813685248000000000000000000), (-29459569423395764096804272503/2251799813685248000000000000000000), (28271313152493082848968668431/11258999068426240000000000000000000), (157585227858497128853652251/5629499534213120000000000000000000), (-407918851080531297691750399/11258999068426240000000000000000000), (1744246557426226202412053/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial125.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial125.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial125.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.negOfNat 4526182649754958036916394426429040), (Int.ofNat 704258234250208770039281860141197), (Int.ofNat 12119408578200423564760337087537), (Int.negOfNat 885634800329183386103369128798), (Int.negOfNat 232722072163288964891051545952), (Int.ofNat 81539161629487484750458212658), (Int.ofNat 3225035991151915281043209808), (Int.negOfNat 2476316033047556095223952359), (Int.ofNat 93956383172530402780308222), (Int.ofNat 25786754927405904748179214), (Int.negOfNat 1653195213038043845892211), (Int.negOfNat 146380542894473030127788), (Int.ofNat 12311194930570544058278), (Int.ofNat 524265636611065654348), (Int.negOfNat 56147326172829520432), (Int.negOfNat 1010971090787662453), (Int.ofNat 372636777308572068), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-56577283121936975461454930330363/140737488355328000000000000000000), (704258234250208770039281860141197/11258999068426240000000000000000000), (12119408578200423564760337087537/11258999068426240000000000000000000), (-442817400164591693051684564399/5629499534213120000000000000000000), (-7272564755102780152845360811/351843720888320000000000000000000), (40769580814743742375229106329/5629499534213120000000000000000000), (201564749446994705065200613/703687441776640000000000000000000), (-2476316033047556095223952359/11258999068426240000000000000000000), (46978191586265201390154111/5629499534213120000000000000000000), (12893377463702952374089607/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial125.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial125.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial125.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.negOfNat 3077463174714753619450155130349228), (Int.ofNat 740839929532207713059131390193197), (Int.ofNat 7118249612089160761722476938811), (Int.negOfNat 79656141862202770598157301761), (Int.ofNat 265296576936420525608637337197), (Int.negOfNat 9991154879265187172815884968), (Int.negOfNat 10512267559862484018302309526), (Int.ofNat 724149026615471602952489576), (Int.ofNat 175147465251781098125974174), (Int.negOfNat 15563193791076561560942435), (Int.negOfNat 1354557884810620759598814), (Int.ofNat 146249461162597813213443), (Int.ofNat 6023874519077387424581), (Int.negOfNat 807827853359526413001), (Int.negOfNat 16710735534708745200), (Int.ofNat 3062510708211459185), (Int.ofNat 105071949607071606), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-769365793678688404862538782587307/2814749767106560000000000000000000), (740839929532207713059131390193197/11258999068426240000000000000000000), (7118249612089160761722476938811/11258999068426240000000000000000000), (-79656141862202770598157301761/11258999068426240000000000000000000), (265296576936420525608637337197/11258999068426240000000000000000000), (-1248894359908148396601985621/1407374883553280000000000000000000), (-5256133779931242009151154763/5629499534213120000000000000000000), (90518628326933950369061197/1407374883553280000000000000000000), (87573732625890549062987087/5629499534213120000000000000000000), (-3112638758215312312188487/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial125.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial125.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial125.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.negOfNat 1564566832379704297069799134116077), (Int.ofNat 774491625034220975739720534637316), (Int.ofNat 10402759582890866589431794741379), (Int.ofNat 582634255767438238240443390967), (Int.negOfNat 140743511229307134432598650117), (Int.negOfNat 34481177361990378981724009494), (Int.ofNat 6568515444774152178639593649), (Int.ofNat 818875598099645435687592575), (Int.negOfNat 142029743559148508178968443), (Int.negOfNat 9223997254352445303587183), (Int.ofNat 1623389047480081793053872), (Int.ofNat 53864219716641390129272), (Int.negOfNat 10808500181816154533572), (Int.negOfNat 177099773981033571279), (Int.ofNat 47424558544753840851), (Int.ofNat 262479839826233182), (Int.negOfNat 322355743689961542), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-1564566832379704297069799134116077/11258999068426240000000000000000000), (193622906258555243934930133659329/2814749767106560000000000000000000), (10402759582890866589431794741379/11258999068426240000000000000000000), (582634255767438238240443390967/11258999068426240000000000000000000), (-140743511229307134432598650117/11258999068426240000000000000000000), (-17240588680995189490862004747/5629499534213120000000000000000000), (6568515444774152178639593649/11258999068426240000000000000000000), (32755023923985817427503703/450359962737049600000000000000000), (-142029743559148508178968443/11258999068426240000000000000000000), (-9223997254352445303587183/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial125.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial125.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial125.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 27819082687221371339534109758630), (Int.ofNat 817301957380358126350912848369957), (Int.ofNat 9611410274043890079976247302846), (Int.negOfNat 691157532812800351633077960091), (Int.negOfNat 35716605045930303844846301596), (Int.ofNat 44479081837669496464443967594), (Int.ofNat 1535492897321859794821425891), (Int.negOfNat 1212077523484248037574022915), (Int.negOfNat 28839737467663661214039194), (Int.ofNat 16943349051124028799855074), (Int.ofNat 259129906400821216072140), (Int.negOfNat 136681795035475425367193), (Int.negOfNat 1109586893598720034538), (Int.ofNat 697460637514586905308), (Int.ofNat 1248874045109755839), (Int.negOfNat 2221239245848022931), (Int.negOfNat 105071949607071606), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(2781908268722137133953410975863/1125899906842624000000000000000000), (817301957380358126350912848369957/11258999068426240000000000000000000), (4805705137021945039988123651423/5629499534213120000000000000000000), (-691157532812800351633077960091/11258999068426240000000000000000000), (-8929151261482575961211575399/2814749767106560000000000000000000), (22239540918834748232221983797/5629499534213120000000000000000000), (1535492897321859794821425891/11258999068426240000000000000000000), (-242415504696849607514804583/2251799813685248000000000000000000), (-14419868733831830607019597/5629499534213120000000000000000000), (8471674525562014399927537/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial125.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial125.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial125.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 1696135647392575573862229857731880), (Int.ofNat 849630209305075861352264640629697), (Int.ofNat 7745160392312095376522075945800), (Int.ofNat 406877376873620117415187986478), (Int.ofNat 195655593767172970561521201813), (Int.negOfNat 19512546862241310594225111554), (Int.negOfNat 8345318537766860832110788475), (Int.ofNat 338550837621346757238947617), (Int.ofNat 160620922247796144619100211), (Int.negOfNat 2572813262767529320951292), (Int.negOfNat 1640863243868742602576335), (Int.ofNat 10405449956814821460720), (Int.ofNat 9971152753185527710555), (Int.negOfNat 45633368637663287498), (Int.negOfNat 39842366106853037089), (Int.ofNat 630376726814290949), (Int.ofNat 272074710071351016), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(42403391184814389346555746443297/281474976710656000000000000000000), (849630209305075861352264640629697/11258999068426240000000000000000000), (38725801961560476882610379729/56294995342131200000000000000000), (203438688436810058707593993239/5629499534213120000000000000000000), (195655593767172970561521201813/11258999068426240000000000000000000), (-9756273431120655297112555777/5629499534213120000000000000000000), (-333812741510674433284431539/450359962737049600000000000000000), (338550837621346757238947617/11258999068426240000000000000000000), (160620922247796144619100211/11258999068426240000000000000000000), (-643203315691882330237823/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial125.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial125.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial125.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 3431685231268741281000211692629673), (Int.ofNat 888893226410536641237798191716022), (Int.ofNat 11803804286531763475562104930510), (Int.ofNat 296275578289298119423530296054), (Int.negOfNat 256279464645556593853754973528), (Int.negOfNat 36414600085290170438554166056), (Int.ofNat 7845860835530499701911634709), (Int.ofNat 1248849741115112897336033472), (Int.negOfNat 97354069279791577469921625), (Int.negOfNat 18401766750532087576179771), (Int.ofNat 553021590893286613537862), (Int.ofNat 138771138713007558228775), (Int.negOfNat 1993487976406734236445), (Int.negOfNat 647380928950555832682), (Int.ofNat 6104179486878220658), (Int.ofNat 1893060679033492061), (Int.ofNat 105071949607071606), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(3431685231268741281000211692629673/11258999068426240000000000000000000), (444446613205268320618899095858011/5629499534213120000000000000000000), (1180380428653176347556210493051/1125899906842624000000000000000000), (148137789144649059711765148027/5629499534213120000000000000000000), (-32034933080694574231719371691/1407374883553280000000000000000000), (-4551825010661271304819270757/1407374883553280000000000000000000), (7845860835530499701911634709/11258999068426240000000000000000000), (19513277204923639020875523/175921860444160000000000000000000), (-778832554238332619759373/90071992547409920000000000000000), (-18401766750532087576179771/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial125.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial125.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial125.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 5254419847932318657525616818043241), (Int.ofNat 930477753662012770797011209332404), (Int.ofNat 6990606857633276147400888497385), (Int.negOfNat 1515286657358441637332444043924), (Int.ofNat 29588255492217453590390218692), (Int.ofNat 90086377510742889165697498503), (Int.ofNat 5719636344846011964016460819), (Int.negOfNat 1810704582179140646753926166), (Int.negOfNat 185516879624510083194626002), (Int.ofNat 13284500032806150470304351), (Int.ofNat 1877194799993533995318086), (Int.negOfNat 53788097214867097303504), (Int.negOfNat 10440711708455363116434), (Int.ofNat 149931359379898649197), (Int.ofNat 38005152936746940182), (Int.negOfNat 678187742501767010), (Int.negOfNat 221793676452740490), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(5254419847932318657525616818043241/11258999068426240000000000000000000), (232619438415503192699252802333101/2814749767106560000000000000000000), (1398121371526655229480177699477/2251799813685248000000000000000000), (-378821664339610409333111010981/2814749767106560000000000000000000), (7397063873054363397597554673/2814749767106560000000000000000000), (90086377510742889165697498503/11258999068426240000000000000000000), (5719636344846011964016460819/11258999068426240000000000000000000), (-905352291089570323376963083/5629499534213120000000000000000000), (-92758439812255041597313001/5629499534213120000000000000000000), (13284500032806150470304351/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial125.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial125.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial125.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 7134667032623594319288416195142373), (Int.ofNat 948546849214037438419321075497106), (Int.ofNat 5720045596645278788943971723101), (Int.ofNat 1990449339480429506776051952941), (Int.ofNat 634143172096678186759349798599), (Int.negOfNat 37132410305258220624291791679), (Int.negOfNat 26526065136613899236500205809), (Int.negOfNat 1580665216020462654218212518), (Int.ofNat 250615337668687396400424198), (Int.ofNat 24498689257194197021245929), (Int.negOfNat 1196257339698293233684334), (Int.negOfNat 167814492383513587867616), (Int.ofNat 3438217116543971611026), (Int.ofNat 702276194952305459063), (Int.negOfNat 7037649711325129598), (Int.negOfNat 1733239089473337710), (Int.negOfNat 138592638686145290), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(7134667032623594319288416195142373/11258999068426240000000000000000000), (474273424607018719209660537748553/5629499534213120000000000000000000), (5720045596645278788943971723101/11258999068426240000000000000000000), (1990449339480429506776051952941/11258999068426240000000000000000000), (634143172096678186759349798599/11258999068426240000000000000000000), (-37132410305258220624291791679/11258999068426240000000000000000000), (-26526065136613899236500205809/11258999068426240000000000000000000), (-790332608010231327109106259/5629499534213120000000000000000000), (125307668834343698200212099/5629499534213120000000000000000000), (24498689257194197021245929/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial125.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial125.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial125.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 9077697720323237847638320290753940), (Int.ofNat 1007138450441817905099141145732636), (Int.ofNat 23026948709719701741025651459681), (Int.ofNat 1004884253128020957760888790180), (Int.negOfNat 1414348978892404940457150804729), (Int.negOfNat 340597527370178154360662236479), (Int.negOfNat 10276257067605156194770064887), (Int.ofNat 4080696659926152664716214980), (Int.ofNat 308058743065926525765044627), (Int.negOfNat 23286933488647354210779633), (Int.negOfNat 2656929177806881676833818), (Int.ofNat 75408523352988548419705), (Int.ofNat 13074736393545673122075), (Int.negOfNat 134550775199584676218), (Int.negOfNat 41716016444555689742), (Int.negOfNat 21738960913178101), (Int.ofNat 188272987373666806), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(453884886016161892381916014537697/562949953421312000000000000000000), (251784612610454476274785286433159/2814749767106560000000000000000000), (23026948709719701741025651459681/11258999068426240000000000000000000), (50244212656401047888044439509/562949953421312000000000000000000), (-1414348978892404940457150804729/11258999068426240000000000000000000), (-340597527370178154360662236479/11258999068426240000000000000000000), (-10276257067605156194770064887/11258999068426240000000000000000000), (204034832996307633235810749/562949953421312000000000000000000), (308058743065926525765044627/11258999068426240000000000000000000), (-23286933488647354210779633/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial125.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial125.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial125.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 11158521859880191610193401977576315), (Int.ofNat 1038902351856879853638603496376097), (Int.negOfNat 31442899741757963276972805804672), (Int.negOfNat 22902191983975841574883529544192), (Int.negOfNat 4074130722762076619339126839179), (Int.negOfNat 48027382665178152542479424550), (Int.ofNat 58606766349367358253292543257), (Int.ofNat 3802441421373077482367193887), (Int.negOfNat 399587270361817585749448213), (Int.negOfNat 40920184194864343097862596), (Int.ofNat 1521399823283042841501377), (Int.ofNat 238208226934299844060220), (Int.negOfNat 2950748372579158585505), (Int.negOfNat 895614767975086667342), (Int.negOfNat 541564334743739889), (Int.ofNat 2321155219015604531), (Int.ofNat 188873672304755816), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(2231704371976038322038680395515263/2251799813685248000000000000000000), (1038902351856879853638603496376097/11258999068426240000000000000000000), (-245647654232484088101350045349/87960930222080000000000000000000), (-44730843718702815575944393641/21990232555520000000000000000000), (-4074130722762076619339126839179/11258999068426240000000000000000000), (-960547653303563050849588491/225179981368524800000000000000000), (58606766349367358253292543257/11258999068426240000000000000000000), (3802441421373077482367193887/11258999068426240000000000000000000), (-399587270361817585749448213/11258999068426240000000000000000000), (-10230046048716085774465649/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial125.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial125.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial125.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 12864730787434271348993516369857418), (Int.ofNat 516552963863625968915004228202555), (Int.negOfNat 254737241720803163395043311191735), (Int.negOfNat 46813090410787751745897581610639), (Int.negOfNat 556028869550126692912797645118), (Int.ofNat 731873306910862311102116841372), (Int.ofNat 47856929507016836631083944229), (Int.negOfNat 5934610311267802991823205621), (Int.negOfNat 606259211401459040506622114), (Int.ofNat 27198433333578079518768838), (Int.ofNat 4150768276499009903420896), (Int.negOfNat 63033409965398095431907), (Int.negOfNat 18205266590157892477498), (Int.negOfNat 9465121139426380608), (Int.ofNat 54715060538173517159), (Int.ofNat 410450435112668031), (Int.negOfNat 188272987373666806), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(6432365393717135674496758184928709/5629499534213120000000000000000000), (103310592772725193783000845640511/2251799813685248000000000000000000), (-50947448344160632679008662238347/2251799813685248000000000000000000), (-46813090410787751745897581610639/11258999068426240000000000000000000), (-278014434775063346456398822559/5629499534213120000000000000000000), (182968326727715577775529210343/2814749767106560000000000000000000), (47856929507016836631083944229/11258999068426240000000000000000000), (-5934610311267802991823205621/11258999068426240000000000000000000), (-303129605700729520253311057/5629499534213120000000000000000000), (13599216666789039759384419/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial125.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial125.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial125.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 12521072493070810688397274676565731), (Int.negOfNat 1017404366011201595186738828220386), (Int.negOfNat 483829262953178924287806445351838), (Int.negOfNat 18533778453336983997697408829961), (Int.ofNat 7453953327610556772505061555805), (Int.ofNat 620693515188044679845225259732), (Int.negOfNat 72872509651217259817597819577), (Int.negOfNat 8504305539483027119276788899), (Int.ofNat 413309994301014340235962657), (Int.ofNat 67724329166513110710527971), (Int.negOfNat 1190724630333232818271272), (Int.negOfNat 347381559149400573027192), (Int.ofNat 80516157696330832068), (Int.ofNat 1222224214381126018299), (Int.ofNat 13510295681460311771), (Int.negOfNat 3214011785656128662), (Int.negOfNat 239154705923366342), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(12521072493070810688397274676565731/11258999068426240000000000000000000), (-508702183005600797593369414110193/5629499534213120000000000000000000), (-241914631476589462143903222675919/5629499534213120000000000000000000), (-18533778453336983997697408829961/11258999068426240000000000000000000), (1490790665522111354501012311161/2251799813685248000000000000000000), (155173378797011169961306314933/2814749767106560000000000000000000), (-72872509651217259817597819577/11258999068426240000000000000000000), (-8504305539483027119276788899/11258999068426240000000000000000000), (413309994301014340235962657/11258999068426240000000000000000000), (67724329166513110710527971/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial125.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial125.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial125.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 8536188097558218713401968722192720), (Int.negOfNat 2904176897511482227147158230630594), (Int.negOfNat 388656439168775703900908160250910), (Int.ofNat 50575722385103809833754895203566), (Int.ofNat 7613090567645715874962457475212), (Int.negOfNat 665900978940998109317114063132), (Int.negOfNat 108991960516366742936197952104), (Int.ofNat 5020867186146112544265614880), (Int.ofNat 1010502516757382240787603510), (Int.negOfNat 18523869314186330280956657), (Int.negOfNat 6101807276143467736319862), (Int.ofNat 5863191758139376010917), (Int.ofNat 25183495033328804010321), (Int.ofNat 280329969911184415401), (Int.negOfNat 73464795236136191500), (Int.negOfNat 1791827011330895045), (Int.ofNat 188272987373666806), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(106702351219477733917524609027409/140737488355328000000000000000000), (-1452088448755741113573579115315297/5629499534213120000000000000000000), (-38865643916877570390090816025091/1125899906842624000000000000000000), (25287861192551904916877447601783/5629499534213120000000000000000000), (1903272641911428968740614368803/2814749767106560000000000000000000), (-166475244735249527329278515783/2814749767106560000000000000000000), (-13623995064545842867024744013/1407374883553280000000000000000000), (31380419913413203401660093/70368744177664000000000000000000), (101050251675738224078760351/1125899906842624000000000000000000), (-18523869314186330280956657/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial125.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial125.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial125.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 1672225200610120207480980338340247), (Int.negOfNat 3679262748147768167717044388914101), (Int.ofNat 23112995841436778459542061387201), (Int.ofNat 71838001552262755314569293877402), (Int.negOfNat 3201064846648460150927888156588), (Int.negOfNat 1183155771424983024396267957753), (Int.ofNat 43104525623759534745785600332), (Int.ofNat 13329728594801745992897693207), (Int.negOfNat 217428593455860274262699326), (Int.negOfNat 96719644780368417401500950), (Int.ofNat 73046243774128858884309), (Int.ofNat 473109353120539266703468), (Int.ofNat 5093026968232213138078), (Int.negOfNat 1633144451285093627608), (Int.negOfNat 32976279307303779152), (Int.ofNat 3962503036617557933), (Int.ofNat 289435739541976868), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(1672225200610120207480980338340247/11258999068426240000000000000000000), (-3679262748147768167717044388914101/11258999068426240000000000000000000), (23112995841436778459542061387201/11258999068426240000000000000000000), (35919000776131377657284646938701/5629499534213120000000000000000000), (-800266211662115037731972039147/2814749767106560000000000000000000), (-1183155771424983024396267957753/11258999068426240000000000000000000), (10776131405939883686446400083/2814749767106560000000000000000000), (13329728594801745992897693207/11258999068426240000000000000000000), (-108714296727930137131349663/5629499534213120000000000000000000), (-1934392895607368348030019/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial125.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial125.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial125.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 5103861558593711941943662402398102), (Int.negOfNat 2908033245954314047139407461562895), (Int.ofNat 301144573798992625606135138291570), (Int.ofNat 12376212285254726012557836109541), (Int.negOfNat 9326528829980180760225136451212), (Int.ofNat 175936737795461458269272763044), (Int.ofNat 147541345958616821757484881641), (Int.negOfNat 1566133404502148529314505998), (Int.negOfNat 1350342651216176175468986639), (Int.negOfNat 1577508920060974057657964), (Int.ofNat 7993705660646026908555463), (Int.ofNat 88943394328718336534516), (Int.negOfNat 32730349177366437299920), (Int.negOfNat 642700573086706423518), (Int.ofNat 96880563784772190393), (Int.ofNat 2610583190240614248), (Int.negOfNat 205033331913203648), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-2551930779296855970971831201199051/5629499534213120000000000000000000), (-581606649190862809427881492312579/2251799813685248000000000000000000), (30114457379899262560613513829157/1125899906842624000000000000000000), (12376212285254726012557836109541/11258999068426240000000000000000000), (-2331632207495045190056284112803/2814749767106560000000000000000000), (43984184448865364567318190761/2814749767106560000000000000000000), (147541345958616821757484881641/11258999068426240000000000000000000), (-783066702251074264657252999/5629499534213120000000000000000000), (-1350342651216176175468986639/11258999068426240000000000000000000), (-394377230015243514414491/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial125.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial125.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial125.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial125.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial125.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial125.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial125.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial125.reflect := by
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

end Bin125
end
end ErdosOverlap.OuterNumerics
