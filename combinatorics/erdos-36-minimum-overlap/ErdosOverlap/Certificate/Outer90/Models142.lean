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

/-! # Exact integer weighted outer models for source bin 142

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin142

def weightDenominator : ℤ := (Int.ofNat 2000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 593513173007871540)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 587163636514737900)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 459480166863843680)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 248314837808633860)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 168344504371912780)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 98902534344231240)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 86422794932766980)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 107781533567950380)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 33424869914027840)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial142.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial142.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 1952902884190905600)⟩, ⟨(314159265359/50000000000), (Int.ofNat 391753574025879200)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 321307693963396000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 130611540444086740)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 62011300864508700)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 14320770253186194)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 18761059307830566)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 28384590263909698)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 1257665399909617)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial142.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial142.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 1952902884190905600)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 391753574025879200)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 321307693963396000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 130611540444086740)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 62011300864508700)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 14320770253186194)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 18761059307830566)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 28384590263909698)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 1257665399909617)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial142.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial142.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial142.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 1963983768376033577854850573549791), (Int.ofNat 938971776114371518796882470211185), (Int.ofNat 195202308504900486159862884204288), (Int.negOfNat 30571546624581048504057962387721), (Int.negOfNat 5690182037592335392176004399285), (Int.ofNat 637329628112526582794004603767), (Int.ofNat 90725138163690082014446017543), (Int.negOfNat 8083212843440310233821459695), (Int.negOfNat 895684333266886759152241926), (Int.ofNat 66907903595463896589852518), (Int.ofNat 5948822213899946423287875), (Int.negOfNat 387468222072716591378904), (Int.negOfNat 28345160479970136172501), (Int.ofNat 1657621549009784969969), (Int.ofNat 101654460188844168093), (Int.negOfNat 5434457489951055249), (Int.negOfNat 295744481002541576), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1963983768376033577854850573549791/2251799813685248000000000000000000), (187794355222874303759376494042237/450359962737049600000000000000000), (762509017597267524061964391423/8796093022208000000000000000000), (-30571546624581048504057962387721/2251799813685248000000000000000000), (-1138036407518467078435200879857/450359962737049600000000000000000), (637329628112526582794004603767/2251799813685248000000000000000000), (90725138163690082014446017543/2251799813685248000000000000000000), (-1616642568688062046764291939/450359962737049600000000000000000), (-447842166633443379576120963/1125899906842624000000000000000000), (33453951797731948294926259/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial142.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial142.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial142.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial142 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 384130196637968481223024670755125), (Int.ofNat 1234883413291978152474133623593984), (Int.negOfNat 58703609280557856185536545961835), (Int.negOfNat 41783399847374632054251280621381), (Int.ofNat 3190616829422020157980654076595), (Int.ofNat 814933803571808868793580612492), (Int.negOfNat 64784478142690725105554650779), (Int.negOfNat 9616360023669435178218248013), (Int.ofNat 726084088254644368658086125), (Int.ofNat 74171240029100998626046151), (Int.negOfNat 5265969692911933773193828), (Int.negOfNat 400124696258134939631225), (Int.ofNat 26974394060900436926333), (Int.ofNat 1593741667945424149523), (Int.negOfNat 103356301212258566300), (Int.negOfNat 4844823121692968799), (Int.ofNat 318401694301874030), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(3073041573103747849784197366041/18014398509481984000000000000000), (1205940833292947414525521116791/2199023255552000000000000000000), (-11740721856111571237107309192367/450359962737049600000000000000000), (-41783399847374632054251280621381/2251799813685248000000000000000000), (638123365884404031596130815319/450359962737049600000000000000000), (203733450892952217198395153123/562949953421312000000000000000000), (-64784478142690725105554650779/2251799813685248000000000000000000), (-9616360023669435178218248013/2251799813685248000000000000000000), (5808672706037154949264689/18014398509481984000000000000000), (74171240029100998626046151/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial142.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial142.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial142.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial142 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 2356783800726830354002744829774704), (Int.ofNat 650099538521486061993124562729581), (Int.negOfNat 188071941003669954127866212516378), (Int.ofNat 2193730104093135976062152572641), (Int.ofNat 5788786698364563682746901797304), (Int.negOfNat 346593176309986452185895100686), (Int.negOfNat 90002051054900861785431627084), (Int.ofNat 6320899662795850400591643083), (Int.ofNat 841655949849514510036172148), (Int.negOfNat 61144427089146307006714513), (Int.negOfNat 5246238725042298466990394), (Int.ofNat 386173136053853844449807), (Int.ofNat 23371401196258983188906), (Int.negOfNat 1746126562768958982810), (Int.negOfNat 78242985340567984947), (Int.ofNat 5959239564503974233), (Int.ofNat 194212205860548439), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(147298987545426897125171551860919/140737488355328000000000000000000), (650099538521486061993124562729581/2251799813685248000000000000000000), (-94035970501834977063933106258189/1125899906842624000000000000000000), (2193730104093135976062152572641/2251799813685248000000000000000000), (723598337295570460343362724663/281474976710656000000000000000000), (-173296588154993226092947550343/1125899906842624000000000000000000), (-22500512763725215446357906771/562949953421312000000000000000000), (6320899662795850400591643083/2251799813685248000000000000000000), (210413987462378627509043037/562949953421312000000000000000000), (-61144427089146307006714513/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial142.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial142.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial142.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial142 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 2999003161069133878479283837830263), (Int.ofNat 67900567265033228620476011574252), (Int.negOfNat 79880772616444326763055961719270), (Int.ofNat 24897011712010568985510172925732), (Int.negOfNat 663233363020289394687848271759), (Int.negOfNat 671021329587904582521057082022), (Int.ofNat 40703677564675749673464206189), (Int.ofNat 8362052537752592665706425652), (Int.negOfNat 590000984037055151509366572), (Int.negOfNat 62864679324570383875158954), (Int.ofNat 4806045475889055291863731), (Int.ofNat 319572702352341341892291), (Int.negOfNat 26275239526299397526238), (Int.negOfNat 1176749672220756849358), (Int.ofNat 104701819413183373692), (Int.ofNat 3173475704300763110), (Int.negOfNat 314628698102145179), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(2999003161069133878479283837830263/2251799813685248000000000000000000), (16975141816258307155119002893563/562949953421312000000000000000000), (-7988077261644432676305596171927/225179981368524800000000000000000), (6224252928002642246377543231433/562949953421312000000000000000000), (-663233363020289394687848271759/2251799813685248000000000000000000), (-335510664793952291260528541011/1125899906842624000000000000000000), (40703677564675749673464206189/2251799813685248000000000000000000), (2090513134438148166426606413/562949953421312000000000000000000), (-147500246009263787877341643/562949953421312000000000000000000), (-31432339662285191937579477/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial142.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial142.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial142.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial142 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 2985870494010419290307213348411881), (Int.negOfNat 16923741368431488672235450851438), (Int.ofNat 14005652570696607543985812237205), (Int.ofNat 2634485232657729616522722088422), (Int.negOfNat 3429677048821692502377063437992), (Int.ofNat 174047801321986177465847209451), (Int.ofNat 68594064534618233856786708188), (Int.negOfNat 4575004250702524933909261106), (Int.negOfNat 669466900672258051660092512), (Int.ofNat 51127656182757153478964786), (Int.ofNat 4028548510402884209740695), (Int.negOfNat 348466322010597048256331), (Int.negOfNat 16563657245253769451873), (Int.ofNat 1648291455450638241149), (Int.ofNat 49284897093538871380), (Int.negOfNat 5875639984001815129), (Int.negOfNat 93937596118464919), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(2985870494010419290307213348411881/2251799813685248000000000000000000), (-8461870684215744336117725425719/1125899906842624000000000000000000), (2801130514139321508797162447441/450359962737049600000000000000000), (1317242616328864808261361044211/1125899906842624000000000000000000), (-428709631102711562797132929749/281474976710656000000000000000000), (174047801321986177465847209451/2251799813685248000000000000000000), (17148516133654558464196677047/562949953421312000000000000000000), (-2287502125351262466954630553/1125899906842624000000000000000000), (-20920840646008064114377891/70368744177664000000000000000000), (25563828091378576739482393/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial142.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial142.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial142.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial142 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 2983478771541162634450701724402711), (Int.negOfNat 14544041330811957455601576361158), (Int.negOfNat 26116023768396130663107152749618), (Int.negOfNat 10306991708698065426093427990089), (Int.ofNat 639750139809481108579376610625), (Int.ofNat 437107179578906699979632709725), (Int.negOfNat 28289227258109929978117620161), (Int.negOfNat 6123570657069519748198988126), (Int.ofNat 457233237353419921748305489), (Int.ofNat 45981934355426845739212844), (Int.negOfNat 4022845792315334996258921), (Int.negOfNat 217444310624546218626209), (Int.ofNat 23075351244435371151146), (Int.ofNat 695782055289200385270), (Int.negOfNat 94765004413838820091), (Int.negOfNat 1546854650011461061), (Int.ofNat 310855701902416328), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(2983478771541162634450701724402711/2251799813685248000000000000000000), (-7272020665405978727800788180579/1125899906842624000000000000000000), (-13058011884198065331553576374809/1125899906842624000000000000000000), (-10306991708698065426093427990089/2251799813685248000000000000000000), (1023600223695169773727002577/3602879701896396800000000000000), (17484287183156267999185308389/90071992547409920000000000000000), (-28289227258109929978117620161/2251799813685248000000000000000000), (-3061785328534759874099494063/1125899906842624000000000000000000), (457233237353419921748305489/2251799813685248000000000000000000), (11495483588856711434803211/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial142.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial142.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial142.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial142 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 2789235892904271877860732474308268), (Int.negOfNat 194874653343458730785318513946033), (Int.negOfNat 47559435394544828877370118423630), (Int.ofNat 5338136605744307863772879195910), (Int.ofNat 2236196642851659983017182278960), (Int.negOfNat 155603685677438150666947022704), (Int.negOfNat 47197625214466577815753632287), (Int.ofNat 3422333567400652445563099118), (Int.ofNat 466674244486325711667340471), (Int.negOfNat 39874585312359723128260142), (Int.negOfNat 2639319439117109238020446), (Int.ofNat 284047887006661965949774), (Int.ofNat 9275823404759511303645), (Int.negOfNat 1385354305034291936477), (Int.negOfNat 19574638072492082539), (Int.ofNat 5039635541086151479), (Int.negOfNat 6337013623618601), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(697308973226067969465183118577067/562949953421312000000000000000000), (-194874653343458730785318513946033/2251799813685248000000000000000000), (-4755943539454482887737011842363/225179981368524800000000000000000), (533813660574430786377287919591/225179981368524800000000000000000), (27952458035645749787714778487/28147497671065600000000000000000), (-9725230354839884416684188919/140737488355328000000000000000000), (-47197625214466577815753632287/2251799813685248000000000000000000), (1711166783700326222781549559/1125899906842624000000000000000000), (466674244486325711667340471/2251799813685248000000000000000000), (-19937292656179861564130071/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial142.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial142.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial142.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial142 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 2280268134882539064910272786925578), (Int.negOfNat 269097653804782600699401725795765), (Int.ofNat 17292721405494276648312063588267), (Int.ofNat 11962455400450635035655224361753), (Int.negOfNat 854355948629197712917569699258), (Int.negOfNat 318222236596642245186483698346), (Int.ofNat 21759692006604848361099146449), (Int.ofNat 4195492199071643597706593283), (Int.negOfNat 334606473154174949068797549), (Int.negOfNat 29425379736571552558507069), (Int.ofNat 3025828962323239311344543), (Int.ofNat 117529444742132636289169), (Int.negOfNat 17860420564492521576152), (Int.negOfNat 240542285549063973119), (Int.ofNat 74560945242344172972), (Int.negOfNat 125812001005246808), (Int.negOfNat 273657835788659637), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(1140134067441269532455136393462789/1125899906842624000000000000000000), (-53819530760956520139880345159153/450359962737049600000000000000000), (17292721405494276648312063588267/2251799813685248000000000000000000), (11962455400450635035655224361753/2251799813685248000000000000000000), (-427177974314598856458784849629/1125899906842624000000000000000000), (-159111118298321122593241849173/1125899906842624000000000000000000), (21759692006604848361099146449/2251799813685248000000000000000000), (4195492199071643597706593283/2251799813685248000000000000000000), (-334606473154174949068797549/2251799813685248000000000000000000), (-29425379736571552558507069/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial142.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial142.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial142.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial142 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 1884922732817445407507966356220623), (Int.negOfNat 103511091608165781687539661907301), (Int.ofNat 50448571035342347083424508121780), (Int.negOfNat 2478647444346626558249794062085), (Int.negOfNat 2006306341646314398453917080879), (Int.ofNat 112150095062175074011896977601), (Int.ofNat 34097594452215162755354457897), (Int.negOfNat 2317746220551456531526022459), (Int.negOfNat 302242582404358262605998557), (Int.ofNat 27213599708970807487584853), (Int.ofNat 1428147527144120530415271), (Int.negOfNat 198869561893871097682401), (Int.negOfNat 2945851139233482867624), (Int.ofNat 990170171548597718087), (Int.negOfNat 5426579303317082160), (Int.negOfNat 3647539294028081836), (Int.ofNat 70671422651855047), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(1884922732817445407507966356220623/2251799813685248000000000000000000), (-103511091608165781687539661907301/2251799813685248000000000000000000), (2522428551767117354171225406089/112589990684262400000000000000000), (-495729488869325311649958812417/450359962737049600000000000000000), (-2006306341646314398453917080879/2251799813685248000000000000000000), (112150095062175074011896977601/2251799813685248000000000000000000), (34097594452215162755354457897/2251799813685248000000000000000000), (-2317746220551456531526022459/2251799813685248000000000000000000), (-302242582404358262605998557/2251799813685248000000000000000000), (27213599708970807487584853/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial142.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial142.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial142.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial142 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 1833176740536981355070826569691292), (Int.ofNat 18576270351198307411815376543027), (Int.ofNat 2617826792977352258674325282741), (Int.negOfNat 10267251578266130576286372468602), (Int.ofNat 294063231414871623461533347450), (Int.ofNat 251736751847419975681300795628), (Int.negOfNat 12025282779500187309630357291), (Int.negOfNat 2887514012314889158768001918), (Int.ofNat 195939248482575488692454775), (Int.ofNat 16820547471705005115844390), (Int.negOfNat 1836934775620536271638658), (Int.negOfNat 39460658742516904311978), (Int.ofNat 11140661951450449417985), (Int.negOfNat 109915169469595998039), (Int.negOfNat 47380712544183957043), (Int.ofNat 1290834771722299745), (Int.ofNat 204292765160784723), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(458294185134245338767706642422823/562949953421312000000000000000000), (18576270351198307411815376543027/2251799813685248000000000000000000), (2617826792977352258674325282741/2251799813685248000000000000000000), (-5133625789133065288143186234301/1125899906842624000000000000000000), (5881264628297432469230666949/45035996273704960000000000000000), (62934187961854993920325198907/562949953421312000000000000000000), (-12025282779500187309630357291/2251799813685248000000000000000000), (-1443757006157444579384000959/1125899906842624000000000000000000), (7837569939303019547698191/90071992547409920000000000000000), (1682054747170500511584439/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial142.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial142.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial142.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial142 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 1810340798393771561969277939683765), (Int.negOfNat 67983128798332431153303935853066), (Int.negOfNat 36208623660647197694059984070489), (Int.negOfNat 973470112726478689903059888880), (Int.ofNat 1543654539276541915726179394413), (Int.negOfNat 28356922711865653356490825143), (Int.negOfNat 25354796132160094617389769813), (Int.ofNat 950165506633744879852524630), (Int.ofNat 192031045563890825887976353), (Int.negOfNat 12700168783021562233598020), (Int.negOfNat 592277405143918997875141), (Int.ofNat 98878436663426114906457), (Int.negOfNat 1372500772313156417550), (Int.negOfNat 507926911649986387094), (Int.ofNat 21998217943040572353), (Int.ofNat 1788044459467465005), (Int.negOfNat 100323296366154036), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(362068159678754312393855587936753/450359962737049600000000000000000), (-33991564399166215576651967926533/1125899906842624000000000000000000), (-36208623660647197694059984070489/2251799813685248000000000000000000), (-12168376409080983623788248611/28147497671065600000000000000000), (1543654539276541915726179394413/2251799813685248000000000000000000), (-28356922711865653356490825143/2251799813685248000000000000000000), (-25354796132160094617389769813/2251799813685248000000000000000000), (95016550663374487985252463/225179981368524800000000000000000), (192031045563890825887976353/2251799813685248000000000000000000), (-635008439151078111679901/112589990684262400000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial142.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial142.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial142.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial142 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 1544084494686958508096375437466550), (Int.negOfNat 181647918034755869280742185081896), (Int.negOfNat 12435534821568765189350043198135), (Int.ofNat 6987453204270303241574123282198), (Int.ofNat 164594807296865994256017711899), (Int.negOfNat 194506165044400191930247325420), (Int.ofNat 220073152425226022554676648), (Int.ofNat 2068699036469965010325267362), (Int.negOfNat 39130279101704726469661644), (Int.negOfNat 9206934359259665951841686), (Int.ofNat 522385868304218596019695), (Int.negOfNat 6151182302625695814277), (Int.negOfNat 3613513010189102937877), (Int.ofNat 303403231846967607775), (Int.ofNat 16064516661465254556), (Int.negOfNat 1914649879714234715), (Int.negOfNat 104018155418701203), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(30881689893739170161927508749331/45035996273704960000000000000000), (-22705989754344483660092773135237/281474976710656000000000000000000), (-2487106964313753037870008639627/450359962737049600000000000000000), (3493726602135151620787061641099/1125899906842624000000000000000000), (164594807296865994256017711899/2251799813685248000000000000000000), (-9725308252220009596512366271/112589990684262400000000000000000), (27509144053153252819334581/281474976710656000000000000000000), (1034349518234982505162633681/1125899906842624000000000000000000), (-9782569775426181617415411/562949953421312000000000000000000), (-4603467179629832975920843/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial142.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial142.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial142.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial142 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 1183620121668528524141092415436229), (Int.negOfNat 156923795156547246053208150311566), (Int.ofNat 19215056124454786717229162299863), (Int.ofNat 1605484505534075842463621506420), (Int.negOfNat 1262549768254267860367093818733), (Int.negOfNat 50411388114587617362066497538), (Int.ofNat 20136745642804957928549711708), (Int.ofNat 531370202640256419428886668), (Int.negOfNat 133613456588607420366725680), (Int.negOfNat 2607353722408491993933454), (Int.ofNat 194519064591212561543423), (Int.ofNat 5775238091024856768057), (Int.ofNat 3160632542345946211710), (Int.negOfNat 746719145591168370), (Int.negOfNat 27590751891276705052), (Int.ofNat 61520957302128306), (Int.ofNat 96550300166425185), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(1183620121668528524141092415436229/2251799813685248000000000000000000), (-78461897578273623026604075155783/1125899906842624000000000000000000), (19215056124454786717229162299863/2251799813685248000000000000000000), (80274225276703792123181075321/112589990684262400000000000000000), (-1262549768254267860367093818733/2251799813685248000000000000000000), (-25205694057293808681033248769/1125899906842624000000000000000000), (5034186410701239482137427927/562949953421312000000000000000000), (132842550660064104857221667/562949953421312000000000000000000), (-1670168207357592754584071/28147497671065600000000000000000), (-1303676861204245996966727/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial142.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial142.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial142.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial142 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 938984121789901416588356349169310), (Int.negOfNat 101269643234050027053508704229342), (Int.negOfNat 545085741126985999486161183054), (Int.negOfNat 7241807594147747573185234271572), (Int.negOfNat 566604208204942659925136709754), (Int.ofNat 172781565731885678939215386107), (Int.ofNat 11764445812299127612374839040), (Int.negOfNat 1696135101705883525239694103), (Int.negOfNat 117845996921092628324925664), (Int.ofNat 6503522541054390303073117), (Int.ofNat 769546859816331055718878), (Int.ofNat 16474007705394145627945), (Int.negOfNat 3776261186549377933598), (Int.negOfNat 319843289526744988802), (Int.ofNat 14884939833473626817), (Int.ofNat 1953875053558560631), (Int.ofNat 3743545676617683), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(93898412178990141658835634916931/225179981368524800000000000000000), (-50634821617025013526754352114671/1125899906842624000000000000000000), (-272542870563492999743080591527/1125899906842624000000000000000000), (-1810451898536936893296308567893/562949953421312000000000000000000), (-283302104102471329962568354877/1125899906842624000000000000000000), (172781565731885678939215386107/2251799813685248000000000000000000), (9190973290858693447167843/1759218604441600000000000000000), (-1696135101705883525239694103/2251799813685248000000000000000000), (-3682687403784144635153927/70368744177664000000000000000000), (6503522541054390303073117/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial142.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial142.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial142.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial142 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 673303158812131202580105059920360), (Int.negOfNat 193263253901364228845023462864335), (Int.negOfNat 42260424801121368148840095077181), (Int.negOfNat 4095108645035957913724082690582), (Int.ofNat 1296858069232105267138951059583), (Int.ofNat 138020661052366089888428816370), (Int.negOfNat 18258446652843455527954424939), (Int.negOfNat 1941014057357057658315437563), (Int.ofNat 120574817660721490255992845), (Int.ofNat 16659987982976992059723869), (Int.negOfNat 217779523224556347466072), (Int.negOfNat 101054399623063729782011), (Int.negOfNat 2376319319699719136339), (Int.ofNat 465816824253858938577), (Int.ofNat 22134247230090800476), (Int.negOfNat 1732660531312706617), (Int.negOfNat 92777303966696334), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(16832578970303280064502626498009/56294995342131200000000000000000), (-38652650780272845769004692572867/450359962737049600000000000000000), (-42260424801121368148840095077181/2251799813685248000000000000000000), (-2047554322517978956862041345291/1125899906842624000000000000000000), (1296858069232105267138951059583/2251799813685248000000000000000000), (13802066105236608988842881637/225179981368524800000000000000000), (-18258446652843455527954424939/2251799813685248000000000000000000), (-1941014057357057658315437563/2251799813685248000000000000000000), (24114963532144298051198569/450359962737049600000000000000000), (16659987982976992059723869/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial142.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial142.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial142.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial142 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.ofNat 108762444009802593745680974852502), (Int.negOfNat 363120773382485876099240140484400), (Int.negOfNat 30063813485395024667234702730878), (Int.ofNat 8090165372705561570735189996589), (Int.ofNat 1232982188510153380668215144338), (Int.negOfNat 161336531229692961518246788442), (Int.negOfNat 22984588518444413755020312785), (Int.ofNat 1642033587234000001465157407), (Int.ofNat 250849239043653857597005922), (Int.negOfNat 8009085482668237589187570), (Int.negOfNat 1845916416515489161489069), (Int.ofNat 5704484205277411315936), (Int.ofNat 9949156649459706001175), (Int.ofNat 167865135589497751299), (Int.negOfNat 40859511740847238719), (Int.negOfNat 1264487085896851035), (Int.ofNat 95273398665556220), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(54381222004901296872840487426251/1125899906842624000000000000000000), (-907801933456214690248100351211/5629499534213120000000000000000), (-15031906742697512333617351365439/1125899906842624000000000000000000), (8090165372705561570735189996589/2251799813685248000000000000000000), (616491094255076690334107572169/1125899906842624000000000000000000), (-80668265614846480759123394221/1125899906842624000000000000000000), (-4596917703688882751004062557/450359962737049600000000000000000), (1642033587234000001465157407/2251799813685248000000000000000000), (125424619521826928798502961/1125899906842624000000000000000000), (-800908548266823758918757/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial142.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial142.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial142.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial142 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 659650641423136079410808872285404), (Int.negOfNat 363193666901136377778249498594700), (Int.ofNat 31141168898509538279789694780345), (Int.ofNat 9122056558754702554280494239027), (Int.negOfNat 1074320889053515031915028702987), (Int.negOfNat 216684054128591582425011705631), (Int.ofNat 17190683970952341284894005705), (Int.ofNat 3011760785289533820758871167), (Int.negOfNat 140742708131748819339378022), (Int.negOfNat 27042447940720198782723570), (Int.ofNat 592960422014070064813229), (Int.ofNat 171894400369604167615316), (Int.negOfNat 641279844459913237615), (Int.negOfNat 816536817207065791761), (Int.negOfNat 7057491893852722961), (Int.ofNat 3066600894087287385), (Int.ofNat 23412233338821420), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-164912660355784019852702218071351/562949953421312000000000000000000), (-3631936669011363777782494985947/22517998136852480000000000000000), (6228233779701907655957938956069/450359962737049600000000000000000), (9122056558754702554280494239027/2251799813685248000000000000000000), (-1074320889053515031915028702987/2251799813685248000000000000000000), (-216684054128591582425011705631/2251799813685248000000000000000000), (3438136794190468256978801141/450359962737049600000000000000000), (3011760785289533820758871167/2251799813685248000000000000000000), (-70371354065874409669689011/1125899906842624000000000000000000), (-2704244794072019878272357/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial142.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial142.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial142.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial142 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 1211183087929391618048937574498693), (Int.negOfNat 176428938675940775919969913706071), (Int.ofNat 48539425145626381929793129504113), (Int.negOfNat 4084310567793507014849428256541), (Int.negOfNat 1618242942471157817940438850706), (Int.ofNat 134554166695656678878552371012), (Int.ofNat 29738454718882262871629140219), (Int.negOfNat 1761352617396566926285052723), (Int.negOfNat 331410671002669184260559805), (Int.ofNat 12689392683806717798538369), (Int.ofNat 2515040083042151667927792), (Int.negOfNat 53659528089786324536651), (Int.negOfNat 13902983473459715592681), (Int.ofNat 120008157871598887397), (Int.ofNat 58266358801753321384), (Int.ofNat 141815979342378383), (Int.negOfNat 159607807693792666), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-1211183087929391618048937574498693/2251799813685248000000000000000000), (-176428938675940775919969913706071/2251799813685248000000000000000000), (48539425145626381929793129504113/2251799813685248000000000000000000), (-4084310567793507014849428256541/2251799813685248000000000000000000), (-809121471235578908970219425353/1125899906842624000000000000000000), (33638541673914169719638092753/562949953421312000000000000000000), (29738454718882262871629140219/2251799813685248000000000000000000), (-1761352617396566926285052723/2251799813685248000000000000000000), (-66282134200533836852111961/450359962737049600000000000000000), (12689392683806717798538369/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial142.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial142.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial142.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial142 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 1422542028697973850226574002910277), (Int.negOfNat 67679892691827903337549400147575), (Int.ofNat 1404812513711246558703431344859), (Int.negOfNat 8367085817892436258591854280528), (Int.ofNat 728286927485067762993371382363), (Int.ofNat 237954620150374847168554890120), (Int.negOfNat 16606558628151303573628492220), (Int.negOfNat 3420228156803073249481663923), (Int.ofNat 184284185341081058947453784), (Int.ofNat 31548654589923290921397317), (Int.negOfNat 1222472801848009453753998), (Int.negOfNat 205548860962944361747115), (Int.ofNat 5279154226985803605718), (Int.ofNat 994575713851195820238), (Int.negOfNat 15470795633946180577), (Int.negOfNat 3677805763572973349), (Int.ofNat 78120041803171717), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-1422542028697973850226574002910277/2251799813685248000000000000000000), (-2707195707673116133501976005903/90071992547409920000000000000000), (1404812513711246558703431344859/2251799813685248000000000000000000), (-522942863618277266161990892533/140737488355328000000000000000000), (728286927485067762993371382363/2251799813685248000000000000000000), (5948865503759371179213872253/56294995342131200000000000000000), (-830327931407565178681424611/112589990684262400000000000000000), (-3420228156803073249481663923/2251799813685248000000000000000000), (23035523167635132368431723/281474976710656000000000000000000), (31548654589923290921397317/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial142.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial142.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial142.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial142 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 1601391034556220622464307288626981), (Int.negOfNat 124591841845934421219789418918217), (Int.negOfNat 18110164771749681658002966407341), (Int.ofNat 2878268287978202162340438046122), (Int.ofNat 1463273114678387897505884928933), (Int.negOfNat 117561310117314873091195925266), (Int.negOfNat 29285733007110186714521559305), (Int.ofNat 2043006636796261835809045228), (Int.ofNat 337788117854360681612311180), (Int.negOfNat 19513307439108215693300434), (Int.negOfNat 2635801549810722186368823), (Int.ofNat 118165328558799272559957), (Int.ofNat 14915597644171406404490), (Int.negOfNat 492838861613633977590), (Int.negOfNat 63418248208222816328), (Int.ofNat 1443108643117060326), (Int.ofNat 155834811494063815), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-1601391034556220622464307288626981/2251799813685248000000000000000000), (-124591841845934421219789418918217/2251799813685248000000000000000000), (-18110164771749681658002966407341/2251799813685248000000000000000000), (1439134143989101081170219023061/1125899906842624000000000000000000), (1463273114678387897505884928933/2251799813685248000000000000000000), (-58780655058657436545597962633/1125899906842624000000000000000000), (-5857146601422037342904311861/450359962737049600000000000000000), (510751659199065458952261307/562949953421312000000000000000000), (16889405892718034080615559/112589990684262400000000000000000), (-9756653719554107846650217/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial142.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial142.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial142.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial142 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 1881877523217170631834720224601934), (Int.negOfNat 129491934782170904022267260774014), (Int.ofNat 19706688870641983198931059351689), (Int.ofNat 6806777523137040682893894321660), (Int.negOfNat 626580684340542675372838362302), (Int.negOfNat 201857519035393452144389081630), (Int.ofNat 17656752607384185785017243792), (Int.ofNat 3030828259610237860530251402), (Int.negOfNat 244434336827275193682835676), (Int.negOfNat 28937651542166934305881486), (Int.ofNat 1993201193056007788632865), (Int.ofNat 194519580822186733834463), (Int.negOfNat 10747813986065713780403), (Int.negOfNat 966024505788547037165), (Int.ofNat 41124041449880023384), (Int.ofNat 3680628978003581225), (Int.negOfNat 178394651545255237), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-940938761608585315917360112300967/1125899906842624000000000000000000), (-64745967391085452011133630387007/1125899906842624000000000000000000), (19706688870641983198931059351689/2251799813685248000000000000000000), (340338876156852034144694716083/112589990684262400000000000000000), (-313290342170271337686419181151/1125899906842624000000000000000000), (-20185751903539345214438908163/225179981368524800000000000000000), (1103547037961511611563577737/140737488355328000000000000000000), (1515414129805118930265125701/1125899906842624000000000000000000), (-61108584206818798420708919/562949953421312000000000000000000), (-14468825771083467152940743/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial142.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial142.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial142.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial142 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 2022622173492848250380731674078935), (Int.negOfNat 740011760700520748924391842774), (Int.ofNat 35091359124784662951040746702462), (Int.negOfNat 2314044214804798538224018161974), (Int.negOfNat 1094220972005916985134311994748), (Int.ofNat 117237246023631446687128422648), (Int.ofNat 22030593375355066946979114193), (Int.negOfNat 2461853032492081993806237370), (Int.negOfNat 264255172642839225896568833), (Int.ofNat 27332423912639461008870240), (Int.ofNat 2152694169507036534902361), (Int.negOfNat 188596627594513509941103), (Int.negOfNat 12692640694692564335870), (Int.ofNat 890629558515915876726), (Int.ofNat 56067746260245974707), (Int.negOfNat 2983306902473595395), (Int.negOfNat 152061815294334964), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-404524434698569650076146334815787/450359962737049600000000000000000), (-370005880350260374462195921387/1125899906842624000000000000000000), (17545679562392331475520373351231/1125899906842624000000000000000000), (-1157022107402399269112009080987/1125899906842624000000000000000000), (-273555243001479246283577998687/562949953421312000000000000000000), (14654655752953930835891052831/281474976710656000000000000000000), (22030593375355066946979114193/2251799813685248000000000000000000), (-246185303249208199380623737/225179981368524800000000000000000), (-264255172642839225896568833/2251799813685248000000000000000000), (170827649453996631305439/14073748835532800000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial142.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial142.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial142.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial142 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 1914962098024344689828185185473956), (Int.ofNat 89148781614578625935070549980333), (Int.ofNat 7628940374744092441807439805416), (Int.negOfNat 4534705685352612497375031943344), (Int.ofNat 544637789612376573159157055716), (Int.ofNat 122360576766660825838221865495), (Int.negOfNat 19740868495279130510744198229), (Int.negOfNat 1888557119922617003494684638), (Int.ofNat 310132608553941977004739245), (Int.ofNat 19126969391300122049699930), (Int.negOfNat 2781259803592386677814222), (Int.negOfNat 137963132308391387358018), (Int.ofNat 16198068131450309441575), (Int.ofNat 728254701522763742761), (Int.negOfNat 66538532209705544997), (Int.negOfNat 2931047330020684555), (Int.ofNat 278669261287338757), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-478740524506086172457046296368489/562949953421312000000000000000000), (89148781614578625935070549980333/2251799813685248000000000000000000), (953617546843011555225929975677/281474976710656000000000000000000), (-283419105334538281085939496459/140737488355328000000000000000000), (136159447403094143289789263929/562949953421312000000000000000000), (24472115353332165167644373099/450359962737049600000000000000000), (-19740868495279130510744198229/2251799813685248000000000000000000), (-944278559961308501747342319/1125899906842624000000000000000000), (62026521710788395400947849/450359962737049600000000000000000), (1912696939130012204969993/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial142.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial142.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial142.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial142 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 1731215699040794714511544033049403), (Int.ofNat 88175288870245026570809717956866), (Int.negOfNat 2116905662709199546132798437290), (Int.ofNat 1112709186594965154623393335926), (Int.ofNat 438500888941242871752384770667), (Int.negOfNat 120369630874806131188211082144), (Int.negOfNat 8915996000687447871391121117), (Int.ofNat 2887256346384937980976872861), (Int.ofNat 115556025330004395221882857), (Int.negOfNat 34856689472448343777828647), (Int.negOfNat 1096394772415512550946671), (Int.ofNat 254489227096926093413959), (Int.ofNat 7429445260357949789544), (Int.negOfNat 1254545595076919405193), (Int.negOfNat 36132953991364170520), (Int.ofNat 4483127963624769304), (Int.ofNat 114863949180578273), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-1731215699040794714511544033049403/2251799813685248000000000000000000), (44087644435122513285404858978433/1125899906842624000000000000000000), (-211690566270919954613279843729/225179981368524800000000000000000), (556354593297482577311696667963/1125899906842624000000000000000000), (438500888941242871752384770667/2251799813685248000000000000000000), (-3761550964837691599631596317/70368744177664000000000000000000), (-8915996000687447871391121117/2251799813685248000000000000000000), (2887256346384937980976872861/2251799813685248000000000000000000), (115556025330004395221882857/2251799813685248000000000000000000), (-34856689472448343777828647/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial142.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial142.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial142.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial142 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 1551456785438193270074091168952054), (Int.ofNat 97079639412811383843015742706225), (Int.ofNat 5295482527129966088927649310065), (Int.ofNat 10282351959569836366441551008), (Int.negOfNat 506370400251934216844245714534), (Int.negOfNat 4333260087420367220013607745), (Int.ofNat 21250866779604782084740512071), (Int.ofNat 50472848898563253486694363), (Int.negOfNat 369102495653720897347215631), (Int.negOfNat 2842578407362136071954869), (Int.ofNat 3479606196423781123517017), (Int.ofNat 41829165068628329641969), (Int.negOfNat 20866867686539812286568), (Int.negOfNat 311175797737085799279), (Int.ofNat 87551032445703596008), (Int.ofNat 1538951082962614912), (Int.negOfNat 343003670315575203), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-775728392719096635037045584476027/1125899906842624000000000000000000), (3883185576512455353720629708249/90071992547409920000000000000000), (1059096505425993217785529862013/450359962737049600000000000000000), (321323498736557386451298469/70368744177664000000000000000000), (-253185200125967108422122857267/1125899906842624000000000000000000), (-866652017484073444002721549/450359962737049600000000000000000), (21250866779604782084740512071/2251799813685248000000000000000000), (50472848898563253486694363/2251799813685248000000000000000000), (-369102495653720897347215631/2251799813685248000000000000000000), (-2842578407362136071954869/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial142.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial142.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial142.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial142 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 1342999775824503056385613220543828), (Int.ofNat 105570479765839080877240250020041), (Int.negOfNat 2642941846451497661886016105038), (Int.negOfNat 1409482248924271499909727942220), (Int.ofNat 360491876778470348417495906580), (Int.ofNat 110998647796770879856970242187), (Int.negOfNat 10215772196092620793133810033), (Int.negOfNat 3226945168605463071628922542), (Int.ofNat 100329173642344014935065869), (Int.ofNat 41341628126580998059216678), (Int.negOfNat 419984810591515262048714), (Int.negOfNat 307966028792804004714166), (Int.ofNat 178141768608902818395), (Int.ofNat 1535039447498995325303), (Int.ofNat 7241132882392104219), (Int.negOfNat 5648150734341822241), (Int.negOfNat 45498878552703359), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-335749943956125764096403305135957/562949953421312000000000000000000), (105570479765839080877240250020041/2251799813685248000000000000000000), (-1321470923225748830943008052519/1125899906842624000000000000000000), (-70474112446213574995486397111/112589990684262400000000000000000), (18024593838923517420874795329/112589990684262400000000000000000), (110998647796770879856970242187/2251799813685248000000000000000000), (-10215772196092620793133810033/2251799813685248000000000000000000), (-1613472584302731535814461271/1125899906842624000000000000000000), (100329173642344014935065869/2251799813685248000000000000000000), (20670814063290499029608339/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial142.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial142.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial142.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial142 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 1145407669676254656297164789136139), (Int.ofNat 95285912047291281278699559065768), (Int.ofNat 2168605638822529561482956320577), (Int.ofNat 2855833269696767120224986592779), (Int.ofNat 214968513321286121222701410725), (Int.negOfNat 166340640371337304416287882771), (Int.negOfNat 21999808948241715066788916519), (Int.ofNat 2469345922056314968042818354), (Int.ofNat 423817756576364434158254791), (Int.negOfNat 18232709404081877979829476), (Int.negOfNat 4040870324689638700894859), (Int.ofNat 80585005598577266632731), (Int.ofNat 24197965597958940890554), (Int.negOfNat 223153323474546431790), (Int.negOfNat 101624415856536786509), (Int.ofNat 320543751598001919), (Int.ofNat 372655544029874192), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-1145407669676254656297164789136139/2251799813685248000000000000000000), (11910739005911410159837444883221/281474976710656000000000000000000), (2168605638822529561482956320577/2251799813685248000000000000000000), (2855833269696767120224986592779/2251799813685248000000000000000000), (8598740532851444848908056429/90071992547409920000000000000000), (-166340640371337304416287882771/2251799813685248000000000000000000), (-21999808948241715066788916519/2251799813685248000000000000000000), (1234672961028157484021409177/1125899906842624000000000000000000), (423817756576364434158254791/2251799813685248000000000000000000), (-4558177351020469494957369/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial142.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial142.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial142.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial142 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 926194787603443763573512239287978), (Int.ofNat 129057149760425560624886355754586), (Int.ofNat 8167790961541680796111146177037), (Int.negOfNat 3609794862292984464654184018690), (Int.negOfNat 1723869626036955885255685009123), (Int.negOfNat 97723739432342615014026633545), (Int.ofNat 36707497241771984876999430875), (Int.ofNat 3717650354568199262431769874), (Int.negOfNat 361140853702269567643519848), (Int.negOfNat 47241147101183213419130214), (Int.ofNat 2169563800116836251069485), (Int.ofNat 344765906326893713666109), (Int.negOfNat 8936825426696227118767), (Int.negOfNat 1694828927004652329931), (Int.ofNat 26757937871745315080), (Int.ofNat 6099120252468223251), (Int.negOfNat 54775731189380161), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-463097393801721881786756119643989/1125899906842624000000000000000000), (64528574880212780312443177877293/1125899906842624000000000000000000), (8167790961541680796111146177037/2251799813685248000000000000000000), (-360979486229298446465418401869/225179981368524800000000000000000), (-1723869626036955885255685009123/2251799813685248000000000000000000), (-19544747886468523002805326709/450359962737049600000000000000000), (293659977934175879015995447/18014398509481984000000000000000), (1858825177284099631215884937/1125899906842624000000000000000000), (-45142606712783695955439981/281474976710656000000000000000000), (-23620573550591606709565107/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial142.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial142.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial142.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial142 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 692285379414954621512962931646941), (Int.ofNat 63678429305795387350559110992011), (Int.negOfNat 52204697362525151069915374039565), (Int.negOfNat 14209335262468658117467590087852), (Int.negOfNat 10656527179676673749136200613), (Int.ofNat 424289843237263936779722437374), (Int.ofNat 28082065612076357827376281468), (Int.negOfNat 5351684093403591575262021888), (Int.negOfNat 496680298841183232468294268), (Int.ofNat 40361540152972765608361266), (Int.ofNat 4461823534635303872493209), (Int.negOfNat 208124645777446064592889), (Int.negOfNat 25827253133864125462162), (Int.ofNat 788868902774020224822), (Int.ofNat 106373498079095374928), (Int.negOfNat 2256531963300362210), (Int.negOfNat 368882547830145341), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-692285379414954621512962931646941/2251799813685248000000000000000000), (63678429305795387350559110992011/2251799813685248000000000000000000), (-10440939472505030213983074807913/450359962737049600000000000000000), (-3552333815617164529366897521963/562949953421312000000000000000000), (-10656527179676673749136200613/2251799813685248000000000000000000), (212144921618631968389861218687/1125899906842624000000000000000000), (7020516403019089456844070367/562949953421312000000000000000000), (-20905015989857779590867273/8796093022208000000000000000000), (-124170074710295808117073567/562949953421312000000000000000000), (20180770076486382804180633/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial142.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial142.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial142.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial142 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 873005425228309672706134183600767), (Int.negOfNat 279451691250707741253116622999962), (Int.negOfNat 101290022221418909100813143066954), (Int.ofNat 3557264081119171001804302994922), (Int.ofNat 4073442104274542717905085121071), (Int.ofNat 198156461256691736618927210412), (Int.negOfNat 64712585429770088896345121156), (Int.negOfNat 4828805251963653360146605557), (Int.ofNat 603736234967146908587035452), (Int.ofNat 53027193266485750104038607), (Int.negOfNat 3795141406601352906519206), (Int.negOfNat 361284534699549798297853), (Int.ofNat 17309650876248228408514), (Int.ofNat 1712160865216873439430), (Int.negOfNat 60120861828186374473), (Int.negOfNat 6051922631379782187), (Int.ofNat 155050340931463681), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-873005425228309672706134183600767/2251799813685248000000000000000000), (-139725845625353870626558311499981/1125899906842624000000000000000000), (-50645011110709454550406571533477/1125899906842624000000000000000000), (1778632040559585500902151497461/1125899906842624000000000000000000), (4073442104274542717905085121071/2251799813685248000000000000000000), (49539115314172934154731802603/562949953421312000000000000000000), (-16178146357442522224086280289/562949953421312000000000000000000), (-4828805251963653360146605557/2251799813685248000000000000000000), (150934058741786727146758863/562949953421312000000000000000000), (53027193266485750104038607/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial142.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial142.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial142.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial142 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 1741677232057097005100953723666422), (Int.negOfNat 509592659856128032444040792355192), (Int.ofNat 16166479041865707492762150891939), (Int.ofNat 32308726327786074450911335118942), (Int.ofNat 1646652328371991029459978511192), (Int.negOfNat 645683414176582143894531191041), (Int.negOfNat 45816245388072281991712373661), (Int.ofNat 7507640615052798154658341627), (Int.ofNat 590024347436623811342886795), (Int.negOfNat 57754474726093027952887329), (Int.negOfNat 4677897471106016208927672), (Int.ofNat 315715692242103296662115), (Int.ofNat 25438568414518845650007), (Int.negOfNat 1289969015406462892257), (Int.negOfNat 101150890317290689520), (Int.ofNat 4014094332243707501), (Int.ofNat 365109551630416490), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-870838616028548502550476861833211/1125899906842624000000000000000000), (-63699082482016004055505099044399/281474976710656000000000000000000), (16166479041865707492762150891939/2251799813685248000000000000000000), (16154363163893037225455667559471/1125899906842624000000000000000000), (205831541046498878682497313899/281474976710656000000000000000000), (-645683414176582143894531191041/2251799813685248000000000000000000), (-45816245388072281991712373661/2251799813685248000000000000000000), (7507640615052798154658341627/2251799813685248000000000000000000), (118004869487324762268577359/450359962737049600000000000000000), (-57754474726093027952887329/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial142.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial142.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial142.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial142 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 2433896094199927171327251402811060), (Int.negOfNat 61165852444929307489693238796837), (Int.ofNat 192680727099758928061149534046149), (Int.ofNat 17219027909998294108455948363767), (Int.negOfNat 5075929858282268680991865684464), (Int.negOfNat 443260922413594917268588700248), (Int.ofNat 76668193682990935519397372614), (Int.ofNat 6274492927408386065449251165), (Int.negOfNat 741698818566734372450007274), (Int.negOfNat 56639677769806054276688402), (Int.ofNat 4930101672118691947542105), (Int.ofNat 350849935542528203347876), (Int.negOfNat 23827243262063585894019), (Int.negOfNat 1574831408426328873371), (Int.ofNat 87401774177366033067), (Int.ofNat 5276111868785305611), (Int.negOfNat 254067285273637584), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-121694804709996358566362570140553/112589990684262400000000000000000), (-61165852444929307489693238796837/2251799813685248000000000000000000), (192680727099758928061149534046149/2251799813685248000000000000000000), (17219027909998294108455948363767/2251799813685248000000000000000000), (-317245616142641792561991605279/140737488355328000000000000000000), (-55407615301699364658573587531/281474976710656000000000000000000), (38334096841495467759698686307/1125899906842624000000000000000000), (1254898585481677213089850233/450359962737049600000000000000000), (-370849409283367186225003637/1125899906842624000000000000000000), (-28319838884903027138344201/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial142.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial142.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial142.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial142.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial142 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial142 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial142 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 2921398908965192701028881274949209), (Int.negOfNat 4372958351103581385672544182465), (Int.ofNat 216450726421247531523264839763552), (Int.negOfNat 23261089817409576608687098229839), (Int.negOfNat 5537372246707244421425330927795), (Int.ofNat 650335522855385045998868226073), (Int.ofNat 82376986553997154851193959417), (Int.negOfNat 8974418315065719109113379145), (Int.negOfNat 787576470836028796988562994), (Int.ofNat 76238845843447306802537482), (Int.ofNat 5177876275007610102340525), (Int.negOfNat 442646582414744431177576), (Int.negOfNat 24767551203197476405499), (Int.ofNat 1876268658053599424991), (Int.ofNat 89994458025349042467), (Int.negOfNat 6053917023180208431), (Int.negOfNat 254067285273637584), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-2921398908965192701028881274949209/2251799813685248000000000000000000), (-874591670220716277134508836493/450359962737049600000000000000000), (6764085200663985360102026242611/70368744177664000000000000000000), (-23261089817409576608687098229839/2251799813685248000000000000000000), (-1107474449341448884285066185559/450359962737049600000000000000000), (650335522855385045998868226073/2251799813685248000000000000000000), (82376986553997154851193959417/2251799813685248000000000000000000), (-1794883663013143821822675829/450359962737049600000000000000000), (-393788235418014398494281497/1125899906842624000000000000000000), (38119422921723653401268741/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial142.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial142.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial142.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 2314252730638801165778174840420165), (Int.ofNat 468313842170795077823328239632136), (Int.ofNat 8739572627950755897720858746235), (Int.negOfNat 34334830969372800655992613122419), (Int.ofNat 2869589784567943511832661651725), (Int.ofNat 712716822866590288757239560428), (Int.negOfNat 70387887170107256036265610421), (Int.negOfNat 8356916748378387154262710107), (Int.ofNat 825232939989676662007942075), (Int.ofNat 63842724249540217341130009), (Int.negOfNat 6035802280227130893956972), (Int.negOfNat 344076975840949403608575), (Int.ofNat 30728494401079166738467), (Int.ofNat 1383046365549052929717), (Int.negOfNat 116102033840659377060), (Int.negOfNat 4273362717042008441), (Int.ofNat 365109551630416490), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-462850546127760233155634968084033/450359962737049600000000000000000), (58539230271349384727916029954017/281474976710656000000000000000000), (1747914525590151179544171749247/450359962737049600000000000000000), (-34334830969372800655992613122419/2251799813685248000000000000000000), (114783591382717740473306466069/90071992547409920000000000000000), (178179205716647572189309890107/562949953421312000000000000000000), (-70387887170107256036265610421/2251799813685248000000000000000000), (-8356916748378387154262710107/2251799813685248000000000000000000), (33009317599587066480317683/90071992547409920000000000000000), (63842724249540217341130009/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial142.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial142.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial142.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 1553962341827229600039571228408904), (Int.ofNat 223798174768434539067845372377899), (Int.negOfNat 92194819028234969588662143110902), (Int.ofNat 2907190468326930975689002170719), (Int.ofNat 4523839739940179400991646393936), (Int.negOfNat 390912105799626088490689710074), (Int.negOfNat 75399806146290703827172811476), (Int.ofNat 7303788950828847799824539117), (Int.ofNat 709456684107191204077138812), (Int.negOfNat 70941538461399282443721167), (Int.negOfNat 4411269985536324876190846), (Int.ofNat 445137860235582094258433), (Int.ofNat 19716956128147378942134), (Int.negOfNat 1987871488146379439790), (Int.negOfNat 66948262627874965893), (Int.ofNat 6656882195909151047), (Int.ofNat 155050340931463681), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-194245292728403700004946403551113/281474976710656000000000000000000), (223798174768434539067845372377899/2251799813685248000000000000000000), (-46097409514117484794331071555451/1125899906842624000000000000000000), (2907190468326930975689002170719/2251799813685248000000000000000000), (282739983746261212561977899621/140737488355328000000000000000000), (-195456052899813044245344855037/1125899906842624000000000000000000), (-18849951536572675956793202869/562949953421312000000000000000000), (7303788950828847799824539117/2251799813685248000000000000000000), (177364171026797801019284703/562949953421312000000000000000000), (-70941538461399282443721167/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial142.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial142.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial142.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 1395764441855444038256467490134663), (Int.negOfNat 7263742401881183388279145005092), (Int.negOfNat 9733137088876978313540874773530), (Int.ofNat 16330189164128290995278654451908), (Int.negOfNat 1394416460956052623768816805801), (Int.negOfNat 528486653335916321465432971698), (Int.ofNat 51094808294402892645790968371), (Int.ofNat 6818734309344407417769934028), (Int.negOfNat 706633391389357367529866788), (Int.negOfNat 51271916861506528036703686), (Int.ofNat 5655654802474206147415109), (Int.ofNat 259669995902906456025989), (Int.negOfNat 30452973503912914594642), (Int.negOfNat 958895401047741875722), (Int.ofNat 119423340113943188908), (Int.ofNat 2602223143031430130), (Int.negOfNat 368882547830145341), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-1395764441855444038256467490134663/2251799813685248000000000000000000), (-1815935600470295847069786251273/562949953421312000000000000000000), (-973313708887697831354087477353/225179981368524800000000000000000), (4082547291032072748819663612977/562949953421312000000000000000000), (-1394416460956052623768816805801/2251799813685248000000000000000000), (-264243326667958160732716485849/1125899906842624000000000000000000), (51094808294402892645790968371/2251799813685248000000000000000000), (1704683577336101854442483507/562949953421312000000000000000000), (-176658347847339341882466697/562949953421312000000000000000000), (-25635958430753264018351843/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial142.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial142.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial142.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 1353863289005132699779932724085281), (Int.ofNat 74920089845726748281201963281678), (Int.ofNat 27915766255498868648421782407275), (Int.negOfNat 5418652292559327001723184161422), (Int.negOfNat 2619608946682732436627386892888), (Int.ofNat 287498267248339546658024928709), (Int.ofNat 53885656190008735809364418012), (Int.negOfNat 5892396578126409430085784614), (Int.negOfNat 525448379728146551335545648), (Int.ofNat 62382505827851231652027254), (Int.ofNat 3119683878045914487412465), (Int.negOfNat 414652986812107491180669), (Int.negOfNat 12641931334659355261967), (Int.ofNat 1923606477836896867691), (Int.ofNat 37215096058610119660), (Int.negOfNat 6704079816997592111), (Int.negOfNat 54775731189380161), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-1353863289005132699779932724085281/2251799813685248000000000000000000), (37460044922863374140600981640839/1125899906842624000000000000000000), (1116630650219954745936871296291/90071992547409920000000000000000), (-2709326146279663500861592080711/1125899906842624000000000000000000), (-327451118335341554578423361611/281474976710656000000000000000000), (287498267248339546658024928709/2251799813685248000000000000000000), (13471414047502183952341104503/562949953421312000000000000000000), (-2946198289063204715042892307/1125899906842624000000000000000000), (-32840523733009159458471603/140737488355328000000000000000000), (31191252913925615826013627/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial142.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial142.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial142.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 1165828871224373278588142886360591), (Int.ofNat 68054721389086261449837550128838), (Int.negOfNat 36124455691994699375789779348782), (Int.negOfNat 10130307492321720560953617120431), (Int.ofNat 1525201239706848800281271996655), (Int.ofNat 341793376544244729865285267195), (Int.negOfNat 41498864461396934837343924519), (Int.negOfNat 4614809791073363860800250234), (Int.ofNat 592374166015600699083925551), (Int.ofNat 33558012183248029598108916), (Int.negOfNat 4978615874503384979314839), (Int.negOfNat 152046742667153464380271), (Int.ofNat 27800079104325199090814), (Int.ofNat 457640273221122582690), (Int.negOfNat 111649460068737756189), (Int.negOfNat 925503316127370779), (Int.ofNat 372655544029874192), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-1165828871224373278588142886360591/2251799813685248000000000000000000), (34027360694543130724918775064419/1125899906842624000000000000000000), (-18062227845997349687894889674391/1125899906842624000000000000000000), (-10130307492321720560953617120431/2251799813685248000000000000000000), (305040247941369760056254399331/450359962737049600000000000000000), (68358675308848945973057053439/450359962737049600000000000000000), (-41498864461396934837343924519/2251799813685248000000000000000000), (-2307404895536681930400125117/1125899906842624000000000000000000), (592374166015600699083925551/2251799813685248000000000000000000), (8389503045812007399527229/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial142.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial142.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial142.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 1223002190470290956767810328534628), (Int.negOfNat 131234697879708216900465798394327), (Int.negOfNat 44862435658836444247643463984730), (Int.ofNat 7681156146113622099409938448810), (Int.ofNat 1890062221865862699388546419000), (Int.negOfNat 252588895664969375509527998496), (Int.negOfNat 34526223783236897354738590473), (Int.ofNat 4819487867228684073374044322), (Int.ofNat 317476174640238581601098849), (Int.negOfNat 52262471753714879629044138), (Int.negOfNat 1645573099748328611036714), (Int.ofNat 357964559509297302025666), (Int.ofNat 4914920783192873241275), (Int.negOfNat 1697740709716426547403), (Int.negOfNat 6067977537254010701), (Int.ofNat 5993841914072890161), (Int.negOfNat 45498878552703359), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-305750547617572739191952582133657/562949953421312000000000000000000), (-131234697879708216900465798394327/2251799813685248000000000000000000), (-4486243565883644424764346398473/225179981368524800000000000000000), (768115614611362209940993844881/225179981368524800000000000000000), (1890062221865862699388546419/2251799813685248000000000000000), (-7893402989530292984672749953/70368744177664000000000000000000), (-34526223783236897354738590473/2251799813685248000000000000000000), (2409743933614342036687022161/1125899906842624000000000000000000), (317476174640238581601098849/2251799813685248000000000000000000), (-26131235876857439814522069/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial142.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial142.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial142.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 1582853142809118451951546897658098), (Int.negOfNat 182505270959596749030032893680595), (Int.ofNat 21650563804614984373562652499933), (Int.ofNat 10150676775471933204521262584207), (Int.negOfNat 1220077482102377549219999816462), (Int.negOfNat 227933760177245060676241001374), (Int.ofNat 33074250788285626167968633151), (Int.ofNat 2628386166561710242439754677), (Int.negOfNat 474472136618690768355363291), (Int.negOfNat 15804555544208857393555531), (Int.ofNat 4069400671239298491455017), (Int.ofNat 44195218949523590928471), (Int.negOfNat 23132445683238759948048), (Int.ofNat 30312667752582781359), (Int.ofNat 93859896475795585548), (Int.negOfNat 847568723500479072), (Int.negOfNat 343003670315575203), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-791426571404559225975773448829049/1125899906842624000000000000000000), (-36501054191919349806006578736119/450359962737049600000000000000000), (21650563804614984373562652499933/2251799813685248000000000000000000), (10150676775471933204521262584207/2251799813685248000000000000000000), (-610038741051188774609999908231/1125899906842624000000000000000000), (-113966880088622530338120500687/1125899906842624000000000000000000), (33074250788285626167968633151/2251799813685248000000000000000000), (2628386166561710242439754677/2251799813685248000000000000000000), (-474472136618690768355363291/2251799813685248000000000000000000), (-15804555544208857393555531/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial142.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial142.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial142.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 1804543342094883674154338321270423), (Int.negOfNat 24345797997400920762023804581059), (Int.ofNat 43865677589536354749064659685740), (Int.negOfNat 2836893122034704643538416098755), (Int.negOfNat 1320413296071797489231670878961), (Int.ofNat 177194974595195428396446314439), (Int.ofNat 19143393593744069746415772983), (Int.negOfNat 3643570761740784559196129221), (Int.negOfNat 133544860697402276030951723), (Int.ofNat 40325717055718868478499867), (Int.ofNat 302124915409893799560129), (Int.negOfNat 279928987609949950202719), (Int.ofNat 2041332738149427603144), (Int.ofNat 1338008107887992973713), (Int.negOfNat 21095387673062716000), (Int.negOfNat 4742396348423070244), (Int.ofNat 114863949180578273), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-1804543342094883674154338321270423/2251799813685248000000000000000000), (-24345797997400920762023804581059/2251799813685248000000000000000000), (2193283879476817737453232984287/112589990684262400000000000000000), (-567378624406940928707683219751/450359962737049600000000000000000), (-1320413296071797489231670878961/2251799813685248000000000000000000), (177194974595195428396446314439/2251799813685248000000000000000000), (19143393593744069746415772983/2251799813685248000000000000000000), (-3643570761740784559196129221/2251799813685248000000000000000000), (-133544860697402276030951723/2251799813685248000000000000000000), (40325717055718868478499867/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial142.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial142.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial142.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 1715178731931080148266490492722772), (Int.ofNat 90994451435543555254864569764573), (Int.ofNat 11418378863078560383768471466259), (Int.negOfNat 5318964159247000180199806129358), (Int.ofNat 585914376456222760911117549790), (Int.ofNat 117096607194263551393456856772), (Int.negOfNat 22460593877648043741301614269), (Int.negOfNat 978874428017220766232189602), (Int.ofNat 341015285671861155265292185), (Int.ofNat 1043241791692998566740970), (Int.negOfNat 2967138446676806512063942), (Int.ofNat 44722312164873912656978), (Int.ofNat 16930185047976535410615), (Int.negOfNat 423560787230796372521), (Int.negOfNat 68612679288091952517), (Int.ofNat 2153242175625781735), (Int.ofNat 278669261287338757), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-428794682982770037066622623180693/562949953421312000000000000000000), (90994451435543555254864569764573/2251799813685248000000000000000000), (11418378863078560383768471466259/2251799813685248000000000000000000), (-2659482079623500090099903064679/1125899906842624000000000000000000), (58591437645622276091111754979/225179981368524800000000000000000), (29274151798565887848364214193/562949953421312000000000000000000), (-22460593877648043741301614269/2251799813685248000000000000000000), (-489437214008610383116094801/1125899906842624000000000000000000), (68203057134372231053058437/450359962737049600000000000000000), (104324179169299856674097/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial142.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial142.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial142.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 1518424127236013872512474195896885), (Int.ofNat 96543717380651822683450940909506), (Int.negOfNat 2530040889740397844179938254471), (Int.ofNat 485108712613215441533146373320), (Int.ofNat 485241446291256087095529830347), (Int.negOfNat 100868041191595193421241629777), (Int.negOfNat 5716169392650003782718616827), (Int.ofNat 2372233712059462666066036890), (Int.negOfNat 9476831248271219707075713), (Int.negOfNat 26974201236345257500280940), (Int.ofNat 707075991781661206340141), (Int.ofNat 187433038555534271431463), (Int.negOfNat 7104776807623548711210), (Int.negOfNat 887453822197382832626), (Int.ofNat 40425220377415151327), (Int.ofNat 2983306902473595395), (Int.negOfNat 152061815294334964), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-303684825447202774502494839179377/450359962737049600000000000000000), (48271858690325911341725470454753/1125899906842624000000000000000000), (-2530040889740397844179938254471/2251799813685248000000000000000000), (12127717815330386038328659333/56294995342131200000000000000000), (485241446291256087095529830347/2251799813685248000000000000000000), (-100868041191595193421241629777/2251799813685248000000000000000000), (-5716169392650003782718616827/2251799813685248000000000000000000), (237223371205946266606603689/225179981368524800000000000000000), (-9476831248271219707075713/2251799813685248000000000000000000), (-1348710061817262875014047/112589990684262400000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial142.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial142.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial142.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 1327117254010244762037059169964830), (Int.ofNat 99602059593197765741410500609456), (Int.ofNat 4050762587379651069840171681655), (Int.ofNat 601939203453518693772328708042), (Int.negOfNat 305314137239899132595219001299), (Int.negOfNat 18539720037554666851571579820), (Int.ofNat 12876082010199346499656138632), (Int.negOfNat 251085631117813697086323082), (Int.negOfNat 203479576472430204820528996), (Int.ofNat 9039524679201620037945206), (Int.ofNat 1769226028320974316439625), (Int.negOfNat 101930538793355864214243), (Int.negOfNat 9898690355900042831243), (Int.ofNat 662605026326591837465), (Int.ofNat 38790625986695314924), (Int.negOfNat 2902823823608678405), (Int.negOfNat 178394651545255237), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-132711725401024476203705916996483/225179981368524800000000000000000), (6225128724574860358838156288091/140737488355328000000000000000000), (810152517475930213968034336331/450359962737049600000000000000000), (300969601726759346886164354021/1125899906842624000000000000000000), (-305314137239899132595219001299/2251799813685248000000000000000000), (-926986001877733342578578991/112589990684262400000000000000000), (1609510251274918312457017329/281474976710656000000000000000000), (-125542815558906848543161541/1125899906842624000000000000000000), (-50869894118107551205132249/562949953421312000000000000000000), (4519762339600810018972603/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial142.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial142.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial142.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 1111626831978205097523545629930069), (Int.ofNat 113955041755012751363173547433766), (Int.ofNat 1467189580293122831904574405537), (Int.negOfNat 956664424103301139074534437660), (Int.ofNat 38592019620992452851028338933), (Int.ofNat 52445071407916052212320394618), (Int.negOfNat 3334650499808574236021365068), (Int.negOfNat 1211068965141079376254149148), (Int.ofNat 96867507102529715344042640), (Int.ofNat 13614233083020267691263854), (Int.negOfNat 1260303127654675133643983), (Int.negOfNat 90969457245909541727897), (Int.ofNat 9580586999706728088450), (Int.ofNat 404115511858651290370), (Int.negOfNat 48467104684854128788), (Int.negOfNat 1183840258318759386), (Int.ofNat 155834811494063815), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-1111626831978205097523545629930069/2251799813685248000000000000000000), (56977520877506375681586773716883/1125899906842624000000000000000000), (1467189580293122831904574405537/2251799813685248000000000000000000), (-47833221205165056953726721883/112589990684262400000000000000000), (38592019620992452851028338933/2251799813685248000000000000000000), (26222535703958026106160197309/1125899906842624000000000000000000), (-833662624952143559005341267/562949953421312000000000000000000), (-302767241285269844063537287/562949953421312000000000000000000), (1210843838781621441800533/28147497671065600000000000000000), (6807116541510133845631927/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial142.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial142.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial142.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 883543691961342568355927969182510), (Int.ofNat 112714898797357540765226933082062), (Int.negOfNat 545203498471696318267774628546), (Int.ofNat 462867481741585477206294154212), (Int.ofNat 167777499308691511154436586474), (Int.negOfNat 30258209175220311434763400507), (Int.negOfNat 5255033089283865718267617560), (Int.ofNat 873852615591551350173340303), (Int.ofNat 77717801281429918388576744), (Int.negOfNat 13376312103542993647396437), (Int.negOfNat 615799680847258362155718), (Int.ofNat 120850837748127828313975), (Int.ofNat 2934644710918846411358), (Int.negOfNat 716618098253437878398), (Int.negOfNat 8902663219055890097), (Int.ofNat 3072846199043604489), (Int.ofNat 78120041803171717), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-88354369196134256835592796918251/225179981368524800000000000000000), (56357449398678770382613466541031/1125899906842624000000000000000000), (-272601749235848159133887314273/1125899906842624000000000000000000), (115716870435396369301573538553/562949953421312000000000000000000), (83888749654345755577218293237/1125899906842624000000000000000000), (-30258209175220311434763400507/2251799813685248000000000000000000), (-131375827232096642956690439/56294995342131200000000000000000), (873852615591551350173340303/2251799813685248000000000000000000), (9714725160178739798572093/281474976710656000000000000000000), (-13376312103542993647396437/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial142.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial142.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial142.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 655087390079589945671748011290160), (Int.ofNat 118466243521588985373307802611935), (Int.ofNat 3238050235973112768608684970861), (Int.ofNat 306436314531893278584155622062), (Int.negOfNat 175379911344983818693022493783), (Int.negOfNat 13394992824925302413063609330), (Int.ofNat 6428975832875787640821778019), (Int.ofNat 234748848980695707536174323), (Int.negOfNat 119922843499882575642994925), (Int.negOfNat 1772287239243566490307149), (Int.ofNat 1311629932356107058919272), (Int.ofNat 2865180943116417916891), (Int.negOfNat 9233544367442257846901), (Int.ofNat 46355722373977549103), (Int.ofNat 45043671177039973444), (Int.negOfNat 487507159073446303), (Int.negOfNat 159607807693792666), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-8188592375994874320896850141127/28147497671065600000000000000000), (23693248704317797074661560522387/450359962737049600000000000000000), (3238050235973112768608684970861/2251799813685248000000000000000000), (153218157265946639292077811031/1125899906842624000000000000000000), (-175379911344983818693022493783/2251799813685248000000000000000000), (-1339499282492530241306360933/225179981368524800000000000000000), (6428975832875787640821778019/2251799813685248000000000000000000), (234748848980695707536174323/2251799813685248000000000000000000), (-4796913739995303025719797/90071992547409920000000000000000), (-1772287239243566490307149/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial142.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial142.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial142.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 405574723028883903467991473290822), (Int.ofNat 129631098513331739206217228141000), (Int.ofNat 1288178011635463199109712664998), (Int.negOfNat 677463407040027705749011038629), (Int.ofNat 17319130358092326167403500582), (Int.ofNat 35957786501754377861589021602), (Int.negOfNat 960912047512462751329761935), (Int.negOfNat 875602118746952851510424287), (Int.ofNat 24669186654062124537849558), (Int.ofNat 11912256543690990035856610), (Int.negOfNat 347962174658770796386131), (Int.negOfNat 101470749332751635349816), (Int.ofNat 3006460646847126236505), (Int.ofNat 585668671300676186941), (Int.negOfNat 17093489653043359721), (Int.negOfNat 2461641329557918525), (Int.ofNat 23412233338821420), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-202787361514441951733995736645411/1125899906842624000000000000000000), (129631098513331739206217228141/2251799813685248000000000000000), (644089005817731599554856332499/1125899906842624000000000000000000), (-677463407040027705749011038629/2251799813685248000000000000000000), (8659565179046163083701750291/1125899906842624000000000000000000), (17978893250877188930794510801/1125899906842624000000000000000000), (-192182409502492550265952387/450359962737049600000000000000000), (-875602118746952851510424287/2251799813685248000000000000000000), (12334593327031062268924779/1125899906842624000000000000000000), (1191225654369099003585661/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial142.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial142.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial142.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 145313474383766483932413676308196), (Int.ofNat 129558204994726005004850818579700), (Int.negOfNat 210822598499124011363352387585), (Int.ofNat 354427779007887324441976474213), (Int.ofNat 141342169098641206417859677347), (Int.negOfNat 19389736397122480652463918089), (Int.negOfNat 4832992499979609718796545145), (Int.ofNat 494125079308580967783289473), (Int.ofNat 85437344257842913719778342), (Int.negOfNat 7121105914360971157679390), (Int.negOfNat 904993819842648300289709), (Int.ofNat 64719166831575120949564), (Int.ofNat 6301416158152666527055), (Int.negOfNat 398733281495887356119), (Int.negOfNat 30823513981656601959), (Int.ofNat 1869446650426219895), (Int.ofNat 95273398665556220), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-36328368595941620983103419077049/562949953421312000000000000000000), (1295582049947260050048508185797/22517998136852480000000000000000), (-42164519699824802272670477517/450359962737049600000000000000000), (354427779007887324441976474213/2251799813685248000000000000000000), (141342169098641206417859677347/2251799813685248000000000000000000), (-19389736397122480652463918089/2251799813685248000000000000000000), (-966598499995921943759309029/450359962737049600000000000000000), (494125079308580967783289473/2251799813685248000000000000000000), (42718672128921456859889171/1125899906842624000000000000000000), (-712110591436097115767939/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial142.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial142.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial142.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 117207460963167176862709909341333), (Int.ofNat 135300558747114319465120774722031), (Int.ofNat 3040950108542159070976250301687), (Int.ofNat 317234391773224050596997692261), (Int.negOfNat 146004961893718932183085205054), (Int.negOfNat 16861487181644107901534268812), (Int.ofNat 5051032233163019702852937261), (Int.ofNat 414410288941186439566559163), (Int.negOfNat 90913009842065118361572035), (Int.negOfNat 5742882538413840751492649), (Int.ofNat 985630627461488261542448), (Int.ofNat 50260052476393823162251), (Int.negOfNat 7045758425717176882119), (Int.negOfNat 299452944008282502077), (Int.ofNat 35356934854804148416), (Int.ofNat 1386969351581638697), (Int.negOfNat 92777303966696334), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(117207460963167176862709909341333/2251799813685248000000000000000000), (135300558747114319465120774722031/2251799813685248000000000000000000), (3040950108542159070976250301687/2251799813685248000000000000000000), (317234391773224050596997692261/2251799813685248000000000000000000), (-73002480946859466091542602527/1125899906842624000000000000000000), (-4215371795411026975383567203/562949953421312000000000000000000), (5051032233163019702852937261/2251799813685248000000000000000000), (414410288941186439566559163/2251799813685248000000000000000000), (-18182601968413023672314407/450359962737049600000000000000000), (-5742882538413840751492649/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial142.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial142.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial142.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 399985785054350257161051511317037), (Int.ofNat 146304649339718704142458221562015), (Int.ofNat 1404930271063830179068726333581), (Int.negOfNat 662410742002576710672789831392), (Int.negOfNat 6094780028442921617605776563), (Int.ofNat 34914845243152803102720645480), (Int.ofNat 412920273431689757013964380), (Int.negOfNat 850240439505638374068629517), (Int.negOfNat 11279612861441487766048624), (Int.ofNat 11668819945325906970927763), (Int.ofNat 162873738815579964120598), (Int.negOfNat 101172030920210679061085), (Int.negOfNat 1431751670482420739238), (Int.ofNat 597800905124502930642), (Int.ofNat 8316807418583336337), (Int.negOfNat 2558834618087929491), (Int.ofNat 3743545676617683), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(399985785054350257161051511317037/2251799813685248000000000000000000), (29260929867943740828491644312403/450359962737049600000000000000000), (1404930271063830179068726333581/2251799813685248000000000000000000), (-20700335687580522208524682231/70368744177664000000000000000000), (-6094780028442921617605776563/2251799813685248000000000000000000), (872871131078820077568016137/56294995342131200000000000000000), (20646013671584487850698219/112589990684262400000000000000000), (-850240439505638374068629517/2251799813685248000000000000000000), (-704975803840092985378039/140737488355328000000000000000000), (11668819945325906970927763/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial142.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial142.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial142.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 693855919091895623703623757982941), (Int.ofNat 146286995065791006820866014052857), (Int.negOfNat 362298227585484273321056553179), (Int.ofNat 316119358338583585865991498878), (Int.ofNat 162131326802576778054216759187), (Int.negOfNat 14704850594830450578721191374), (Int.negOfNat 5814336864494139219150663295), (Int.ofNat 300567469014926040126009412), (Int.ofNat 107307154163223545901542860), (Int.negOfNat 3291720633679456008103126), (Int.negOfNat 1180979357564834491181417), (Int.ofNat 21420633221864874064003), (Int.ofNat 8495643186810624527750), (Int.negOfNat 87976630609391518850), (Int.negOfNat 42541895414645392592), (Int.ofNat 197747427496172634), (Int.ofNat 96550300166425185), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(693855919091895623703623757982941/2251799813685248000000000000000000), (146286995065791006820866014052857/2251799813685248000000000000000000), (-362298227585484273321056553179/2251799813685248000000000000000000), (158059679169291792932995749439/1125899906842624000000000000000000), (162131326802576778054216759187/2251799813685248000000000000000000), (-7352425297415225289360595687/1125899906842624000000000000000000), (-1162867372898827843830132659/450359962737049600000000000000000), (75141867253731510031502353/562949953421312000000000000000000), (5365357708161177295077143/112589990684262400000000000000000), (-1645860316839728004051563/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial142.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial142.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial142.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 989324225481729741643521386203734), (Int.ofNat 151758042845913902195551847323214), (Int.ofNat 3220391461672888201538542606791), (Int.ofNat 421263522315058345538555732100), (Int.negOfNat 156671739804180838288393055338), (Int.negOfNat 25891074028429358043058058770), (Int.ofNat 5000743749610065307915781808), (Int.ofNat 711043592022459153118660958), (Int.negOfNat 80085039456549715331968324), (Int.negOfNat 10691192503705648316094594), (Int.ofNat 746361033039252068212935), (Int.ofNat 98740224331456565434497), (Int.negOfNat 4462636640354773887037), (Int.negOfNat 606822711308922807475), (Int.ofNat 18397932124649963016), (Int.ofNat 2692455034109137535), (Int.negOfNat 104018155418701203), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(494662112740864870821760693101867/1125899906842624000000000000000000), (75879021422956951097775923661607/1125899906842624000000000000000000), (3220391461672888201538542606791/2251799813685248000000000000000000), (4212635223150583455385557321/22517998136852480000000000000000), (-78335869902090419144196527669/1125899906842624000000000000000000), (-2589107402842935804305805877/225179981368524800000000000000000), (312546484350629081744736363/140737488355328000000000000000000), (355521796011229576559330479/1125899906842624000000000000000000), (-20021259864137428832992081/562949953421312000000000000000000), (-5345596251852824158047297/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial142.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial142.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial142.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 1306142752138773668163037620744295), (Int.ofNat 163786834418269327172695192547054), (Int.ofNat 1412776353830145946862110543418), (Int.negOfNat 855465389467673236489094571346), (Int.negOfNat 35807879019299042316636090052), (Int.ofNat 44726127543881116234874295912), (Int.ofNat 2391966635844976112307961207), (Int.negOfNat 1039784827066364207592725110), (Int.negOfNat 62747295830677180301516767), (Int.ofNat 13058391459315765742187320), (Int.ofNat 853340772581456330687079), (Int.negOfNat 100042025702405353416097), (Int.negOfNat 6960364659382172042210), (Int.ofNat 511102647968519431194), (Int.ofNat 37640743825871395733), (Int.negOfNat 1788044459467465005), (Int.negOfNat 100323296366154036), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(261228550427754733632607524148859/450359962737049600000000000000000), (81893417209134663586347596273527/1125899906842624000000000000000000), (706388176915072973431055271709/1125899906842624000000000000000000), (-427732694733836618244547285673/1125899906842624000000000000000000), (-8951969754824760579159022513/562949953421312000000000000000000), (5590765942985139529359286989/281474976710656000000000000000000), (2391966635844976112307961207/2251799813685248000000000000000000), (-103978482706636420759272511/225179981368524800000000000000000), (-62747295830677180301516767/2251799813685248000000000000000000), (326459786482894143554683/56294995342131200000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial142.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial142.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial142.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 1633393374445324243818593752392716), (Int.ofNat 161566962698719791262482390907187), (Int.negOfNat 1171611695397190138718505818296), (Int.ofNat 413581733671008486288032284104), (Int.ofNat 252786644571217239484089373204), (Int.negOfNat 12279567886640293681983903775), (Int.negOfNat 9305557397131274079072941251), (Int.ofNat 20082464375051389041127678), (Int.ofNat 165056571364656310431901835), (Int.ofNat 3349663711288115500596510), (Int.negOfNat 1651056132536116437388938), (Int.negOfNat 53780161401000570389062), (Int.ofNat 10408545034924223448945), (Int.ofNat 414609083761563368279), (Int.negOfNat 45306565465797549523), (Int.negOfNat 2068639926117202565), (Int.ofNat 204292765160784723), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(408348343611331060954648438098179/562949953421312000000000000000000), (161566962698719791262482390907187/2251799813685248000000000000000000), (-146451461924648767339813227287/281474976710656000000000000000000), (51697716708876060786004035513/281474976710656000000000000000000), (63196661142804309871022343301/562949953421312000000000000000000), (-491182715465611747279356151/90071992547409920000000000000000), (-9305557397131274079072941251/2251799813685248000000000000000000), (10041232187525694520563839/1125899906842624000000000000000000), (33011314272931262086380367/450359962737049600000000000000000), (334966371128811550059651/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial142.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial142.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial142.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 1958250375872614176432726129517003), (Int.ofNat 167340582480708600779785478299174), (Int.ofNat 4465987783087052399554997813810), (Int.ofNat 754463508910209585084465305074), (Int.negOfNat 247392156634082467872117432787), (Int.negOfNat 55324751341802508534774084336), (Int.ofNat 6038204857783645137547563797), (Int.ofNat 1561431805195609953306766099), (Int.negOfNat 53141696376951591353163977), (Int.negOfNat 21744572125700282786913633), (Int.ofNat 29627839318714179908471), (Int.ofNat 173429801380847240893641), (Int.ofNat 2442261382975039318776), (Int.negOfNat 906707658737524149567), (Int.negOfNat 20464145621618536680), (Int.ofNat 3388270909229780896), (Int.ofNat 70671422651855047), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(1958250375872614176432726129517003/2251799813685248000000000000000000), (83670291240354300389892739149587/1125899906842624000000000000000000), (446598778308705239955499781381/225179981368524800000000000000000), (377231754455104792542232652537/1125899906842624000000000000000000), (-247392156634082467872117432787/2251799813685248000000000000000000), (-3457796958862656783423380271/140737488355328000000000000000000), (6038204857783645137547563797/2251799813685248000000000000000000), (1561431805195609953306766099/2251799813685248000000000000000000), (-53141696376951591353163977/2251799813685248000000000000000000), (-21744572125700282786913633/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial142.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial142.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial142.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 2311664492253915206131332055999414), (Int.ofNat 183672022257669293514316900661895), (Int.ofNat 937640128002171875412500934415), (Int.negOfNat 1801496273021236943859664046888), (Int.negOfNat 140648866778793010830176213986), (Int.ofNat 85955216332130393100700208385), (Int.ofNat 9936307997924004277871025369), (Int.negOfNat 1516633183611370101780144243), (Int.negOfNat 229236832189205078060649889), (Int.ofNat 10778245785000559092996669), (Int.ofNat 2436034487507721943406543), (Int.negOfNat 31505060723980715718729), (Int.negOfNat 15594842567793573914672), (Int.negOfNat 40320844435439044801), (Int.ofNat 68252081212252183432), (Int.ofNat 817194360467382648), (Int.negOfNat 273657835788659637), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(1155832246126957603065666027999707/1125899906842624000000000000000000), (36734404451533858702863380132379/450359962737049600000000000000000), (187528025600434375082500186883/450359962737049600000000000000000), (-225187034127654617982458005861/281474976710656000000000000000000), (-70324433389396505415088106993/1125899906842624000000000000000000), (17191043266426078620140041677/450359962737049600000000000000000), (9936307997924004277871025369/2251799813685248000000000000000000), (-1516633183611370101780144243/2251799813685248000000000000000000), (-229236832189205078060649889/2251799813685248000000000000000000), (10778245785000559092996669/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial142.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial142.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial142.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 2669238307549812259205530514356308), (Int.ofNat 169210435229219120463295066302919), (Int.negOfNat 5339941582169332204425313791882), (Int.ofNat 933537291445240810226225419900), (Int.ofNat 706626297765098187421600921220), (Int.ofNat 14013437809285028286007977813), (Int.negOfNat 22887173627322301254148851847), (Int.negOfNat 1829790868777431443817977338), (Int.ofNat 249527243488431145001307491), (Int.ofNat 28953741685225841558432682), (Int.negOfNat 1413731149960295889032446), (Int.negOfNat 234049356290168668638274), (Int.ofNat 4539044390175540880765), (Int.ofNat 1222653042816860714377), (Int.negOfNat 6265527652845967619), (Int.negOfNat 4693944361355083559), (Int.negOfNat 6337013623618601), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(667309576887453064801382628589077/562949953421312000000000000000000), (169210435229219120463295066302919/2251799813685248000000000000000000), (-2669970791084666102212656895941/1125899906842624000000000000000000), (9335372914452408102262254199/22517998136852480000000000000000), (35331314888254909371080046061/112589990684262400000000000000000), (14013437809285028286007977813/2251799813685248000000000000000000), (-22887173627322301254148851847/2251799813685248000000000000000000), (-914895434388715721908988669/1125899906842624000000000000000000), (249527243488431145001307491/2251799813685248000000000000000000), (14476870842612920779216341/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial142.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial142.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial142.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 3003899973088270863694291487454379), (Int.ofNat 177884674766812945916473345363472), (Int.ofNat 12177037562435915770386171761103), (Int.ofNat 3032517486078943361951502231341), (Int.negOfNat 670482586576260027623096812845), (Int.negOfNat 261654443406093565829778805829), (Int.negOfNat 8790171744954710207562612161), (Int.ofNat 3978106788052470855441556246), (Int.ofNat 288676827914183656822634729), (Int.negOfNat 30656631576260694120933404), (Int.negOfNat 3085100242501588717838941), (Int.ofNat 145982573555970020878669), (Int.ofNat 19473237738069112950886), (Int.negOfNat 461295105542624234370), (Int.negOfNat 84739960201637850411), (Int.ofNat 941895085482092201), (Int.ofNat 310855701902416328), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(3003899973088270863694291487454379/2251799813685248000000000000000000), (11117792172925809119779584085217/140737488355328000000000000000000), (12177037562435915770386171761103/2251799813685248000000000000000000), (3032517486078943361951502231341/2251799813685248000000000000000000), (-134096517315252005524619362569/450359962737049600000000000000000), (-261654443406093565829778805829/2251799813685248000000000000000000), (-8790171744954710207562612161/2251799813685248000000000000000000), (1989053394026235427720778123/1125899906842624000000000000000000), (288676827914183656822634729/2251799813685248000000000000000000), (-7664157894065173530233351/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial142.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial142.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial142.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 3413538995410458789862954522809338), (Int.ofNat 220900980974342661644798101207054), (Int.negOfNat 5742322723210089769444323441957), (Int.negOfNat 11662932387507152297992553130510), (Int.negOfNat 2533937728176775968606561986957), (Int.ofNat 15726726493959015659222904785), (Int.ofNat 51415905586383998255221540285), (Int.ofNat 2400258027144314766255246366), (Int.negOfNat 505159374646381067968066712), (Int.negOfNat 35986297456089135246067746), (Int.ofNat 3078428432473805973397715), (Int.ofNat 278579241525383270741771), (Int.negOfNat 12858551337290641308673), (Int.negOfNat 1419513904618393703389), (Int.ofNat 38827738906674066800), (Int.ofNat 5270680419472446269), (Int.negOfNat 93937596118464919), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(1706769497705229394931477261404669/1125899906842624000000000000000000), (110450490487171330822399050603527/1125899906842624000000000000000000), (-5742322723210089769444323441957/2251799813685248000000000000000000), (-1166293238750715229799255313051/225179981368524800000000000000000), (-2533937728176775968606561986957/2251799813685248000000000000000000), (3145345298791803131844580957/450359962737049600000000000000000), (10283181117276799651044308057/450359962737049600000000000000000), (1200129013572157383127623183/1125899906842624000000000000000000), (-63144921830797633496008339/281474976710656000000000000000000), (-17993148728044567623033873/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial142.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial142.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial142.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 3702482223507687815356000849471541), (Int.negOfNat 11485880361170384674920788918131), (Int.negOfNat 122352332890052052462853441971115), (Int.negOfNat 22776157810356727146816420288428), (Int.ofNat 720526570755325137793998125133), (Int.ofNat 566824519489346489134490028226), (Int.ofNat 17690934882346699524249700052), (Int.negOfNat 6895002321811776823198513512), (Int.negOfNat 380047891488881016447794052), (Int.ofNat 51954302616036621446816534), (Int.ofNat 3612214208050153016941831), (Int.negOfNat 268027352226880950459191), (Int.negOfNat 21649519156250608393758), (Int.ofNat 1006723173947035198458), (Int.ofNat 91651977378335559712), (Int.negOfNat 2827784524569695190), (Int.negOfNat 314628698102145179), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(3702482223507687815356000849471541/2251799813685248000000000000000000), (-11485880361170384674920788918131/2251799813685248000000000000000000), (-24470466578010410492570688394223/450359962737049600000000000000000), (-5694039452589181786704105072107/562949953421312000000000000000000), (720526570755325137793998125133/2251799813685248000000000000000000), (283412259744673244567245014113/1125899906842624000000000000000000), (4422733720586674881062425013/562949953421312000000000000000000), (-861875290226472102899814189/281474976710656000000000000000000), (-95011972872220254111948513/562949953421312000000000000000000), (25977151308018310723408267/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial142.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial142.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial142.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 3037740717323813470068245794745247), (Int.negOfNat 705753055003731733374761712978038), (Int.negOfNat 197167144196854292352972691930846), (Int.ofNat 4270724445347114202818654900718), (Int.ofNat 5338389062699625381558185454929), (Int.ofNat 153837531767160608013588601348), (Int.negOfNat 79314830338380246854603936764), (Int.negOfNat 3845915963930655960913709523), (Int.ofNat 735935500709470214546068788), (Int.ofNat 43230081894232774667031953), (Int.negOfNat 4630110146107326497318754), (Int.negOfNat 302319810517821548489227), (Int.ofNat 20964095944359832655286), (Int.ofNat 1470415939839452982450), (Int.negOfNat 71415584540879393527), (Int.negOfNat 5354279999974605373), (Int.ofNat 194212205860548439), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(3037740717323813470068245794745247/2251799813685248000000000000000000), (-352876527501865866687380856489019/1125899906842624000000000000000000), (-98583572098427146176486345965423/1125899906842624000000000000000000), (2135362222673557101409327450359/1125899906842624000000000000000000), (5338389062699625381558185454929/2251799813685248000000000000000000), (38459382941790152003397150337/562949953421312000000000000000000), (-19828707584595061713650984191/562949953421312000000000000000000), (-3845915963930655960913709523/2251799813685248000000000000000000), (183983875177367553636517197/562949953421312000000000000000000), (43230081894232774667031953/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial142.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial142.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial142.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 956705695217759788727527890818542), (Int.negOfNat 1276162230977321584156162484415888), (Int.negOfNat 51276702866650030185698877277259), (Int.ofNat 39757295205789638006897042300978), (Int.ofNat 1967679373226943660931967021608), (Int.negOfNat 747900394881892499899215904399), (Int.negOfNat 40212836360655751061001414019), (Int.ofNat 8767083890343846178613879533), (Int.ofNat 490875495701591517993030845), (Int.negOfNat 68082990505653809237803471), (Int.negOfNat 3908064883790819088164528), (Int.ofNat 371763412659288832684765), (Int.ofNat 21684468074340115837873), (Int.negOfNat 1500664317802834112063), (Int.negOfNat 88405157688889878760), (Int.ofNat 4585554736894667859), (Int.ofNat 318401694301874030), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(478352847608879894363763945409271/1125899906842624000000000000000000), (-79760139436082599009760155275993/140737488355328000000000000000000), (-51276702866650030185698877277259/2251799813685248000000000000000000), (19878647602894819003448521150489/1125899906842624000000000000000000), (245959921653367957616495877701/281474976710656000000000000000000), (-747900394881892499899215904399/2251799813685248000000000000000000), (-40212836360655751061001414019/2251799813685248000000000000000000), (8767083890343846178613879533/2251799813685248000000000000000000), (98175099140318303598606169/450359962737049600000000000000000), (-68082990505653809237803471/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial142.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial142.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial142.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 1476480953612728553103069058112180), (Int.negOfNat 1004510586910426685563251563486643), (Int.ofNat 171432309183419110943804727140571), (Int.ofNat 24529484717172411819846533731793), (Int.negOfNat 5228739649168063369462587317496), (Int.negOfNat 430255027670884999212596558632), (Int.ofNat 85016345292681347351849611506), (Int.ofNat 5383287455782977190157331715), (Int.negOfNat 849806680997592334613686206), (Int.negOfNat 47308735521822644064003438), (Int.ofNat 5701047611011028268489455), (Int.ofNat 295671575200500363549204), (Int.negOfNat 27404852538836245661021), (Int.negOfNat 1356184299382514418349), (Int.ofNat 99061776340861158693), (Int.ofNat 4656652335556152429), (Int.negOfNat 295744481002541576), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-73824047680636427655153452905609/112589990684262400000000000000000), (-1004510586910426685563251563486643/2251799813685248000000000000000000), (171432309183419110943804727140571/2251799813685248000000000000000000), (24529484717172411819846533731793/2251799813685248000000000000000000), (-653592456146007921182823414687/281474976710656000000000000000000), (-53781878458860624901574569829/281474976710656000000000000000000), (42508172646340673675924805753/1125899906842624000000000000000000), (1076657491156595438031466343/450359962737049600000000000000000), (-424903340498796167306843103/1125899906842624000000000000000000), (-23654367760911322032001719/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial142.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial142.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial142.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial142.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial142.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial142.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial142.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial142.reflect := by
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

end Bin142
end
end ErdosOverlap.OuterNumerics
