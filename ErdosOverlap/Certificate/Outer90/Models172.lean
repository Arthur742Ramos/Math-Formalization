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

/-! # Exact integer weighted outer models for source bin 172

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin172

def weightDenominator : ℤ := (Int.ofNat 2000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 87745885150255200)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 342888140491829360)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 233139950809966880)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 96338548832470852)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 169881157450468480)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 139379935722249160)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 99207321134550440)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 69061423187642460)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 37223353832661080)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 21017946685360344)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial172.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial172.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 1761216249351386800)⟩, ⟨(314159265359/50000000000), (Int.ofNat 680587219587294000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 224984222220323460)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 179917185538792880)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 89854241318765680)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 33621982453631634)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 793581355788527)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 8114837368093472)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 8269528377390274)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial172.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial172.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 1761216249351386800)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 680587219587294000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 224984222220323460)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 179917185538792880)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 89854241318765680)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 33621982453631634)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 793581355788527)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 8114837368093472)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 8269528377390274)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial172.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial172.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial172.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 798378611110605866482758850130815), (Int.ofNat 754021205001942149374309573666992), (Int.ofNat 78395781804114956932846641339202), (Int.negOfNat 17669579970928066630888615653194), (Int.negOfNat 2448006956397479860052134437269), (Int.ofNat 297628549642996556659910310599), (Int.ofNat 41914645579957102556317743393), (Int.negOfNat 3346369422261173754729386422), (Int.negOfNat 444100770673083956501822917), (Int.ofNat 26166576403924131356835866), (Int.ofNat 3178621326278842507250425), (Int.negOfNat 148716267117655808171754), (Int.negOfNat 16356765877896077704806), (Int.ofNat 636605571887560421230), (Int.ofNat 63409204916635413127), (Int.negOfNat 2085228490296092080), (Int.negOfNat 200045094891897916), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-159675722222121173296551770026163/450359962737049600000000000000000), (47126325312621384335894348354187/140737488355328000000000000000000), (39197890902057478466423320669601/1125899906842624000000000000000000), (-8834789985464033315444307826597/1125899906842624000000000000000000), (-2448006956397479860052134437269/2251799813685248000000000000000000), (297628549642996556659910310599/2251799813685248000000000000000000), (41914645579957102556317743393/2251799813685248000000000000000000), (-1673184711130586877364693211/1125899906842624000000000000000000), (-444100770673083956501822917/2251799813685248000000000000000000), (13083288201962065678417933/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial172.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial172.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial172.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial172 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 854403087660623703506855162552456), (Int.ofNat 807211638950960320215282863199287), (Int.negOfNat 55396631769940020239312605790107), (Int.negOfNat 21130345959751756297845277842932), (Int.ofNat 1748941533812995820275323362792), (Int.ofNat 393147533048620751107227658800), (Int.negOfNat 29393897388482519195673379694), (Int.negOfNat 4739015687882293233144541507), (Int.ofNat 309304007156326505332333858), (Int.ofNat 38660909758019294470934880), (Int.negOfNat 2223318461942940236967963), (Int.negOfNat 225133692480519632832726), (Int.ofNat 11539224784037105184118), (Int.ofNat 977053015524739988808), (Int.negOfNat 45154349651448562860), (Int.negOfNat 3241593428217933017), (Int.ofNat 143156029752528920), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(106800385957577962938356895319057/281474976710656000000000000000000), (807211638950960320215282863199287/2251799813685248000000000000000000), (-55396631769940020239312605790107/2251799813685248000000000000000000), (-5282586489937939074461319460733/562949953421312000000000000000000), (218617691726624477534415420349/281474976710656000000000000000000), (982868832621551877768069147/5629499534213120000000000000000), (-14696948694241259597836689847/1125899906842624000000000000000000), (-4739015687882293233144541507/2251799813685248000000000000000000), (154652003578163252666166929/1125899906842624000000000000000000), (241630685987620590443343/14073748835532800000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial172.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial172.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial172.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial172 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 2116369345855378668597193696258862), (Int.ofNat 412104397219833103942884909713543), (Int.negOfNat 118290075485256626305498718225932), (Int.ofNat 1950216236508224230008957066839), (Int.ofNat 3054534639689664816239317552311), (Int.negOfNat 164296659877821805697355861244), (Int.negOfNat 45061371715106804969184961790), (Int.ofNat 2829453206159215455402256278), (Int.ofNat 428645295533682732334277928), (Int.negOfNat 27537657573915569915260991), (Int.negOfNat 2843030630204899952388680), (Int.ofNat 178362330734262433049957), (Int.ofNat 13848930855417853408557), (Int.negOfNat 830304089085690880707), (Int.negOfNat 51424424097521765110), (Int.ofNat 2921220458246622297), (Int.ofNat 145260783213207158), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(1058184672927689334298596848129431/1125899906842624000000000000000000), (412104397219833103942884909713543/2251799813685248000000000000000000), (-29572518871314156576374679556483/562949953421312000000000000000000), (1950216236508224230008957066839/2251799813685248000000000000000000), (3054534639689664816239317552311/2251799813685248000000000000000000), (-41074164969455451424338965311/562949953421312000000000000000000), (-4506137171510680496918496179/225179981368524800000000000000000), (1414726603079607727701128139/1125899906842624000000000000000000), (53580661941710341541784741/281474976710656000000000000000000), (-27537657573915569915260991/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial172.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial172.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial172.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial172 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 2524206008706439092339985256647934), (Int.ofNat 39927107254314423031805558931811), (Int.negOfNat 54722719458781831497898176501490), (Int.ofNat 14774540672615323295902871139227), (Int.negOfNat 160085500136712247857834154118), (Int.negOfNat 347406580895802477819048726217), (Int.ofNat 17743748242403575838280804115), (Int.ofNat 4177482807363564888535765761), (Int.negOfNat 274962622549891058559416791), (Int.negOfNat 32483877336082353789686375), (Int.ofNat 2347197035663462982760728), (Int.ofNat 179109902923103258105610), (Int.negOfNat 13353635329975576998270), (Int.negOfNat 739109921283097022603), (Int.ofNat 55053445285009875101), (Int.ofNat 2313945438254981400), (Int.negOfNat 167964614884699742), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(1262103004353219546169992628323967/1125899906842624000000000000000000), (39927107254314423031805558931811/2251799813685248000000000000000000), (-5472271945878183149789817650149/225179981368524800000000000000000), (14774540672615323295902871139227/2251799813685248000000000000000000), (-80042750068356123928917077059/1125899906842624000000000000000000), (-347406580895802477819048726217/2251799813685248000000000000000000), (3548749648480715167656160823/450359962737049600000000000000000), (4177482807363564888535765761/2251799813685248000000000000000000), (-274962622549891058559416791/2251799813685248000000000000000000), (-259871018688658830317491/18014398509481984000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial172.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial172.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial172.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial172 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 2491273298244551339668173935184126), (Int.negOfNat 29648963189150399816545202235995), (Int.ofNat 8744380503333539529355862305195), (Int.ofNat 4150559769307754080901595050462), (Int.negOfNat 1801553451468286805899137795784), (Int.ofNat 50444762144930208525938199842), (Int.ofNat 33232935069678869117672472345), (Int.negOfNat 2093195779029997690028977533), (Int.negOfNat 325039235264644370442931234), (Int.ofNat 25914138884571713628542266), (Int.ofNat 2082282880335547703899580), (Int.negOfNat 186969329309816179563151), (Int.negOfNat 9584084133546170946984), (Int.ofNat 921623032326422484056), (Int.ofNat 33478785375257810601), (Int.negOfNat 3387264244110075805), (Int.negOfNat 82206943157126126), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(1245636649122275669834086967592063/1125899906842624000000000000000000), (-5929792637830079963309040447199/450359962737049600000000000000000), (1748876100666707905871172461039/450359962737049600000000000000000), (2075279884653877040450797525231/1125899906842624000000000000000000), (-225194181433535850737392224473/281474976710656000000000000000000), (25222381072465104262969099921/1125899906842624000000000000000000), (6646587013935773823534494469/450359962737049600000000000000000), (-2093195779029997690028977533/2251799813685248000000000000000000), (-162519617632322185221465617/1125899906842624000000000000000000), (12957069442285856814271133/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial172.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial172.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial172.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial172 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 2474737504051116452488555945241800), (Int.ofNat 6699356186914037556856951625725), (Int.ofNat 570487953275219876246911433995), (Int.negOfNat 4518858226460592997472909460186), (Int.negOfNat 129547014346963488273588726828), (Int.ofNat 190655595394303934992699154049), (Int.negOfNat 11177254725417439679572630247), (Int.negOfNat 2683224532219763437490546573), (Int.ofNat 234974145117625477054977225), (Int.ofNat 21101205530472828192194188), (Int.negOfNat 2260624400748478892864121), (Int.negOfNat 110095213414958139944786), (Int.ofNat 13656200753391330840263), (Int.ofNat 415835714123533995988), (Int.negOfNat 58271325069689818075), (Int.negOfNat 1178870987373503615), (Int.ofNat 192773200016870564), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(12373687520255582262442779726209/11258999068426240000000000000000), (267974247476561502274278065029/90071992547409920000000000000000), (114097590655043975249382286799/450359962737049600000000000000000), (-2259429113230296498736454730093/1125899906842624000000000000000000), (-32386753586740872068397181707/562949953421312000000000000000000), (190655595394303934992699154049/2251799813685248000000000000000000), (-11177254725417439679572630247/2251799813685248000000000000000000), (-2683224532219763437490546573/2251799813685248000000000000000000), (9398965804705019082199089/90071992547409920000000000000000), (5275301382618207048048547/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial172.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial172.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial172.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial172 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 2457305207412919425921261565493381), (Int.negOfNat 37209397963195443042145516520235), (Int.negOfNat 18394877776237377749721945260961), (Int.negOfNat 723221625703305477969392596801), (Int.ofNat 670109810670620834868473060958), (Int.negOfNat 41079088947181302431069356758), (Int.negOfNat 16615988194341113814370099213), (Int.ofNat 1728768637192929955805710712), (Int.ofNat 176290534075334208735796915), (Int.negOfNat 23375780333342498518792797), (Int.negOfNat 1076630364795437672220522), (Int.ofNat 177988215255286845739297), (Int.ofNat 4327325020237313061067), (Int.negOfNat 905768114022711490238), (Int.negOfNat 12135561331983820306), (Int.ofNat 3416410039511541885), (Int.ofNat 19153103101045094), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(2457305207412919425921261565493381/2251799813685248000000000000000000), (-7441879592639088608429103304047/450359962737049600000000000000000), (-18394877776237377749721945260961/2251799813685248000000000000000000), (-723221625703305477969392596801/2251799813685248000000000000000000), (335054905335310417434236530479/1125899906842624000000000000000000), (-20539544473590651215534678379/1125899906842624000000000000000000), (-16615988194341113814370099213/2251799813685248000000000000000000), (216096079649116244475713839/281474976710656000000000000000000), (35258106815066841747159383/450359962737049600000000000000000), (-23375780333342498518792797/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial172.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial172.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial172.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial172 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 2312118646884577215259806778535512), (Int.negOfNat 103602949365008223648243974141311), (Int.negOfNat 12563051302916231656566014341016), (Int.ofNat 1485490596851794540672395786477), (Int.negOfNat 157128919741840782539998604109), (Int.negOfNat 66682915488710839873593247152), (Int.ofNat 10692829248841832936154168293), (Int.ofNat 1099841591928660146996895302), (Int.negOfNat 205969764747075575601401896), (Int.negOfNat 8226004030443612315139711), (Int.ofNat 2025548316764982455246240), (Int.ofNat 33124478003778753555758), (Int.negOfNat 12531267054454515702852), (Int.negOfNat 64665030577063272675), (Int.ofNat 54164892247493307912), (Int.negOfNat 64547774131260046), (Int.negOfNat 196563838463681042), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(289014830860572151907475847316939/281474976710656000000000000000000), (-103602949365008223648243974141311/2251799813685248000000000000000000), (-1570381412864528957070751792627/281474976710656000000000000000000), (1485490596851794540672395786477/2251799813685248000000000000000000), (-157128919741840782539998604109/2251799813685248000000000000000000), (-4167682218044427492099577947/140737488355328000000000000000000), (10692829248841832936154168293/2251799813685248000000000000000000), (549920795964330073498447651/1125899906842624000000000000000000), (-25746220593384446950175237/281474976710656000000000000000000), (-8226004030443612315139711/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial172.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial172.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial172.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial172 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 2062666823547743135245813062982266), (Int.negOfNat 144065700951381268899258339655479), (Int.negOfNat 9834035984096829877715663948704), (Int.negOfNat 494293467937312425183223792292), (Int.negOfNat 111220875480959777511367751314), (Int.ofNat 61235430291412314763685208486), (Int.ofNat 4074672417257485647559623825), (Int.negOfNat 1562692640437050631036219254), (Int.negOfNat 37775726305127278844244832), (Int.ofNat 20000086220494281514166495), (Int.ofNat 79989895527445227699432), (Int.negOfNat 152941661545903684879322), (Int.ofNat 902130581869428845584), (Int.ofNat 786359578760470255303), (Int.negOfNat 8789002129844449136), (Int.negOfNat 2972582673850437490), (Int.ofNat 39421847024456142), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(1031333411773871567622906531491133/1125899906842624000000000000000000), (-144065700951381268899258339655479/2251799813685248000000000000000000), (-307313624503025933678614498397/70368744177664000000000000000000), (-123573366984328106295805948073/562949953421312000000000000000000), (-55610437740479888755683875657/1125899906842624000000000000000000), (30617715145706157381842604243/1125899906842624000000000000000000), (162986896690299425902384953/90071992547409920000000000000000), (-781346320218525315518109627/1125899906842624000000000000000000), (-1180491447035227463882651/70368744177664000000000000000000), (4000017244098856302833299/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial172.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial172.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial172.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial172 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 1731486032149247961899270824997605), (Int.negOfNat 187905202268550317486536125508383), (Int.negOfNat 10621209569019924891021694584036), (Int.ofNat 877111446937497077900811526696), (Int.ofNat 341391717918311684036213017633), (Int.negOfNat 1282000808001130110347784024), (Int.negOfNat 10373768859054688171632715981), (Int.ofNat 83131399198418891680227044), (Int.ofNat 170412803165242299996255183), (Int.negOfNat 2853973916001916807818971), (Int.negOfNat 1629290450351039166367790), (Int.ofNat 36079578019096463376871), (Int.ofNat 10077316189711585741543), (Int.negOfNat 252678207132577331154), (Int.negOfNat 43788420800330624930), (Int.ofNat 1188063629449943963), (Int.ofNat 171067001847740902), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(346297206429849592379854164999521/450359962737049600000000000000000), (-187905202268550317486536125508383/2251799813685248000000000000000000), (-2655302392254981222755423646009/562949953421312000000000000000000), (109638930867187134737601440837/281474976710656000000000000000000), (341391717918311684036213017633/2251799813685248000000000000000000), (-160250101000141263793473003/281474976710656000000000000000000), (-10373768859054688171632715981/2251799813685248000000000000000000), (20782849799604722920056761/562949953421312000000000000000000), (170412803165242299996255183/2251799813685248000000000000000000), (-2853973916001916807818971/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial172.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial172.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial172.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial172 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 1325016252460809314614025025236797), (Int.negOfNat 210837027903296199704831991605122), (Int.ofNat 573560885930927680691010374847), (Int.ofNat 2211281809721992783861711518364), (Int.negOfNat 110452385219484945332318286937), (Int.negOfNat 59366517494151373745845777914), (Int.ofNat 3528174286392411174312277165), (Int.ofNat 1236187324026600961736905085), (Int.negOfNat 64261592711062354812694799), (Int.negOfNat 14916551687825682058825944), (Int.ofNat 716175251226453044994655), (Int.ofNat 112438136087181798114602), (Int.negOfNat 5182211784798229734265), (Int.negOfNat 576631476222170799684), (Int.ofNat 25917933779425760701), (Int.ofNat 2144227493926764583), (Int.negOfNat 85248378841987308), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(1325016252460809314614025025236797/2251799813685248000000000000000000), (-105418513951648099852415995802561/1125899906842624000000000000000000), (573560885930927680691010374847/2251799813685248000000000000000000), (552820452430498195965427879591/562949953421312000000000000000000), (-110452385219484945332318286937/2251799813685248000000000000000000), (-29683258747075686872922888957/1125899906842624000000000000000000), (705634857278482234862455433/450359962737049600000000000000000), (247237464805320192347381017/450359962737049600000000000000000), (-64261592711062354812694799/2251799813685248000000000000000000), (-1864568960978210257353243/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial172.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial172.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial172.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial172 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 920020613015532130611292328240433), (Int.negOfNat 189155371897655139476241161335389), (Int.ofNat 7945646082548873464773415040361), (Int.ofNat 29446669017095507871400827584), (Int.negOfNat 264872494545391194836870297491), (Int.ofNat 36366929526932905833280668092), (Int.ofNat 7273561000300342859818517037), (Int.negOfNat 839209839106800917537441399), (Int.negOfNat 113857187104191093262346694), (Int.ofNat 10601780307424200891053770), (Int.ofNat 1062916874932959328871540), (Int.negOfNat 86332314205810174074169), (Int.negOfNat 6509533260394949872196), (Int.ofNat 484983288531345263564), (Int.ofNat 28138687860586359557), (Int.negOfNat 1985870671787505283), (Int.negOfNat 108013161791659870), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(920020613015532130611292328240433/2251799813685248000000000000000000), (-189155371897655139476241161335389/2251799813685248000000000000000000), (7945646082548873464773415040361/2251799813685248000000000000000000), (460104203392117310490637931/35184372088832000000000000000000), (-264872494545391194836870297491/2251799813685248000000000000000000), (9091732381733226458320167023/562949953421312000000000000000000), (7273561000300342859818517037/2251799813685248000000000000000000), (-839209839106800917537441399/2251799813685248000000000000000000), (-56928593552095546631173347/1125899906842624000000000000000000), (1060178030742420089105377/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial172.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial172.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial172.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial172 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 570989067772605930824683674465505), (Int.negOfNat 161653260308544458431777688267099), (Int.ofNat 5710727034377509702382149078568), (Int.negOfNat 75975227639020462236642820288), (Int.ofNat 225472454603770071266708808812), (Int.ofNat 29061950367373024803432712045), (Int.negOfNat 8070314657765798830418824199), (Int.negOfNat 672693106809873117037035421), (Int.ofNat 126330362381101398109199325), (Int.ofNat 8038902910453938957970035), (Int.negOfNat 1213765997410552867231616), (Int.negOfNat 59679114320864323465842), (Int.ofNat 7879345849840504781566), (Int.ofNat 302125811302666905231), (Int.negOfNat 36579713092582914391), (Int.negOfNat 1093435489530766592), (Int.ofNat 110056963974158130), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(114197813554521186164936734893101/450359962737049600000000000000000), (-161653260308544458431777688267099/2251799813685248000000000000000000), (713840879297188712797768634821/281474976710656000000000000000000), (-1187112931859694722447544067/35184372088832000000000000000000), (56368113650942517816677202203/562949953421312000000000000000000), (5812390073474604960686542409/450359962737049600000000000000000), (-8070314657765798830418824199/2251799813685248000000000000000000), (-672693106809873117037035421/2251799813685248000000000000000000), (5053214495244055924367973/90071992547409920000000000000000), (1607780582090787791594007/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial172.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial172.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial172.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial172 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 273887715792011439281554305630270), (Int.negOfNat 131891644723631765575061387319627), (Int.ofNat 10850575846722676288233012339538), (Int.ofNat 1471707988758271038401847655079), (Int.negOfNat 342633070461254121262497610), (Int.negOfNat 62179509874008170643937607338), (Int.negOfNat 2395043003103520416931589122), (Int.ofNat 1241603509913393333391037730), (Int.ofNat 41108885519620175069515224), (Int.negOfNat 14547585090636577014108621), (Int.negOfNat 379665941443595388854328), (Int.ofNat 111582219305911649197091), (Int.ofNat 2257958817215696098757), (Int.negOfNat 599364944985195240773), (Int.negOfNat 9410954680307949990), (Int.ofNat 2379857837172640271), (Int.ofNat 44959321735578838), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(27388771579201143928155430563027/225179981368524800000000000000000), (-131891644723631765575061387319627/2251799813685248000000000000000000), (5425287923361338144116506169769/1125899906842624000000000000000000), (1471707988758271038401847655079/2251799813685248000000000000000000), (-34263307046125412126249761/225179981368524800000000000000000), (-31089754937004085321968803669/1125899906842624000000000000000000), (-1197521501551760208465794561/1125899906842624000000000000000000), (124160350991339333339103773/225179981368524800000000000000000), (5138610689952521883689403/281474976710656000000000000000000), (-14547585090636577014108621/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial172.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial172.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial172.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial172 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 63293729209377366842545134250533), (Int.negOfNat 75709866486365942205619382875000), (Int.ofNat 14963242690245788033466655224367), (Int.negOfNat 711705272610395799308039011668), (Int.negOfNat 431130964134550887384152536952), (Int.ofNat 2730292535227796871277610299), (Int.ofNat 10190344315124280727411809530), (Int.ofNat 20364163394718358594587223), (Int.negOfNat 148451101917114075311735418), (Int.negOfNat 321501932288189819741136), (Int.ofNat 1373998045263553143079073), (Int.ofNat 1558291331645315393526), (Int.negOfNat 8670919203887912831206), (Int.negOfNat 240920749753907000), (Int.ofNat 39390587338861453028), (Int.negOfNat 80711189042316191), (Int.negOfNat 134865549106328952), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(63293729209377366842545134250533/2251799813685248000000000000000000), (-605678931890927537644955063/18014398509481984000000000000), (14963242690245788033466655224367/2251799813685248000000000000000000), (-177926318152598949827009752917/562949953421312000000000000000000), (-53891370516818860923019067119/281474976710656000000000000000000), (2730292535227796871277610299/2251799813685248000000000000000000), (1019034431512428072741180953/225179981368524800000000000000000), (20364163394718358594587223/2251799813685248000000000000000000), (-74225550958557037655867709/1125899906842624000000000000000000), (-20093870768011863733821/140737488355328000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial172.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial172.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial172.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial172 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 40159405406170899832608372878508), (Int.negOfNat 36155368100025199898290442817863), (Int.ofNat 2771453520413119555617894523104), (Int.negOfNat 2657212614364053243688353766602), (Int.ofNat 63205915294777226170194211787), (Int.ofNat 69856832926887372376132514170), (Int.negOfNat 2211101514907936458568023099), (Int.negOfNat 1277151955623436271545777546), (Int.ofNat 33583295929022023587493275), (Int.ofNat 14566490840303263465496422), (Int.negOfNat 317695000632525106099607), (Int.negOfNat 109826142735507027533874), (Int.ofNat 2062165456303645559318), (Int.ofNat 582847700492208245590), (Int.negOfNat 9682139875716356825), (Int.negOfNat 2303075317230438208), (Int.ofNat 26364046697892468), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-10039851351542724958152093219627/562949953421312000000000000000000), (-36155368100025199898290442817863/2251799813685248000000000000000000), (86607922512909986113059203847/70368744177664000000000000000000), (-1328606307182026621844176883301/1125899906842624000000000000000000), (63205915294777226170194211787/2251799813685248000000000000000000), (6985683292688737237613251417/225179981368524800000000000000000), (-2211101514907936458568023099/2251799813685248000000000000000000), (-638575977811718135772888773/1125899906842624000000000000000000), (1343331837160880943499731/90071992547409920000000000000000), (7283245420151631732748211/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial172.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial172.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial172.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial172 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 119684782975506504737312116486262), (Int.negOfNat 50276498165184044309691648741986), (Int.negOfNat 7334465966639626266026079985446), (Int.negOfNat 296909762310218851352609247369), (Int.ofNat 359400805547907763009169837503), (Int.negOfNat 24970469252076505642935938471), (Int.negOfNat 8995264556386278100036298701), (Int.ofNat 581452818768111534753745990), (Int.ofNat 130403054703612578447375445), (Int.negOfNat 6916820742097173067637914), (Int.negOfNat 1197986472161762779868569), (Int.ofNat 52937784569958616742702), (Int.ofNat 7524995156248851849522), (Int.negOfNat 283329588638163623378), (Int.negOfNat 34179599735912937799), (Int.ofNat 1153755963429928624), (Int.ofNat 109368712490388812), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-59842391487753252368656058243131/1125899906842624000000000000000000), (-25138249082592022154845824370993/1125899906842624000000000000000000), (-3667232983319813133013039992723/1125899906842624000000000000000000), (-296909762310218851352609247369/2251799813685248000000000000000000), (359400805547907763009169837503/2251799813685248000000000000000000), (-24970469252076505642935938471/2251799813685248000000000000000000), (-8995264556386278100036298701/2251799813685248000000000000000000), (58145281876811153475374599/225179981368524800000000000000000), (26080610940722515689475089/450359962737049600000000000000000), (-3458410371048586533818957/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial172.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial172.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial172.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial172 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 247472082935868477887900847389104), (Int.negOfNat 75028465642578542965349132094499), (Int.negOfNat 4066118718600314304592299608507), (Int.ofNat 646923358650544863293162743422), (Int.negOfNat 162096286688841120704373451004), (Int.negOfNat 47051792778925324018137331198), (Int.ofNat 6219724850316758767772055614), (Int.ofNat 948352965191141276195500823), (Int.negOfNat 97244582340954414821974158), (Int.negOfNat 10914666452736810894231560), (Int.ofNat 913777584546748676732519), (Int.ofNat 82673263190956017338222), (Int.negOfNat 5773028147294128691610), (Int.negOfNat 441400823608375806008), (Int.ofNat 26172288439620337996), (Int.ofNat 1790771309793787353), (Int.negOfNat 84938996823393704), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-15467005183491779867993802961819/140737488355328000000000000000000), (-75028465642578542965349132094499/2251799813685248000000000000000000), (-4066118718600314304592299608507/2251799813685248000000000000000000), (323461679325272431646581371711/1125899906842624000000000000000000), (-40524071672210280176093362751/562949953421312000000000000000000), (-23525896389462662009068665599/1125899906842624000000000000000000), (3109862425158379383886027807/1125899906842624000000000000000000), (948352965191141276195500823/2251799813685248000000000000000000), (-48622291170477207410987079/1125899906842624000000000000000000), (-272866661318420272355789/56294995342131200000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial172.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial172.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial172.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial172 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 412227253292660742521467186846754), (Int.negOfNat 90981313575895378764951302845217), (Int.negOfNat 5921157586031801809394210478415), (Int.negOfNat 1221854018072648096146585541027), (Int.negOfNat 131902636176381420993737012771), (Int.ofNat 50790825676492988019408142800), (Int.ofNat 5148562933694301007037570594), (Int.negOfNat 1046553549705014663271847038), (Int.negOfNat 77880489307878205555448760), (Int.ofNat 12417673221768987195218187), (Int.ofNat 729568364305353939557512), (Int.negOfNat 94812111786296979761749), (Int.negOfNat 4679708954891609124701), (Int.ofNat 503491750745181519659), (Int.ofNat 21592940485086609294), (Int.negOfNat 1989747931380458841), (Int.negOfNat 54584400811698054), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-206113626646330371260733593423377/1125899906842624000000000000000000), (-90981313575895378764951302845217/2251799813685248000000000000000000), (-1184231517206360361878842095683/450359962737049600000000000000000), (-1221854018072648096146585541027/2251799813685248000000000000000000), (-131902636176381420993737012771/2251799813685248000000000000000000), (126977064191232470048520357/5629499534213120000000000000000), (2574281466847150503518785297/1125899906842624000000000000000000), (-523276774852507331635923519/1125899906842624000000000000000000), (-1947012232696955138886219/56294995342131200000000000000000), (12417673221768987195218187/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial172.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial172.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial172.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial172 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 627951970927238664312891903682245), (Int.negOfNat 129014700448345151140144060744488), (Int.negOfNat 11899143835054653205859694132291), (Int.negOfNat 73712544565175128649594894555), (Int.ofNat 360134468131323540681235257747), (Int.ofNat 17593653049175755701379864100), (Int.negOfNat 8986435261839904085995202015), (Int.negOfNat 362044788821004415690381661), (Int.ofNat 137863476597235387875074763), (Int.ofNat 4364243106814137753451643), (Int.negOfNat 1303627953153383790991056), (Int.negOfNat 35151105429365054139738), (Int.ofNat 8260039851869904179778), (Int.ofNat 199447941529712320511), (Int.negOfNat 37329115891703518785), (Int.negOfNat 863123319830835736), (Int.ofNat 109747581955564526), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-125590394185447732862578380736449/450359962737049600000000000000000), (-16126837556043143892518007593061/281474976710656000000000000000000), (-11899143835054653205859694132291/2251799813685248000000000000000000), (-14742508913035025729918978911/450359962737049600000000000000000), (360134468131323540681235257747/2251799813685248000000000000000000), (175936530491757557013798641/22517998136852480000000000000000), (-1797287052367980817199040403/450359962737049600000000000000000), (-362044788821004415690381661/2251799813685248000000000000000000), (137863476597235387875074763/2251799813685248000000000000000000), (4364243106814137753451643/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial172.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial172.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial172.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial172 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 928427817248587157471444728301230), (Int.negOfNat 166307256638612823249900160690437), (Int.negOfNat 4439008332555263229556100741640), (Int.ofNat 2120499621271494654514072915359), (Int.ofNat 49590585115607813017240630518), (Int.negOfNat 60782603235109907682188966336), (Int.negOfNat 78965240827850341214101325), (Int.ofNat 1249364365208946994402726057), (Int.ofNat 1563975904153838202195062), (Int.negOfNat 15091011406109489717469486), (Int.negOfNat 51229055457882873001780), (Int.ofNat 116635594055004953093439), (Int.ofNat 605370815983631578380), (Int.negOfNat 623754381699786574700), (Int.negOfNat 4104740507362741965), (Int.ofNat 2455791717243912349), (Int.negOfNat 8469439244382978), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-92842781724858715747144472830123/225179981368524800000000000000000), (-166307256638612823249900160690437/2251799813685248000000000000000000), (-110975208313881580738902518541/56294995342131200000000000000000), (2120499621271494654514072915359/2251799813685248000000000000000000), (24795292557803906508620315259/1125899906842624000000000000000000), (-949728175548592307534202599/35184372088832000000000000000000), (-3158609633114013648564053/90071992547409920000000000000000), (1249364365208946994402726057/2251799813685248000000000000000000), (781987952076919101097531/1125899906842624000000000000000000), (-7545505703054744858734743/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial172.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial172.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial172.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial172 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 1262838238388845901379850924741504), (Int.negOfNat 161380585024484784643980403531363), (Int.ofNat 5368075809296729296059250061956), (Int.ofNat 698630007977781327093420250162), (Int.negOfNat 268157435014599469092116021461), (Int.ofNat 16388370438392210109235519710), (Int.ofNat 8900254023603530899771875275), (Int.negOfNat 383017412806886185600096571), (Int.negOfNat 145028463362412151231440681), (Int.ofNat 3978029921291152009855448), (Int.ofNat 1408494784376720188512761), (Int.negOfNat 25068002726901114350782), (Int.negOfNat 9076401333173214891799), (Int.ofNat 104827599741522976836), (Int.ofNat 41676874069996181619), (Int.negOfNat 271951131050642049), (Int.negOfNat 134556167087735348), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-9865923737412858604530085349543/17592186044416000000000000000000), (-161380585024484784643980403531363/2251799813685248000000000000000000), (1342018952324182324014812515489/562949953421312000000000000000000), (349315003988890663546710125081/1125899906842624000000000000000000), (-268157435014599469092116021461/2251799813685248000000000000000000), (1638837043839221010923551971/225179981368524800000000000000000), (356010160944141235990875011/90071992547409920000000000000000), (-383017412806886185600096571/2251799813685248000000000000000000), (-145028463362412151231440681/2251799813685248000000000000000000), (497253740161394001231931/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial172.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial172.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial172.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial172 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 1561817301446719804218888028014283), (Int.negOfNat 137390060504790648020238154054522), (Int.ofNat 6087198299773586071459604453834), (Int.ofNat 199564845286172193769800957822), (Int.ofNat 192904410783826033985228428122), (Int.ofNat 43836654200054777256987560144), (Int.negOfNat 6153667125588999857176053731), (Int.negOfNat 1112397390523683012046271372), (Int.ofNat 86741537567614431558942929), (Int.ofNat 14227951391246671557667749), (Int.negOfNat 730112699533569622265450), (Int.negOfNat 113727001015833766494873), (Int.ofNat 4072645670441044730193), (Int.ofNat 621903973173472376174), (Int.negOfNat 16115239647203906318), (Int.negOfNat 2484937512645378429), (Int.ofNat 71523279300464010), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-1561817301446719804218888028014283/2251799813685248000000000000000000), (-68695030252395324010119077027261/1125899906842624000000000000000000), (3043599149886793035729802226917/1125899906842624000000000000000000), (99782422643086096884900478911/1125899906842624000000000000000000), (96452205391913016992614214061/1125899906842624000000000000000000), (2739790887503423578561722509/140737488355328000000000000000000), (-6153667125588999857176053731/2251799813685248000000000000000000), (-278099347630920753011567843/562949953421312000000000000000000), (86741537567614431558942929/2251799813685248000000000000000000), (14227951391246671557667749/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial172.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial172.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial172.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial172 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 1806670557116812801831609388579385), (Int.negOfNat 102529757673357088025150561521758), (Int.ofNat 13406570800873901603374230808231), (Int.ofNat 2105273554375198587566632531632), (Int.ofNat 91201594907717002625183435608), (Int.negOfNat 64560991472288610755546853733), (Int.negOfNat 6226204704693494136193895369), (Int.ofNat 1183700631384296592728556394), (Int.ofNat 114286548160450477026769928), (Int.negOfNat 12822638485132205949592433), (Int.negOfNat 1188335146911745392815952), (Int.ofNat 88999567563623460511694), (Int.ofNat 8016552872549676673520), (Int.negOfNat 426582988903915920793), (Int.negOfNat 37775490394974150184), (Int.ofNat 1515369892555405710), (Int.ofNat 138346805534545826), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-361334111423362560366321877715877/450359962737049600000000000000000), (-51264878836678544012575280760879/1125899906842624000000000000000000), (13406570800873901603374230808231/2251799813685248000000000000000000), (131579597148449911722914533227/140737488355328000000000000000000), (11400199363464625328147929451/281474976710656000000000000000000), (-64560991472288610755546853733/2251799813685248000000000000000000), (-6226204704693494136193895369/2251799813685248000000000000000000), (591850315692148296364278197/1125899906842624000000000000000000), (14285818520056309628346241/281474976710656000000000000000000), (-12822638485132205949592433/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial172.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial172.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial172.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial172 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 1942093604094783544829602646923341), (Int.negOfNat 26469178848059596437238464223238), (Int.ofNat 22498321226079529600022282977435), (Int.ofNat 41252935665602231183135141085), (Int.negOfNat 531630279518417284345629681579), (Int.negOfNat 20806846844750380547051328475), (Int.ofNat 12207921418940463978628904987), (Int.ofNat 637783430053051876966918150), (Int.negOfNat 172685020221714973679373280), (Int.negOfNat 9563249651976343189596239), (Int.ofNat 1502427406691368378138280), (Int.ofNat 84934098238256850521974), (Int.negOfNat 8686814606004154473052), (Int.negOfNat 494802640939759851811), (Int.ofNat 35778754038057618288), (Int.ofNat 2041110146984274034), (Int.negOfNat 130098229425965246), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-1942093604094783544829602646923341/2251799813685248000000000000000000), (-13234589424029798218619232111619/1125899906842624000000000000000000), (4499664245215905920004456595487/450359962737049600000000000000000), (8250587133120446236627028217/450359962737049600000000000000000), (-531630279518417284345629681579/2251799813685248000000000000000000), (-832273873790015221882053139/90071992547409920000000000000000), (12207921418940463978628904987/2251799813685248000000000000000000), (12755668601061037539338363/45035996273704960000000000000000), (-1079281376385718585496083/14073748835532800000000000000000), (-9563249651976343189596239/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial172.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial172.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial172.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial172 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 1913065044028582519202213096940440), (Int.ofNat 47781623137403238087075037198194), (Int.ofNat 11346185437870211646601719177885), (Int.negOfNat 3068929139259049978363519588270), (Int.negOfNat 38070517769836957032760150701), (Int.ofNat 96244754086094543809766071051), (Int.ofNat 1082837117545651223208153965), (Int.negOfNat 1867651716836386846295584424), (Int.negOfNat 43312702851935663248252547), (Int.ofNat 20976985007947423466131443), (Int.ofNat 646555428103316425408242), (Int.negOfNat 148206857877523097449247), (Int.negOfNat 5169627922243010911363), (Int.ofNat 720949034736311748930), (Int.ofNat 26675921596095015874), (Int.negOfNat 2638885747874089627), (Int.negOfNat 112849968918605686), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-47826626100714562980055327423511/56294995342131200000000000000000), (23890811568701619043537518599097/1125899906842624000000000000000000), (2269237087574042329320343835577/450359962737049600000000000000000), (-306892913925904997836351958827/225179981368524800000000000000000), (-38070517769836957032760150701/2251799813685248000000000000000000), (96244754086094543809766071051/2251799813685248000000000000000000), (216567423509130244641630793/450359962737049600000000000000000), (-233456464604548355786948053/281474976710656000000000000000000), (-43312702851935663248252547/2251799813685248000000000000000000), (20976985007947423466131443/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial172.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial172.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial172.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial172 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 1794367547327598161805000865865663), (Int.ofNat 62197269175420526371098056221349), (Int.negOfNat 1254588823595047425568790823832), (Int.negOfNat 357863903188950307975761525028), (Int.ofNat 504531504034036963291100360645), (Int.negOfNat 24194674603405705800342455198), (Int.negOfNat 15971557339653193032585679393), (Int.ofNat 253371642166488196486554491), (Int.ofNat 246532669236632007939004415), (Int.ofNat 1236194021861375304052940), (Int.negOfNat 2181129657999412153363855), (Int.negOfNat 33440432638652296585530), (Int.ofNat 12647399129775667108841), (Int.ofNat 260010086864530004828), (Int.negOfNat 52305807255926249365), (Int.negOfNat 1212754967060601127), (Int.ofNat 175924761243496412), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-1794367547327598161805000865865663/2251799813685248000000000000000000), (62197269175420526371098056221349/2251799813685248000000000000000000), (-156823602949380928196098852979/281474976710656000000000000000000), (-89465975797237576993940381257/562949953421312000000000000000000), (100906300806807392658220072129/450359962737049600000000000000000), (-12097337301702852900171227599/1125899906842624000000000000000000), (-15971557339653193032585679393/2251799813685248000000000000000000), (253371642166488196486554491/2251799813685248000000000000000000), (49306533847326401587800883/450359962737049600000000000000000), (61809701093068765202647/112589990684262400000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial172.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial172.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial172.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial172 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 1671484252739147450693178174312672), (Int.ofNat 64385024732871881600317902022503), (Int.ofNat 3530792568727880939963481865855), (Int.ofNat 712017968245653523827999381507), (Int.negOfNat 372748548626054807775241971194), (Int.negOfNat 98896820972220490124214785070), (Int.ofNat 8958102845983041633457400297), (Int.ofNat 2430544726949334706978418163), (Int.negOfNat 67583142762528010915302814), (Int.negOfNat 28000277754243003114437870), (Int.ofNat 150425176881401605476020), (Int.ofNat 196474477065802598314697), (Int.ofNat 970302171424065256960), (Int.negOfNat 949284472410412459648), (Int.negOfNat 9768456837828881953), (Int.ofNat 3436692790211650947), (Int.ofNat 49796128862524654), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-52233882898098357834161817947271/70368744177664000000000000000000), (64385024732871881600317902022503/2251799813685248000000000000000000), (706158513745576187992696373171/450359962737049600000000000000000), (712017968245653523827999381507/2251799813685248000000000000000000), (-186374274313027403887620985597/1125899906842624000000000000000000), (-9889682097222049012421478507/225179981368524800000000000000000), (8958102845983041633457400297/2251799813685248000000000000000000), (2430544726949334706978418163/2251799813685248000000000000000000), (-33791571381264005457651407/1125899906842624000000000000000000), (-2800027775424300311443787/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial172.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial172.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial172.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial172 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 1531170220854549644431857816082097), (Int.ofNat 69890789696920016415412678103806), (Int.negOfNat 5514495095450422236132003744944), (Int.negOfNat 3692640150597412031562501957453), (Int.negOfNat 322172369054562240844215458779), (Int.ofNat 132849005008018138645011199766), (Int.ofNat 19860573257407071596846410123), (Int.negOfNat 1579295564096485543132855039), (Int.negOfNat 315618225753340155486010817), (Int.ofNat 9551044491296959256883073), (Int.ofNat 2726487984762610298237304), (Int.negOfNat 31985952239929192682846), (Int.negOfNat 15494946899343132324834), (Int.ofNat 43399121656494043717), (Int.ofNat 63425025313623490235), (Int.ofNat 161962962664603136), (Int.negOfNat 200733346375667234), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-1531170220854549644431857816082097/2251799813685248000000000000000000), (34945394848460008207706339051903/1125899906842624000000000000000000), (-344655943465651389758250234059/140737488355328000000000000000000), (-3692640150597412031562501957453/2251799813685248000000000000000000), (-322172369054562240844215458779/2251799813685248000000000000000000), (66424502504009069322505599883/1125899906842624000000000000000000), (19860573257407071596846410123/2251799813685248000000000000000000), (-1579295564096485543132855039/2251799813685248000000000000000000), (-315618225753340155486010817/2251799813685248000000000000000000), (9551044491296959256883073/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial172.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial172.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial172.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial172 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 1442895649732041202196395498619534), (Int.ofNat 6657278330333731533210220347044), (Int.negOfNat 21561386643899832693135684813688), (Int.ofNat 861827592124132115938546981080), (Int.ofNat 1474175889147411033574752391188), (Int.ofNat 135920757880976604420026787516), (Int.negOfNat 23351687775445916757304225662), (Int.negOfNat 3166306378034759752197457290), (Int.ofNat 195567168861895379484198728), (Int.ofNat 34089956102718480690206537), (Int.negOfNat 1038763601275943606133224), (Int.negOfNat 229258894474366000954323), (Int.ofNat 3810694470847984301387), (Int.ofNat 1081265601380633120685), (Int.negOfNat 10089154736062247474), (Int.negOfNat 3830679955596785935), (Int.ofNat 13257711193556378), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-721447824866020601098197749309767/1125899906842624000000000000000000), (1664319582583432883302555086761/562949953421312000000000000000000), (-2695173330487479086641960601711/281474976710656000000000000000000), (21545689803103302898463674527/56294995342131200000000000000000), (368543972286852758393688097797/562949953421312000000000000000000), (33980189470244151105006696879/562949953421312000000000000000000), (-11675843887722958378652112831/1125899906842624000000000000000000), (-316630637803475975219745729/225179981368524800000000000000000), (24445896107736922435524841/281474976710656000000000000000000), (34089956102718480690206537/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial172.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial172.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial172.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial172 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 1482829525451211545328642117692813), (Int.negOfNat 16830025021735222002349155083225), (Int.ofNat 22620841614052213966249765663471), (Int.ofNat 13091479510383887709985292692194), (Int.ofNat 879415491052648068847743926176), (Int.negOfNat 268364213599365277162457024137), (Int.negOfNat 29301895375990658571692593450), (Int.ofNat 2868943555061081253128679613), (Int.ofNat 389406629210244350912467238), (Int.negOfNat 19822843785338892219601224), (Int.negOfNat 3095741608918528946228989), (Int.ofNat 97413456324191649512610), (Int.ofNat 16847308380552991776138), (Int.negOfNat 360687715358760882680), (Int.negOfNat 67359143448609370884), (Int.ofNat 1012183715908479647), (Int.ofNat 225541931507838056), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-1482829525451211545328642117692813/2251799813685248000000000000000000), (-673201000869408880093966203329/90071992547409920000000000000000), (22620841614052213966249765663471/2251799813685248000000000000000000), (6545739755191943854992646346097/1125899906842624000000000000000000), (27481734095395252151491997693/70368744177664000000000000000000), (-268364213599365277162457024137/2251799813685248000000000000000000), (-586037907519813171433851869/45035996273704960000000000000000), (2868943555061081253128679613/2251799813685248000000000000000000), (194703314605122175456233619/1125899906842624000000000000000000), (-2477855473167361527450153/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial172.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial172.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial172.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial172 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 1317212843203650628910741174644072), (Int.ofNat 233421292075333447645399372306387), (Int.ofNat 96276638952816668359644731947756), (Int.ofNat 6860097931530531482383189605193), (Int.negOfNat 2438380284752746142722759084158), (Int.negOfNat 265063123189557924261504984450), (Int.ofNat 33063926483460364033051641653), (Int.ofNat 4148021842159934658487211274), (Int.negOfNat 288930313741226193490872683), (Int.negOfNat 38485826796097657569827670), (Int.ofNat 1786246492716895706295991), (Int.ofNat 241025706453317511310262), (Int.negOfNat 8236962319815596767554), (Int.negOfNat 1094123507159370607258), (Int.ofNat 29387298439261033017), (Int.ofNat 3753897435654583872), (Int.negOfNat 84581079627027684), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-164651605400456328613842646830509/281474976710656000000000000000000), (233421292075333447645399372306387/2251799813685248000000000000000000), (24069159738204167089911182986939/562949953421312000000000000000000), (6860097931530531482383189605193/2251799813685248000000000000000000), (-1219190142376373071361379542079/1125899906842624000000000000000000), (-5301262463791158485230099689/45035996273704960000000000000000), (33063926483460364033051641653/2251799813685248000000000000000000), (2074010921079967329243605637/1125899906842624000000000000000000), (-288930313741226193490872683/2251799813685248000000000000000000), (-3848582679609765756982767/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial172.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial172.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial172.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial172.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial172 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial172 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial172 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 1897186205142553351545887554179225), (Int.negOfNat 321500364765090679642347031742128), (Int.ofNat 113282305165750345047489673402006), (Int.negOfNat 6122680859034950597539763182462), (Int.negOfNat 2528560832611427209381329587659), (Int.ofNat 262964543909563627909990324761), (Int.ofNat 33264681481287280973934996007), (Int.negOfNat 4144903017996078245338265354), (Int.negOfNat 289175980602104311096905243), (Int.ofNat 38482965164378205005488390), (Int.ofNat 1786435761426239060676791), (Int.negOfNat 241023841333711031575222), (Int.negOfNat 8236962319815596767554), (Int.ofNat 1094123507159370607258), (Int.ofNat 29387298439261033017), (Int.negOfNat 3753897435654583872), (Int.negOfNat 84581079627027684), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-75887448205702134061835502167169/90071992547409920000000000000000), (-20093772797818167477646689483883/140737488355328000000000000000000), (56641152582875172523744836701003/1125899906842624000000000000000000), (-3061340429517475298769881591231/1125899906842624000000000000000000), (-2528560832611427209381329587659/2251799813685248000000000000000000), (262964543909563627909990324761/2251799813685248000000000000000000), (33264681481287280973934996007/2251799813685248000000000000000000), (-2072451508998039122669132677/1125899906842624000000000000000000), (-289175980602104311096905243/2251799813685248000000000000000000), (3848296516437820500548839/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial172.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial172.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial172.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 2166535891269922406976987566315120), (Int.ofNat 2608643204071736757883228647129), (Int.ofNat 41768616624648923282684073184091), (Int.negOfNat 13126035296096133605406922508932), (Int.ofNat 780883644676642512775599862432), (Int.ofNat 268822417808920370804626225640), (Int.negOfNat 29086257706626846381958978890), (Int.negOfNat 2869978808652804805942058253), (Int.ofNat 389145083871486826236195878), (Int.ofNat 19823979453220829226626104), (Int.negOfNat 3095540820246977667850509), (Int.negOfNat 97414155744044079413250), (Int.ofNat 16847308380552991776138), (Int.ofNat 360687715358760882680), (Int.negOfNat 67359143448609370884), (Int.negOfNat 1012183715908479647), (Int.ofNat 225541931507838056), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-27081698640874030087212344578939/28147497671065600000000000000000), (2608643204071736757883228647129/2251799813685248000000000000000000), (41768616624648923282684073184091/2251799813685248000000000000000000), (-3281508824024033401351730627233/562949953421312000000000000000000), (24402613896145078524237495701/70368744177664000000000000000000), (6720560445223009270115655641/56294995342131200000000000000000), (-2908625770662684638195897889/225179981368524800000000000000000), (-2869978808652804805942058253/2251799813685248000000000000000000), (194572541935743413118097939/1125899906842624000000000000000000), (2477997431652603653328263/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial172.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial172.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial172.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 2080278370308904673025356765707126), (Int.ofNat 52222082168312076408767463963537), (Int.negOfNat 4898458145461863851051269277028), (Int.negOfNat 1632847239385133662688325411911), (Int.ofNat 1392588775351135075807247967401), (Int.negOfNat 133075159652113066233980650964), (Int.negOfNat 23178416283856244606188062482), (Int.ofNat 3161436064112419746137690970), (Int.ofNat 195360390306964857150339128), (Int.negOfNat 34085151573052705234402377), (Int.negOfNat 1038605957138863617869464), (Int.ofNat 229255863655005471384883), (Int.ofNat 3810694470847984301387), (Int.negOfNat 1081265601380633120685), (Int.negOfNat 10089154736062247474), (Int.ofNat 3830679955596785935), (Int.ofNat 13257711193556378), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-1040139185154452336512678382853563/1125899906842624000000000000000000), (52222082168312076408767463963537/2251799813685248000000000000000000), (-1224614536365465962762817319257/562949953421312000000000000000000), (-1632847239385133662688325411911/2251799813685248000000000000000000), (1392588775351135075807247967401/2251799813685248000000000000000000), (-33268789913028266558495162741/562949953421312000000000000000000), (-11589208141928122303094031241/1125899906842624000000000000000000), (316143606411241974613769097/225179981368524800000000000000000), (24420048788370607143792391/281474976710656000000000000000000), (-34085151573052705234402377/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial172.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial172.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial172.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 1991514582641263612579717943612214), (Int.ofNat 44035795569367564829523894192029), (Int.ofNat 4829838268562687194771797628682), (Int.ofNat 2407401147628045822329207597221), (Int.negOfNat 366481142104807806773410237602), (Int.negOfNat 128415034965788794213774787975), (Int.ofNat 19946208873871298936327082637), (Int.ofNat 1571941632043233454505930879), (Int.negOfNat 315714837387725093233600737), (Int.negOfNat 9543896623259843030189713), (Int.ofNat 2726559367117890598755464), (Int.ofNat 31981522580863803312126), (Int.negOfNat 15494946899343132324834), (Int.negOfNat 43399121656494043717), (Int.ofNat 63425025313623490235), (Int.negOfNat 161962962664603136), (Int.negOfNat 200733346375667234), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-995757291320631806289858971806107/1125899906842624000000000000000000), (44035795569367564829523894192029/2251799813685248000000000000000000), (2414919134281343597385898814341/1125899906842624000000000000000000), (2407401147628045822329207597221/2251799813685248000000000000000000), (-183240571052403903386705118801/1125899906842624000000000000000000), (-5136601398631551768550991519/90071992547409920000000000000000), (19946208873871298936327082637/2251799813685248000000000000000000), (1571941632043233454505930879/2251799813685248000000000000000000), (-315714837387725093233600737/2251799813685248000000000000000000), (-9543896623259843030189713/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial172.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial172.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial172.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 1873442557521484331603497404809054), (Int.ofNat 74445928148321795855382060181755), (Int.ofNat 5470470172218454159374060958341), (Int.negOfNat 2164918657579455654420821200174), (Int.negOfNat 369717206815812242889607386664), (Int.ofNat 103712254180443865309510396470), (Int.ofNat 8934937078370578303258803007), (Int.negOfNat 2438371379265053480973994163), (Int.negOfNat 67544463206863489283438974), (Int.ofNat 28007810187002612001504270), (Int.ofNat 150391193622487247206340), (Int.negOfNat 196479373004769607619177), (Int.ofNat 970302171424065256960), (Int.ofNat 949284472410412459648), (Int.negOfNat 9768456837828881953), (Int.negOfNat 3436692790211650947), (Int.ofNat 49796128862524654), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-936721278760742165801748702404527/1125899906842624000000000000000000), (14889185629664359171076412036351/450359962737049600000000000000000), (5470470172218454159374060958341/2251799813685248000000000000000000), (-1082459328789727827210410600087/1125899906842624000000000000000000), (-46214650851976530361200923333/281474976710656000000000000000000), (10371225418044386530951039647/225179981368524800000000000000000), (8934937078370578303258803007/2251799813685248000000000000000000), (-2438371379265053480973994163/2251799813685248000000000000000000), (-33772231603431744641719487/1125899906842624000000000000000000), (2800781018700261200150427/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial172.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial172.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial172.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 1722328316823053452653122214208776), (Int.ofNat 67431926010712810906373769744715), (Int.negOfNat 7585044290190924570370235216419), (Int.negOfNat 886149082136019807018433608174), (Int.ofNat 552208807753564297907584490132), (Int.ofNat 28106782202211338570626760791), (Int.negOfNat 16095085025052449926830774113), (Int.negOfNat 259551730281055990117184651), (Int.ofNat 246694775650503988348021455), (Int.negOfNat 1230331770426045007959820), (Int.negOfNat 2181258981854636341845535), (Int.ofNat 33436702399439337115450), (Int.ofNat 12647399129775667108841), (Int.negOfNat 260010086864530004828), (Int.negOfNat 52305807255926249365), (Int.ofNat 1212754967060601127), (Int.ofNat 175924761243496412), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-215291039602881681581640276776097/281474976710656000000000000000000), (13486385202142562181274753948943/450359962737049600000000000000000), (-7585044290190924570370235216419/2251799813685248000000000000000000), (-443074541068009903509216804087/1125899906842624000000000000000000), (138052201938391074476896122533/562949953421312000000000000000000), (28106782202211338570626760791/2251799813685248000000000000000000), (-16095085025052449926830774113/2251799813685248000000000000000000), (-259551730281055990117184651/2251799813685248000000000000000000), (49338955130100797669604291/450359962737049600000000000000000), (-61516588521302250397991/112589990684262400000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial172.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial172.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial172.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 1616161977060100905728388123756397), (Int.ofNat 43409929492489623999382299807947), (Int.negOfNat 1024607786912195785413365105047), (Int.ofNat 2339913486269406142334665966313), (Int.ofNat 39789088572294209372466008610), (Int.negOfNat 94250807836019991561273239010), (Int.ofNat 894399203880545700966919805), (Int.ofNat 1864767867725640173539720824), (Int.negOfNat 43072599074309334523822867), (Int.negOfNat 20974380568125956186278083), (Int.ofNat 646366557456017459751602), (Int.ofNat 148205459037818237647967), (Int.negOfNat 5169627922243010911363), (Int.negOfNat 720949034736311748930), (Int.ofNat 26675921596095015874), (Int.ofNat 2638885747874089627), (Int.negOfNat 112849968918605686), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-1616161977060100905728388123756397/2251799813685248000000000000000000), (43409929492489623999382299807947/2251799813685248000000000000000000), (-1024607786912195785413365105047/2251799813685248000000000000000000), (2339913486269406142334665966313/2251799813685248000000000000000000), (3978908857229420937246600861/225179981368524800000000000000000), (-9425080783601999156127323901/225179981368524800000000000000000), (178879840776109140193383961/450359962737049600000000000000000), (233095983465705021692465103/281474976710656000000000000000000), (-43072599074309334523822867/2251799813685248000000000000000000), (-20974380568125956186278083/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial172.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial172.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial172.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 1516825536563529555122283790395800), (Int.ofNat 62043172686259164178385270283855), (Int.ofNat 7734857342778608560423409417936), (Int.negOfNat 98957599331002625640053684533), (Int.negOfNat 445668138826813625490121421427), (Int.ofNat 20408552032175232886795824608), (Int.ofNat 12007099329465776850920480347), (Int.negOfNat 636637700551385815674741510), (Int.negOfNat 172433319679927028808984560), (Int.ofNat 9561908555861299941931119), (Int.ofNat 1502231102852786386025320), (Int.negOfNat 84932932538502800687574), (Int.negOfNat 8686814606004154473052), (Int.ofNat 494802640939759851811), (Int.ofNat 35778754038057618288), (Int.negOfNat 2041110146984274034), (Int.negOfNat 130098229425965246), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-7584127682817647775611418951979/11258999068426240000000000000000), (12408634537251832835677054056771/450359962737049600000000000000000), (483428583923663035026463088621/140737488355328000000000000000000), (-98957599331002625640053684533/2251799813685248000000000000000000), (-445668138826813625490121421427/2251799813685248000000000000000000), (637767251005476027712369519/70368744177664000000000000000000), (12007099329465776850920480347/2251799813685248000000000000000000), (-63663770055138581567474151/225179981368524800000000000000000), (-2155416495999087860112307/28147497671065600000000000000000), (9561908555861299941931119/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial172.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial172.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial172.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 1368419988345166957967415402767122), (Int.ofNat 81038574035563670174497963202471), (Int.ofNat 281121993128429514948389805464), (Int.negOfNat 1522261940305957240242107208556), (Int.ofNat 161726175250695613872124656914), (Int.ofNat 61957584534167094440922078330), (Int.negOfNat 6384337708106534796154600625), (Int.negOfNat 1178901937391509166487051434), (Int.ofNat 114480772019381106557876408), (Int.ofNat 12817748846488076649644113), (Int.negOfNat 1188485261752924119002832), (Int.negOfNat 88996303604312120975374), (Int.ofNat 8016552872549676673520), (Int.ofNat 426582988903915920793), (Int.negOfNat 37775490394974150184), (Int.negOfNat 1515369892555405710), (Int.ofNat 138346805534545826), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-684209994172583478983707701383561/1125899906842624000000000000000000), (81038574035563670174497963202471/2251799813685248000000000000000000), (35140249141053689368548725683/281474976710656000000000000000000), (-380565485076489310060526802139/562949953421312000000000000000000), (80863087625347806936062328457/1125899906842624000000000000000000), (6195758453416709444092207833/225179981368524800000000000000000), (-10214940332970455673847361/3602879701896396800000000000000), (-589450968695754583243525717/1125899906842624000000000000000000), (14310096502422638319734551/281474976710656000000000000000000), (12817748846488076649644113/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial172.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial172.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial172.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 1213351177214152581138098332378021), (Int.ofNat 72413710187389407742570898604687), (Int.negOfNat 2090266766167712387996376015316), (Int.ofNat 821212721276930382392936375368), (Int.ofNat 229446517709074460694488625423), (Int.negOfNat 47858521042685940512933878744), (Int.negOfNat 6226604140581408976957567331), (Int.ofNat 1119474111014238851495295052), (Int.ofNat 86825498857699661659357809), (Int.negOfNat 14235020549740060339604549), (Int.negOfNat 730175249857862036526010), (Int.ofNat 113731663814849965832473), (Int.ofNat 4072645670441044730193), (Int.negOfNat 621903973173472376174), (Int.negOfNat 16115239647203906318), (Int.ofNat 2484937512645378429), (Int.ofNat 71523279300464010), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-1213351177214152581138098332378021/2251799813685248000000000000000000), (72413710187389407742570898604687/2251799813685248000000000000000000), (-522566691541928096999094003829/562949953421312000000000000000000), (102651590159616297799117046921/281474976710656000000000000000000), (229446517709074460694488625423/2251799813685248000000000000000000), (-5982315130335742564116734843/281474976710656000000000000000000), (-6226604140581408976957567331/2251799813685248000000000000000000), (279868527753559712873823763/562949953421312000000000000000000), (86825498857699661659357809/2251799813685248000000000000000000), (-14235020549740060339604549/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial172.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial172.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial172.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 1068416224879302120359790066923805), (Int.ofNat 76780539200211487638254512019298), (Int.ofNat 3857905325983205724335113592305), (Int.ofNat 446014468741773661008302455236), (Int.negOfNat 274163848629882602354663821719), (Int.negOfNat 20668041892812043344887928654), (Int.ofNat 8930902491698043457866412635), (Int.ofNat 390384037092596913715397451), (Int.negOfNat 145076840798185274236868201), (Int.negOfNat 3985316221535972779607368), (Int.ofNat 1408536118365870783860121), (Int.ofNat 25072665525917313688382), (Int.negOfNat 9076401333173214891799), (Int.negOfNat 104827599741522976836), (Int.ofNat 41676874069996181619), (Int.ofNat 271951131050642049), (Int.negOfNat 134556167087735348), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-213683244975860424071958013384761/450359962737049600000000000000000), (38390269600105743819127256009649/1125899906842624000000000000000000), (771581065196641144867022718461/450359962737049600000000000000000), (111503617185443415252075613809/562949953421312000000000000000000), (-274163848629882602354663821719/2251799813685248000000000000000000), (-10334020946406021672443964327/1125899906842624000000000000000000), (1786180498339608691573282527/450359962737049600000000000000000), (390384037092596913715397451/2251799813685248000000000000000000), (-145076840798185274236868201/2251799813685248000000000000000000), (-498164527691996597450921/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial172.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial172.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial172.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 900319585244825623092062271835841), (Int.ofNat 88876802341713512847322627281933), (Int.ofNat 444346745701218264228354233727), (Int.negOfNat 1186189278582577279063261737136), (Int.ofNat 4606210621006224268942968227), (Int.ofNat 57453617623939671469972465060), (Int.ofNat 44708125244911782190450059), (Int.negOfNat 1243757263609696278270052857), (Int.ofNat 1397826903147108306428582), (Int.ofNat 15085521236137434481919486), (Int.negOfNat 51094931768309910836180), (Int.negOfNat 116632096955742803590239), (Int.ofNat 605370815983631578380), (Int.ofNat 623754381699786574700), (Int.negOfNat 4104740507362741965), (Int.negOfNat 2455791717243912349), (Int.negOfNat 8469439244382978), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-900319585244825623092062271835841/2251799813685248000000000000000000), (88876802341713512847322627281933/2251799813685248000000000000000000), (444346745701218264228354233727/2251799813685248000000000000000000), (-74136829911411079941453858571/140737488355328000000000000000000), (4606210621006224268942968227/2251799813685248000000000000000000), (2872680881196983573498623253/112589990684262400000000000000000), (44708125244911782190450059/2251799813685248000000000000000000), (-1243757263609696278270052857/2251799813685248000000000000000000), (698913451573554153214291/1125899906842624000000000000000000), (7542760618068717240959743/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial172.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial172.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial172.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 728514434391035195880214131812745), (Int.ofNat 80649646948481223535590248954627), (Int.negOfNat 2722742360157634540357652078824), (Int.ofNat 537591122804567183013882399936), (Int.ofNat 290644341452567475246318449076), (Int.negOfNat 19051889713893068626541807117), (Int.negOfNat 8806063657022259142876975833), (Int.ofNat 364347928947631955913066141), (Int.ofNat 137626595281551912525362843), (Int.negOfNat 4366427291261267770559083), (Int.negOfNat 1303439151323560168471136), (Int.ofNat 35152504269069913941018), (Int.ofNat 8260039851869904179778), (Int.negOfNat 199447941529712320511), (Int.negOfNat 37329115891703518785), (Int.ofNat 863123319830835736), (Int.ofNat 109747581955564526), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-145702886878207039176042826362549/450359962737049600000000000000000), (80649646948481223535590248954627/2251799813685248000000000000000000), (-340342795019704317544706509853/281474976710656000000000000000000), (8399861293821362234591912499/35184372088832000000000000000000), (72661085363141868811579612269/562949953421312000000000000000000), (-19051889713893068626541807117/2251799813685248000000000000000000), (-8806063657022259142876975833/2251799813685248000000000000000000), (364347928947631955913066141/2251799813685248000000000000000000), (137626595281551912525362843/2251799813685248000000000000000000), (-4366427291261267770559083/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial172.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial172.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial172.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 570249917810346746362526965185046), (Int.ofNat 82583482463343414917467212129035), (Int.ofNat 4298497931021441469192196502414), (Int.ofNat 1101198044791522647423292032089), (Int.negOfNat 204779484824639853600982792894), (Int.negOfNat 50000112480946979231838314870), (Int.ofNat 5333828768884649975010347154), (Int.ofNat 1044938009088652974727740558), (Int.negOfNat 78121695210696180532499320), (Int.negOfNat 12415960327855223826536507), (Int.ofNat 729759717031065025471192), (Int.ofNat 94810946086542929927349), (Int.negOfNat 4679708954891609124701), (Int.negOfNat 503491750745181519659), (Int.ofNat 21592940485086609294), (Int.ofNat 1989747931380458841), (Int.negOfNat 54584400811698054), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-285124958905173373181263482592523/1125899906842624000000000000000000), (16516696492668682983493442425807/450359962737049600000000000000000), (2149248965510720734596098251207/1125899906842624000000000000000000), (1101198044791522647423292032089/2251799813685248000000000000000000), (-102389742412319926800491396447/1125899906842624000000000000000000), (-5000011248094697923183831487/225179981368524800000000000000000), (2666914384442324987505173577/1125899906842624000000000000000000), (522469004544326487363870279/1125899906842624000000000000000000), (-1953042380267404513312483/56294995342131200000000000000000), (-12415960327855223826536507/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial172.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial172.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial172.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 383506172606761107418568481033205), (Int.ofNat 103827188013476863076843313800936), (Int.ofNat 3786769624759113809385465493497), (Int.negOfNat 1290647910939946558236779471732), (Int.negOfNat 216663134319570040760473851528), (Int.ofNat 49826884894482604297121347661), (Int.ofNat 6357130193389867530075596414), (Int.negOfNat 953405732685399588700805703), (Int.negOfNat 97422752662949382293095438), (Int.ofNat 10919788944816749789979560), (Int.ofNat 913918675147703045420679), (Int.negOfNat 82676760290218166841422), (Int.negOfNat 5773028147294128691610), (Int.ofNat 441400823608375806008), (Int.ofNat 26172288439620337996), (Int.negOfNat 1790771309793787353), (Int.negOfNat 84938996823393704), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-76701234521352221483713696206641/450359962737049600000000000000000), (12978398501684607884605414225117/281474976710656000000000000000000), (3786769624759113809385465493497/2251799813685248000000000000000000), (-322661977734986639559194867933/562949953421312000000000000000000), (-27082891789946255095059231441/281474976710656000000000000000000), (49826884894482604297121347661/2251799813685248000000000000000000), (3178565096694933765037798207/1125899906842624000000000000000000), (-953405732685399588700805703/2251799813685248000000000000000000), (-48711376331474691146547719/1125899906842624000000000000000000), (272994723620418744749489/56294995342131200000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial172.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial172.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial172.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 172635833227592145580940517127484), (Int.ofNat 101261895752550383195578852112287), (Int.negOfNat 4402234237147408729169984522192), (Int.negOfNat 653480303794192005976178312998), (Int.ofNat 339237276166926354325512854157), (Int.ofNat 28901532891308686633782239470), (Int.negOfNat 8944689526164899678488060141), (Int.negOfNat 588502403784317758937228470), (Int.ofNat 130337585626589253176092965), (Int.ofNat 6923921492479119315863834), (Int.negOfNat 1197934701449111520979289), (Int.negOfNat 52942447368974816080302), (Int.ofNat 7524995156248851849522), (Int.ofNat 283329588638163623378), (Int.negOfNat 34179599735912937799), (Int.negOfNat 1153755963429928624), (Int.ofNat 109368712490388812), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-43158958306898036395235129281871/562949953421312000000000000000000), (101261895752550383195578852112287/2251799813685248000000000000000000), (-275139639821713045573124032637/140737488355328000000000000000000), (-326740151897096002988089156499/1125899906842624000000000000000000), (339237276166926354325512854157/2251799813685248000000000000000000), (2890153289130868663378223947/225179981368524800000000000000000), (-8944689526164899678488060141/2251799813685248000000000000000000), (-58850240378431775893722847/225179981368524800000000000000000), (26067517125317850635218593/450359962737049600000000000000000), (3461960746239559657931917/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial172.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial172.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial172.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 12791644846041948094343062241286), (Int.ofNat 87140765687449739621133911140586), (Int.negOfNat 160778209049933268045142875266), (Int.ofNat 1706822548258752958325604476673), (Int.ofNat 83369444675907912204569858169), (Int.negOfNat 65925769287653913604593229721), (Int.negOfNat 2261676545129314880116261659), (Int.ofNat 1270102370607230047362295066), (Int.ofNat 33648765006045348858775755), (Int.negOfNat 14559390089921317217270502), (Int.negOfNat 317746771345176364988887), (Int.ofNat 109821479936490828196274), (Int.ofNat 2062165456303645559318), (Int.negOfNat 582847700492208245590), (Int.negOfNat 9682139875716356825), (Int.ofNat 2303075317230438208), (Int.ofNat 26364046697892468), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(6395822423020974047171531120643/1125899906842624000000000000000000), (43570382843724869810566955570293/1125899906842624000000000000000000), (-80389104524966634022571437633/1125899906842624000000000000000000), (1706822548258752958325604476673/2251799813685248000000000000000000), (83369444675907912204569858169/2251799813685248000000000000000000), (-65925769287653913604593229721/2251799813685248000000000000000000), (-2261676545129314880116261659/2251799813685248000000000000000000), (635051185303615023681147533/1125899906842624000000000000000000), (6729753001209069771755151/450359962737049600000000000000000), (-7279695044960658608635251/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial172.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial172.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial172.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 199327818880610415370160196861200), (Int.ofNat 104508588857410680696258248496587), (Int.ofNat 7110354346903223244198006863675), (Int.ofNat 67980720319363602207560768962), (Int.negOfNat 376564116503718081036956346284), (Int.ofNat 44799580414544210061433430), (Int.ofNat 10052938972051171965108268730), (Int.negOfNat 25416930888976671099892103), (Int.negOfNat 148272931595119107840614138), (Int.ofNat 326624424368128715489136), (Int.ofNat 1373856954662598774390913), (Int.negOfNat 1561788430907464896726), (Int.negOfNat 8670919203887912831206), (Int.ofNat 240920749753907000), (Int.ofNat 39390587338861453028), (Int.ofNat 80711189042316191), (Int.negOfNat 134865549106328952), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(498319547201526038425400492153/5629499534213120000000000000000), (104508588857410680696258248496587/2251799813685248000000000000000000), (284414173876128929767920274547/90071992547409920000000000000000), (33990360159681801103780384481/1125899906842624000000000000000000), (-94141029125929520259239086571/562949953421312000000000000000000), (4479958041454421006143343/225179981368524800000000000000000), (1005293897205117196510826873/225179981368524800000000000000000), (-25416930888976671099892103/2251799813685248000000000000000000), (-74136465797559553920307069/1125899906842624000000000000000000), (20414026523008044718071/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial172.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial172.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial172.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 431910380310384094290263144004042), (Int.ofNat 123493813611271828683669620576249), (Int.ofNat 630920329674468700335931300215), (Int.negOfNat 1592363962040513080463296688413), (Int.ofNat 72534215578042400782563343387), (Int.ofNat 62970223069538259138789841928), (Int.negOfNat 2580308838293869384904365682), (Int.negOfNat 1243219050529755021935144210), (Int.ofNat 41350091422438150046565784), (Int.ofNat 14549297984550340382790301), (Int.negOfNat 379857294169306474768008), (Int.negOfNat 111583385005665699031491), (Int.ofNat 2257958817215696098757), (Int.ofNat 599364944985195240773), (Int.negOfNat 9410954680307949990), (Int.negOfNat 2379857837172640271), (Int.ofNat 44959321735578838), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(215955190155192047145131572002021/1125899906842624000000000000000000), (123493813611271828683669620576249/2251799813685248000000000000000000), (126184065934893740067186260043/450359962737049600000000000000000), (-1592363962040513080463296688413/2251799813685248000000000000000000), (72534215578042400782563343387/2251799813685248000000000000000000), (7871277883692282392348730241/281474976710656000000000000000000), (-1290154419146934692452182841/1125899906842624000000000000000000), (-124321905052975502193514421/225179981368524800000000000000000), (5168761427804768755820723/281474976710656000000000000000000), (14549297984550340382790301/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial172.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial172.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial172.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 671551531237478144894688517924853), (Int.ofNat 113288206808878896977828167141776), (Int.negOfNat 3465674440521392883720643230917), (Int.ofNat 539853805878001529646806414347), (Int.ofNat 294962581282645282850141128853), (Int.negOfNat 30520187032108154566042419060), (Int.negOfNat 8250686262599982830291830929), (Int.ofNat 674996246936500657259719901), (Int.ofNat 126567243696784873458911245), (Int.negOfNat 8041087094901068975077475), (Int.negOfNat 1213954799240376489751536), (Int.ofNat 59680513160569183267122), (Int.ofNat 7879345849840504781566), (Int.negOfNat 302125811302666905231), (Int.negOfNat 36579713092582914391), (Int.ofNat 1093435489530766592), (Int.ofNat 110056963974158130), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(671551531237478144894688517924853/2251799813685248000000000000000000), (7080512925554931061114260446361/140737488355328000000000000000000), (-3465674440521392883720643230917/2251799813685248000000000000000000), (539853805878001529646806414347/2251799813685248000000000000000000), (294962581282645282850141128853/2251799813685248000000000000000000), (-1526009351605407728302120953/112589990684262400000000000000000), (-8250686262599982830291830929/2251799813685248000000000000000000), (674996246936500657259719901/2251799813685248000000000000000000), (25313448739356974691782249/450359962737049600000000000000000), (-321643483796042759003099/90071992547409920000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial172.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial172.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial172.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 891912381013230957393672078763550), (Int.ofNat 111724917600938025719875197662349), (Int.ofNat 3062291004286470695473573832104), (Int.ofNat 904863673670173139326652988777), (Int.negOfNat 219888120051393575018342140758), (Int.negOfNat 39695915138103760809534356576), (Int.ofNat 7149887634227580736413965653), (Int.ofNat 844816940706051633670114599), (Int.negOfNat 113691038103184363366580214), (Int.negOfNat 10607270477396256126603770), (Int.ofNat 1062782751243386366705940), (Int.ofNat 86335811305072323577369), (Int.negOfNat 6509533260394949872196), (Int.negOfNat 484983288531345263564), (Int.ofNat 28138687860586359557), (Int.ofNat 1985870671787505283), (Int.negOfNat 108013161791659870), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(17838247620264619147873441575271/45035996273704960000000000000000), (111724917600938025719875197662349/2251799813685248000000000000000000), (382786375535808836934196729013/281474976710656000000000000000000), (904863673670173139326652988777/2251799813685248000000000000000000), (-109944060025696787509171070379/1125899906842624000000000000000000), (-1240497348065742525297948643/70368744177664000000000000000000), (7149887634227580736413965653/2251799813685248000000000000000000), (844816940706051633670114599/2251799813685248000000000000000000), (-56845519051592181683290107/1125899906842624000000000000000000), (-1060727047739625612660377/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial172.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial172.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial172.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 1130594238953049939010540027332672), (Int.ofNat 126236982079147624851967556300587), (Int.ofNat 2083731369220397558314057866020), (Int.negOfNat 1066637333006777714935148821298), (Int.negOfNat 104445971603926456170132565011), (Int.ofNat 55086846039767483567107490570), (Int.ofNat 3497525818297898616217739805), (Int.negOfNat 1228820699740890233621604205), (Int.negOfNat 64213215275289231807267279), (Int.ofNat 14909265387580861289074024), (Int.ofNat 716133917237302449647295), (Int.negOfNat 112433473288165598777002), (Int.negOfNat 5182211784798229734265), (Int.ofNat 576631476222170799684), (Int.ofNat 25917933779425760701), (Int.negOfNat 2144227493926764583), (Int.negOfNat 85248378841987308), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(17665534983641405297039687927073/35184372088832000000000000000000), (126236982079147624851967556300587/2251799813685248000000000000000000), (104186568461019877915702893301/112589990684262400000000000000000), (-533318666503388857467574410649/1125899906842624000000000000000000), (-104445971603926456170132565011/2251799813685248000000000000000000), (5508684603976748356710749057/225179981368524800000000000000000), (699505163659579723243547961/450359962737049600000000000000000), (-245764139948178046724320841/450359962737049600000000000000000), (-64213215275289231807267279/2251799813685248000000000000000000), (1863658173447607661134253/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial172.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial172.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial172.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 1383019907918580257644825379493123), (Int.ofNat 122928851951130156953839776740450), (Int.negOfNat 2443744503123858425669410084570), (Int.ofNat 143666119624195234097277981370), (Int.ofNat 304849610993222521126094555238), (Int.negOfNat 2739866034578709473408864648), (Int.negOfNat 10300831844062279051851202381), (Int.negOfNat 76054678707863052231203364), (Int.ofNat 170328841875157069895840303), (Int.ofNat 2846904757508528025882171), (Int.negOfNat 1629227900026746752107230), (Int.negOfNat 36074915220080264039271), (Int.ofNat 10077316189711585741543), (Int.ofNat 252678207132577331154), (Int.negOfNat 43788420800330624930), (Int.negOfNat 1188063629449943963), (Int.ofNat 171067001847740902), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(1383019907918580257644825379493123/2251799813685248000000000000000000), (2458577039022603139076795534809/45035996273704960000000000000000), (-244374450312385842566941008457/225179981368524800000000000000000), (14366611962419523409727798137/225179981368524800000000000000000), (152424805496611260563047277619/1125899906842624000000000000000000), (-342483254322338684176108081/281474976710656000000000000000000), (-10300831844062279051851202381/2251799813685248000000000000000000), (-19013669676965763057800841/562949953421312000000000000000000), (170328841875157069895840303/2251799813685248000000000000000000), (2846904757508528025882171/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial172.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial172.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial172.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 1624416254777772016743458439505449), (Int.ofNat 122574517313384611575665528967566), (Int.ofNat 3291412823605860803052160537785), (Int.ofNat 1077305082008302411204559844616), (Int.negOfNat 181745455823841210584321982968), (Int.negOfNat 63838837229568186972512528435), (Int.ofNat 4232805420670526307520329081), (Int.ofNat 1567491334429838057277724214), (Int.negOfNat 37969950164057908375351312), (Int.negOfNat 20004975859138410814114815), (Int.ofNat 80140010368623953886312), (Int.ofNat 152944925505215024415642), (Int.ofNat 902130581869428845584), (Int.negOfNat 786359578760470255303), (Int.negOfNat 8789002129844449136), (Int.ofNat 2972582673850437490), (Int.ofNat 39421847024456142), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(1624416254777772016743458439505449/2251799813685248000000000000000000), (61287258656692305787832764483783/1125899906842624000000000000000000), (658282564721172160610432107557/450359962737049600000000000000000), (134663135251037801400569980577/281474976710656000000000000000000), (-22718181977980151323040247871/281474976710656000000000000000000), (-12767767445913637394502505687/450359962737049600000000000000000), (4232805420670526307520329081/2251799813685248000000000000000000), (783745667214919028638862107/1125899906842624000000000000000000), (-2373121885253619273459457/140737488355328000000000000000000), (-4000995171827682162822963/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial172.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial172.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial172.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 1886850579354436676050129752034053), (Int.ofNat 139176943202856318266272140603014), (Int.ofNat 2200412580356450890342898815005), (Int.negOfNat 1543195260514900093842350676029), (Int.negOfNat 243091060433121469844395129861), (Int.ofNat 66284620676150025343343759571), (Int.ofNat 10893651338316520063862592933), (Int.negOfNat 1098695862426994085704718662), (Int.negOfNat 206221465288863520471790616), (Int.ofNat 8224662934328569067474591), (Int.ofNat 2025744620603564447359200), (Int.negOfNat 33123312304024703721358), (Int.negOfNat 12531267054454515702852), (Int.ofNat 64665030577063272675), (Int.ofNat 54164892247493307912), (Int.ofNat 64547774131260046), (Int.negOfNat 196563838463681042), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(1886850579354436676050129752034053/2251799813685248000000000000000000), (69588471601428159133136070301507/1125899906842624000000000000000000), (440082516071290178068579763001/450359962737049600000000000000000), (-1543195260514900093842350676029/2251799813685248000000000000000000), (-243091060433121469844395129861/2251799813685248000000000000000000), (66284620676150025343343759571/2251799813685248000000000000000000), (10893651338316520063862592933/2251799813685248000000000000000000), (-549347931213497042852359331/1125899906842624000000000000000000), (-25777683161107940058973827/281474976710656000000000000000000), (8224662934328569067474591/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial172.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial172.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial172.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 2160402140444756818316051470566968), (Int.ofNat 128400950592662923669139952569414), (Int.negOfNat 6024084551461705892926896835893), (Int.negOfNat 5794027284251852778713333274), (Int.ofNat 592250204328471821204805818253), (Int.ofNat 43073035197222966608857470077), (Int.negOfNat 16427550280676008292128865053), (Int.negOfNat 1731652486303676628561574312), (Int.ofNat 176050430297707880011367235), (Int.ofNat 23378384773163965798646157), (Int.negOfNat 1076441494148138706563882), (Int.negOfNat 177989614094991705540577), (Int.ofNat 4327325020237313061067), (Int.ofNat 905768114022711490238), (Int.negOfNat 12135561331983820306), (Int.negOfNat 3416410039511541885), (Int.ofNat 19153103101045094), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(270050267555594602289506433820871/281474976710656000000000000000000), (64200475296331461834569976284707/1125899906842624000000000000000000), (-6024084551461705892926896835893/2251799813685248000000000000000000), (-2897013642125926389356666637/1125899906842624000000000000000000), (592250204328471821204805818253/2251799813685248000000000000000000), (43073035197222966608857470077/2251799813685248000000000000000000), (-16427550280676008292128865053/2251799813685248000000000000000000), (-216456560787959578570196789/281474976710656000000000000000000), (35210086059541576002273447/450359962737049600000000000000000), (23378384773163965798646157/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial172.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial172.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial172.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 2402698273546035327588928868853263), (Int.ofNat 122929838998801973564586234413155), (Int.ofNat 6900943419885504205180285438344), (Int.ofNat 3274845241138551766103048343956), (Int.negOfNat 177224318066859382214436634997), (Int.negOfNat 186743487795512944734439458346), (Int.negOfNat 11053727040018182785327535527), (Int.ofNat 2677044444105195643859916413), (Int.ofNat 234812038703753496645960185), (Int.negOfNat 21095343279037497896101068), (Int.negOfNat 2260495076893254704382441), (Int.ofNat 110091483175745180474706), (Int.ofNat 13656200753391330840263), (Int.negOfNat 415835714123533995988), (Int.negOfNat 58271325069689818075), (Int.ofNat 1178870987373503615), (Int.ofNat 192773200016870564), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(2402698273546035327588928868853263/2251799813685248000000000000000000), (24585967799760394712917246882631/450359962737049600000000000000000), (862617927485688025647535679793/281474976710656000000000000000000), (818711310284637941525762085989/562949953421312000000000000000000), (-177224318066859382214436634997/2251799813685248000000000000000000), (-93371743897756472367219729173/1125899906842624000000000000000000), (-11053727040018182785327535527/2251799813685248000000000000000000), (2677044444105195643859916413/2251799813685248000000000000000000), (46962407740750699329192037/450359962737049600000000000000000), (-5273835819759374474025267/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial172.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial172.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial172.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 2693231603025601731210679517490592), (Int.ofNat 168479916070020685752919901225201), (Int.ofNat 6804702899875882657109773279433), (Int.negOfNat 5603460458640386814312538219819), (Int.negOfNat 1804584793278710271138434774990), (Int.negOfNat 45629328936756141128888336482), (Int.ofNat 33256100837274793391116289087), (Int.ofNat 2085369126714278916033401533), (Int.negOfNat 325077914820308892074795074), (Int.negOfNat 25906606451812104741475866), (Int.ofNat 2082316863594462062169260), (Int.ofNat 186964433370849170258671), (Int.negOfNat 9584084133546170946984), (Int.negOfNat 921623032326422484056), (Int.ofNat 33478785375257810601), (Int.ofNat 3387264244110075805), (Int.negOfNat 82206943157126126), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(84163487594550054100333734921581/70368744177664000000000000000000), (168479916070020685752919901225201/2251799813685248000000000000000000), (6804702899875882657109773279433/2251799813685248000000000000000000), (-5603460458640386814312538219819/2251799813685248000000000000000000), (-180458479327871027113843477499/225179981368524800000000000000000), (-22814664468378070564444168241/1125899906842624000000000000000000), (33256100837274793391116289087/2251799813685248000000000000000000), (2085369126714278916033401533/2251799813685248000000000000000000), (-162538957410154446037397537/1125899906842624000000000000000000), (-12953303225906052370737933/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial172.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial172.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial172.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 2984550370491345786928976040707865), (Int.ofNat 73999478011774641331535355709082), (Int.negOfNat 65067052822764668455509283024760), (Int.negOfNat 16059779675586385851537702936795), (Int.negOfNat 115776727087019835024025860669), (Int.ofNat 351840550938046464762309747898), (Int.ofNat 17658112625955887555554912149), (Int.negOfNat 4184836739416816977162689921), (Int.negOfNat 274866010915506120811826871), (Int.ofNat 32491025204119470016379735), (Int.ofNat 2347125653308182682242568), (Int.negOfNat 179114332582168647476330), (Int.negOfNat 13353635329975576998270), (Int.ofNat 739109921283097022603), (Int.ofNat 55053445285009875101), (Int.negOfNat 2313945438254981400), (Int.negOfNat 167964614884699742), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(596910074098269157385795208141573/450359962737049600000000000000000), (36999739005887320665767677854541/1125899906842624000000000000000000), (-1626676320569116711387732075619/56294995342131200000000000000000), (-3211955935117277170307540587359/450359962737049600000000000000000), (-115776727087019835024025860669/2251799813685248000000000000000000), (175920275469023232381154873949/1125899906842624000000000000000000), (17658112625955887555554912149/2251799813685248000000000000000000), (-4184836739416816977162689921/2251799813685248000000000000000000), (-274866010915506120811826871/2251799813685248000000000000000000), (6498205040823894003275947/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial172.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial172.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial172.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 2753752066430128724033995139590454), (Int.negOfNat 353225036721301517887798693740860), (Int.negOfNat 134953003983682217215689906731784), (Int.negOfNat 2721235883771940524148239331808), (Int.ofNat 3136121753486307676005293409612), (Int.ofNat 167142258106750881346383932780), (Int.negOfNat 45234643206696477120301124970), (Int.negOfNat 2834323520081555461462022598), (Int.ofNat 428852074088613254668137528), (Int.ofNat 27542462103581345371065151), (Int.negOfNat 2843188274341979940652440), (Int.negOfNat 178365361553622962619397), (Int.ofNat 13848930855417853408557), (Int.ofNat 830304089085690880707), (Int.negOfNat 51424424097521765110), (Int.negOfNat 2921220458246622297), (Int.ofNat 145260783213207158), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(1376876033215064362016997569795227/1125899906842624000000000000000000), (-17661251836065075894389934687043/112589990684262400000000000000000), (-16869125497960277151961238341473/281474976710656000000000000000000), (-85038621367873141379632479119/70368744177664000000000000000000), (784030438371576919001323352403/562949953421312000000000000000000), (8357112905337544067319196639/112589990684262400000000000000000), (-4523464320669647712030112497/225179981368524800000000000000000), (-1417161760040777730731011299/1125899906842624000000000000000000), (53606509261076656833517191/281474976710656000000000000000000), (27542462103581345371065151/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial172.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial172.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial172.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 1538109453477029655533973821836877), (Int.negOfNat 821433020768704484910084347629935), (Int.negOfNat 74544406780525450277463839149527), (Int.ofNat 21095790174040407749413962583782), (Int.ofNat 1847473380189683946502515113680), (Int.negOfNat 392689328839096839033837847735), (Int.negOfNat 29609535057846331385406994254), (Int.ofNat 4737980434290569680331162867), (Int.ofNat 309565552495084030008605218), (Int.negOfNat 38659774090137357463910000), (Int.negOfNat 2223519250614491515346443), (Int.ofNat 225132993060667202932086), (Int.ofNat 11539224784037105184118), (Int.negOfNat 977053015524739988808), (Int.negOfNat 45154349651448562860), (Int.ofNat 3241593428217933017), (Int.ofNat 143156029752528920), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(1538109453477029655533973821836877/2251799813685248000000000000000000), (-164286604153740896982016869525987/450359962737049600000000000000000), (-74544406780525450277463839149527/2251799813685248000000000000000000), (10547895087020203874706981291891/1125899906842624000000000000000000), (23093417252371049331281438921/28147497671065600000000000000000), (-78537865767819367806767569547/450359962737049600000000000000000), (-14804767528923165692703497127/1125899906842624000000000000000000), (4737980434290569680331162867/2251799813685248000000000000000000), (154782776247542015004302609/1125899906842624000000000000000000), (-3865977409013735746391/225179981368524800000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial172.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial172.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial172.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 218405249174134186481014630617912), (Int.negOfNat 842100277691735630936100990849235), (Int.ofNat 61390115591197425203218859463196), (Int.ofNat 18406997043424878753595762154543), (Int.negOfNat 2357826408539150933540797006162), (Int.negOfNat 299727128923038264254940547670), (Int.ofNat 41713890582146724672189169587), (Int.ofNat 3349488246425030167878332342), (Int.negOfNat 443855103812205838895790357), (Int.negOfNat 26169438035643583921175146), (Int.ofNat 3178432057569499152869625), (Int.ofNat 148718132237262287906794), (Int.negOfNat 16356765877896077704806), (Int.negOfNat 636605571887560421230), (Int.ofNat 63409204916635413127), (Int.ofNat 2085228490296092080), (Int.negOfNat 200045094891897916), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-27300656146766773310126828827239/281474976710656000000000000000000), (-168420055538347126187220198169847/450359962737049600000000000000000), (15347528897799356300804714865799/562949953421312000000000000000000), (18406997043424878753595762154543/2251799813685248000000000000000000), (-1178913204269575466770398503081/1125899906842624000000000000000000), (-29972712892303826425494054767/225179981368524800000000000000000), (41713890582146724672189169587/2251799813685248000000000000000000), (1674744123212515083939166171/1125899906842624000000000000000000), (-443855103812205838895790357/2251799813685248000000000000000000), (-13084719017821791960587573/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial172.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial172.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial172.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial172.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial172.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial172.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial172.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial172.reflect := by
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

end Bin172
end
end ErdosOverlap.OuterNumerics
