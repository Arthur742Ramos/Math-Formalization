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

/-! # Exact integer weighted outer models for source bin 140

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin140

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 3188969204600229000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 3020391391495171300)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 2216961770155533300)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 1168813444639533300)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 608457448598471900)⟩, ⟨(19494472361809/1000000000000), (Int.negOfNat 439494900868372200)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 691086469733463200)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 336171953802492400)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 521168492819220500)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 132073534366729060)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial140.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial140.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9736894521525766000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1765348345655414800)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1593790306583951800)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 599290092971379200)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 151190710986038170)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 28249570476721070)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 14300895080734302)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 83059460112897970)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 18302632214292787)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial140.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial140.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9736894521525766000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1765348345655414800)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1593790306583951800)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 599290092971379200)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 151190710986038170)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 28249570476721070)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 14300895080734302)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 83059460112897970)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 18302632214292787)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial140.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial140.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial140.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 10352307953555448054149878299421575), (Int.ofNat 4660129562381071994848144726407797), (Int.ofNat 1013862583043346299640775615988082), (Int.negOfNat 155145497890852169247017258913083), (Int.negOfNat 28945232274551551925595644626537), (Int.ofNat 3232563942278756103576324057581), (Int.ofNat 444137385322162456298113958111), (Int.negOfNat 40314606688650743846272507557), (Int.negOfNat 4191633745040315962335178710), (Int.ofNat 326676483477223894275107394), (Int.ofNat 26632408445653788119468713), (Int.negOfNat 1853255518592603105742864), (Int.negOfNat 121854488399697059481481), (Int.ofNat 7784368923609631649477), (Int.ofNat 421260888983753261531), (Int.negOfNat 24999374800171297011), (Int.negOfNat 1154779831480007048), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-414092318142217922165995131976863/450359962737049600000000000000000), (4660129562381071994848144726407797/11258999068426240000000000000000000), (506931291521673149820387807994041/5629499534213120000000000000000000), (-155145497890852169247017258913083/11258999068426240000000000000000000), (-28945232274551551925595644626537/11258999068426240000000000000000000), (3232563942278756103576324057581/11258999068426240000000000000000000), (444137385322162456298113958111/11258999068426240000000000000000000), (-40314606688650743846272507557/11258999068426240000000000000000000), (-419163374504031596233517871/1125899906842624000000000000000000), (163338241738611947137553697/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial140.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial140.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial140.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial140 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 1444937619932882404272236674839357), (Int.ofNat 6249978410657482617935161367973000), (Int.negOfNat 279347629723046656118544807247957), (Int.negOfNat 214354581892562205708137328985753), (Int.ofNat 15630511455046227998196614557875), (Int.ofNat 4107038331472181972990115863494), (Int.negOfNat 313361100619474494374326622913), (Int.negOfNat 46652240614779037985294394187), (Int.ofNat 3449028516203432908249437267), (Int.ofNat 343924754721637956181426965), (Int.negOfNat 24568877983072496042850554), (Int.negOfNat 1772718882926869314152231), (Int.ofNat 123784698582355529181411), (Int.ofNat 6762629583485931293233), (Int.negOfNat 467055762326352765902), (Int.negOfNat 19578686751810570549), (Int.ofNat 1435834302130597098), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(1444937619932882404272236674839357/11258999068426240000000000000000000), (6249978410657482617935161367973/11258999068426240000000000000000), (-279347629723046656118544807247957/11258999068426240000000000000000000), (-214354581892562205708137328985753/11258999068426240000000000000000000), (125044091640369823985572916463/90071992547409920000000000000000), (2053519165736090986495057931747/5629499534213120000000000000000000), (-313361100619474494374326622913/11258999068426240000000000000000000), (-46652240614779037985294394187/11258999068426240000000000000000000), (3449028516203432908249437267/11258999068426240000000000000000000), (68784950944327591236285393/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial140.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial140.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial140.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial140 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 11469184885793565725102925976778520), (Int.ofNat 3312188598844876486351936749596523), (Int.negOfNat 960894980469413165923763345853824), (Int.ofNat 6300898363284180008844123088889), (Int.ofNat 29698770983677041205994577746078), (Int.negOfNat 1569854832220625470385637074838), (Int.negOfNat 449435363468694232695583934204), (Int.ofNat 28762053166676643095737119953), (Int.ofNat 4034991908716801534247033922), (Int.negOfNat 276300760996379076090824521), (Int.negOfNat 24027769086681377826897758), (Int.ofNat 1727899090028549397476409), (Int.ofNat 102148425561538919196982), (Int.negOfNat 7728126398925146926012), (Int.negOfNat 326259302337186517465), (Int.ofNat 26081560805062873007), (Int.ofNat 740256596165527081), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(286729622144839143127573149419463/281474976710656000000000000000000), (3312188598844876486351936749596523/11258999068426240000000000000000000), (-7506992034917290358779401139483/87960930222080000000000000000000), (6300898363284180008844123088889/11258999068426240000000000000000000), (14849385491838520602997288873039/5629499534213120000000000000000000), (-784927416110312735192818537419/5629499534213120000000000000000000), (-112358840867173558173895983551/2814749767106560000000000000000000), (28762053166676643095737119953/11258999068426240000000000000000000), (2017495954358400767123516961/5629499534213120000000000000000000), (-276300760996379076090824521/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial140.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial140.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial140.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial140 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 14701122786047250849017950529339717), (Int.ofNat 298979296116173450773145237221108), (Int.negOfNat 418708920308116180202000902766840), (Int.ofNat 130752247981228874699242040910344), (Int.negOfNat 1747466687676347415200733243561), (Int.negOfNat 3431521905148989403924483962526), (Int.ofNat 168454181600406411460252703787), (Int.ofNat 41234245882369752242589063452), (Int.negOfNat 2531336957800447074660272284), (Int.negOfNat 297166979152029539285351748), (Int.ofNat 20785157948493903323271169), (Int.ofNat 1443275384434134675098697), (Int.negOfNat 113464373518500125158006), (Int.negOfNat 5061178035658787029084), (Int.ofNat 449691580833141544264), (Int.ofNat 12686169655178991442), (Int.negOfNat 1380926405487718737), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(14701122786047250849017950529339717/11258999068426240000000000000000000), (74744824029043362693286309305277/2814749767106560000000000000000000), (-10467723007702904505050022569171/281474976710656000000000000000000), (16344030997653609337405255113793/1407374883553280000000000000000000), (-1747466687676347415200733243561/11258999068426240000000000000000000), (-1715760952574494701962241981263/5629499534213120000000000000000000), (168454181600406411460252703787/11258999068426240000000000000000000), (10308561470592438060647265863/2814749767106560000000000000000000), (-632834239450111768665068071/2814749767106560000000000000000000), (-74291744788007384821337937/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial140.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial140.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial140.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial140 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 14547778133602146989529395915529475), (Int.negOfNat 89611039310156536867440756795962), (Int.ofNat 111848317371063006342282887859443), (Int.ofNat 23788074380580945309252679754272), (Int.negOfNat 18118547269675333923844083101542), (Int.ofNat 518083071024428935188694274029), (Int.ofNat 346250136330278457098734019562), (Int.negOfNat 17705100293582412448773083016), (Int.negOfNat 3248180466861418488058082622), (Int.ofNat 209479099673520791448480934), (Int.ofNat 18763483571892846287752407), (Int.negOfNat 1455412420789467188238611), (Int.negOfNat 73759556103563180316527), (Int.ofNat 6914244817983782417541), (Int.ofNat 208079468774134539942), (Int.negOfNat 24762933178217337783), (Int.negOfNat 344035993065339901), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(581911125344085879581175836621179/450359962737049600000000000000000), (-44805519655078268433720378397981/5629499534213120000000000000000000), (111848317371063006342282887859443/11258999068426240000000000000000000), (743377324393154540914146242321/351843720888320000000000000000000), (-9059273634837666961922041550771/5629499534213120000000000000000000), (518083071024428935188694274029/11258999068426240000000000000000000), (173125068165139228549367009781/5629499534213120000000000000000000), (-2213137536697801556096635377/1407374883553280000000000000000000), (-1624090233430709244029041311/5629499534213120000000000000000000), (104739549836760395724240467/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial140.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial140.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial140.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial140 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 14752121286682810552503977423041209), (Int.ofNat 160675148493066193045213786022194), (Int.negOfNat 72303633079381413858877308127524), (Int.negOfNat 59425839455641864692399674388239), (Int.ofNat 270553455673448175854696718489), (Int.ofNat 2256193410951026710905038176673), (Int.negOfNat 85866252117403450501861271105), (Int.negOfNat 30242383745000513249646217806), (Int.ofNat 1698738076281086997734927593), (Int.ofNat 219188656295255846867633012), (Int.negOfNat 15961166074183495457623563), (Int.negOfNat 1000064402146560845386361), (Int.ofNat 93842336644147817722026), (Int.ofNat 3063353813336850216232), (Int.negOfNat 388199107593685934129), (Int.negOfNat 6231730087902302355), (Int.ofNat 1326018508844840376), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(14752121286682810552503977423041209/11258999068426240000000000000000000), (80337574246533096522606893011097/5629499534213120000000000000000000), (-18075908269845353464719327031881/2814749767106560000000000000000000), (-59425839455641864692399674388239/11258999068426240000000000000000000), (270553455673448175854696718489/11258999068426240000000000000000000), (2256193410951026710905038176673/11258999068426240000000000000000000), (-17173250423480690100372254221/2251799813685248000000000000000000), (-15121191872500256624823108903/5629499534213120000000000000000000), (1698738076281086997734927593/11258999068426240000000000000000000), (54797164073813961716908253/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial140.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial140.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial140.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial140 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 14376540027057468049462298092403772), (Int.negOfNat 680377225615828620952211976257023), (Int.negOfNat 278951886917480662558541831459132), (Int.ofNat 6258252147945105281709974287512), (Int.ofNat 11754846340938644106057592775070), (Int.negOfNat 259807250884218701609581919096), (Int.negOfNat 234202905910787846947109611389), (Int.ofNat 10438487722599543119930051160), (Int.ofNat 2244597316149240965824723245), (Int.negOfNat 144981570109064544746040878), (Int.negOfNat 12396336384830226506843246), (Int.ofNat 1102910785727062363712162), (Int.ofNat 42528172384750692749665), (Int.negOfNat 5516613068685058672441), (Int.negOfNat 86639613088343953305), (Int.ofNat 20063773273794942333), (Int.negOfNat 52184610034847279), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(3594135006764367012365574523100943/2814749767106560000000000000000000), (-680377225615828620952211976257023/11258999068426240000000000000000000), (-69737971729370165639635457864783/2814749767106560000000000000000000), (782281518493138160213746785939/1407374883553280000000000000000000), (1175484634093864410605759277507/1125899906842624000000000000000000), (-32475906360527337701197739887/1407374883553280000000000000000000), (-234202905910787846947109611389/11258999068426240000000000000000000), (260962193064988577998251279/281474976710656000000000000000000), (448919463229848193164944649/2251799813685248000000000000000000), (-72490785054532272373020439/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial140.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial140.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial140.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial140 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 12116644974708271447302117874648096), (Int.negOfNat 1404091629720679290990488190858365), (Int.negOfNat 26020202505410748084366859155915), (Int.ofNat 61380044447590701972705111278903), (Int.negOfNat 159924901527276371666702042206), (Int.negOfNat 1545000601540481734322690930050), (Int.ofNat 41843429057627608970280169261), (Int.ofNat 19863403825133030122310892761), (Int.negOfNat 1031742812970831266274611469), (Int.negOfNat 137970585182268901387256243), (Int.ofNat 10892549216172399096160473), (Int.ofNat 551471121222941735722279), (Int.negOfNat 68269587577678782752512), (Int.negOfNat 1156207445710549818253), (Int.ofNat 291406179642021269370), (Int.negOfNat 427646006226604632), (Int.negOfNat 1139037077835232955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(378645155459633482728191183582753/351843720888320000000000000000000), (-280818325944135858198097638171673/2251799813685248000000000000000000), (-5204040501082149616873371831183/2251799813685248000000000000000000), (61380044447590701972705111278903/11258999068426240000000000000000000), (-79962450763638185833351021103/5629499534213120000000000000000000), (-30900012030809634686453818601/225179981368524800000000000000000), (41843429057627608970280169261/11258999068426240000000000000000000), (19863403825133030122310892761/11258999068426240000000000000000000), (-1031742812970831266274611469/11258999068426240000000000000000000), (-137970585182268901387256243/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial140.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial140.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial140.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial140 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 9648320170204977487643456447946363), (Int.negOfNat 884710921645212993513165647670725), (Int.ofNat 235864117213068318037865546170428), (Int.ofNat 13711251737479095527837214909785), (Int.negOfNat 9088513177307687842912741140201), (Int.negOfNat 17590054622563187555920155153), (Int.ofNat 152337675469156957464324772761), (Int.negOfNat 4877683869202783882311150001), (Int.negOfNat 1361661069179312169092046069), (Int.ofNat 85275375467877593940458383), (Int.ofNat 6601745458326285396670233), (Int.negOfNat 712049664974643280865099), (Int.negOfNat 14970834285116618038872), (Int.ofNat 3730056644938990341813), (Int.negOfNat 14731722358755662670), (Int.negOfNat 14249402556953300928), (Int.ofNat 279726414339719825), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(9648320170204977487643456447946363/11258999068426240000000000000000000), (-35388436865808519740526625906829/450359962737049600000000000000000), (58966029303267079509466386542607/2814749767106560000000000000000000), (2742250347495819105567442981957/2251799813685248000000000000000000), (-9088513177307687842912741140201/11258999068426240000000000000000000), (-17590054622563187555920155153/11258999068426240000000000000000000), (152337675469156957464324772761/11258999068426240000000000000000000), (-4877683869202783882311150001/11258999068426240000000000000000000), (-1361661069179312169092046069/11258999068426240000000000000000000), (85275375467877593940458383/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial140.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial140.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial140.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial140 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 8794891331006558501987787076163872), (Int.negOfNat 43067686952117642564879470955483), (Int.ofNat 129891766000012331581954408035525), (Int.negOfNat 39968890194483311897809426949626), (Int.negOfNat 2613066951477771920156064685536), (Int.ofNat 994467134833837604580875930156), (Int.ofNat 394340186159579767919271471), (Int.negOfNat 11803332287472483665115180060), (Int.ofNat 443822804223838808820670305), (Int.ofNat 72197831929485414413369158), (Int.negOfNat 5833347624017598105808146), (Int.negOfNat 192064396725389263985142), (Int.ofNat 39572655957038811101985), (Int.negOfNat 308399191011773021059), (Int.negOfNat 174965684185393469705), (Int.ofNat 4873125618723585907), (Int.ofNat 838284744673189261), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(274840354093954953187118346130121/351843720888320000000000000000000), (-43067686952117642564879470955483/11258999068426240000000000000000000), (5195670640000493263278176321421/450359962737049600000000000000000), (-19984445097241655948904713474813/5629499534213120000000000000000000), (-81658342233680372504877021423/351843720888320000000000000000000), (248616783708459401145218982539/2814749767106560000000000000000000), (394340186159579767919271471/11258999068426240000000000000000000), (-590166614373624183255759003/562949953421312000000000000000000), (88764560844767761764134061/2251799813685248000000000000000000), (36098915964742707206684579/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial140.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial140.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial140.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial140 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 8897244561999804989468293204700743), (Int.negOfNat 11810530780261819881119543936832), (Int.negOfNat 99857034348525320842196800466559), (Int.negOfNat 26551511121243205678989955659738), (Int.ofNat 4756741429119871253219122621773), (Int.ofNat 303133467649237097045781610869), (Int.negOfNat 86912680067665350431577182565), (Int.negOfNat 16993030686075600305814894), (Int.ofNat 712382779768992308008665953), (Int.negOfNat 29631493972533471429947672), (Int.negOfNat 2440901368450600600005163), (Int.ofNat 312979892639701797334741), (Int.negOfNat 3903716897398825591914), (Int.negOfNat 1764742356092190727172), (Int.ofNat 80455102823938221551), (Int.ofNat 6367324688468730795), (Int.negOfNat 356892052063570524), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(8897244561999804989468293204700743/11258999068426240000000000000000000), (-184539543441590935642492874013/175921860444160000000000000000000), (-99857034348525320842196800466559/11258999068426240000000000000000000), (-13275755560621602839494977829869/5629499534213120000000000000000000), (4756741429119871253219122621773/11258999068426240000000000000000000), (303133467649237097045781610869/11258999068426240000000000000000000), (-17382536013533070086315436513/2251799813685248000000000000000000), (-8496515343037800152907447/5629499534213120000000000000000000), (712382779768992308008665953/11258999068426240000000000000000000), (-3703936746566683928743459/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial140.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial140.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial140.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial140 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 8342192132487405544733745612145892), (Int.negOfNat 569433188310961428080507624575480), (Int.negOfNat 140503860747045674718434057258631), (Int.ofNat 10804346356604157116756982291386), (Int.ofNat 3226322528430415872848293359191), (Int.negOfNat 493144063271427707434082523292), (Int.negOfNat 31394331147311424810680162338), (Int.ofNat 6173978184982451326211723316), (Int.ofNat 68450821017408390909987978), (Int.negOfNat 30105385900734727973642474), (Int.ofNat 1048647895988104035777447), (Int.negOfNat 20957869085946244037029), (Int.negOfNat 10637729953774913833007), (Int.ofNat 1091012719596769002459), (Int.ofNat 51431095041489691042), (Int.negOfNat 7405850347914210257), (Int.negOfNat 442064141573002081), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(2085548033121851386183436403036473/2814749767106560000000000000000000), (-14235829707774035702012690614387/281474976710656000000000000000000), (-140503860747045674718434057258631/11258999068426240000000000000000000), (5402173178302078558378491145693/5629499534213120000000000000000000), (3226322528430415872848293359191/11258999068426240000000000000000000), (-123286015817856926858520630823/2814749767106560000000000000000000), (-15697165573655712405340081169/5629499534213120000000000000000000), (1543494546245612831552930829/2814749767106560000000000000000000), (34225410508704195454993989/5629499534213120000000000000000000), (-15052692950367363986821237/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial140.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial140.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial140.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial140 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 6762369772501801060755957852156647), (Int.negOfNat 941261783846447896300056853345334), (Int.negOfNat 41088396176541689139452322492261), (Int.ofNat 15298684522298064916713240186474), (Int.negOfNat 1892491391587770950421009834363), (Int.negOfNat 374140072967017964460298209014), (Int.ofNat 45322270938054853942245509040), (Int.ofNat 3690953760103242646492112328), (Int.negOfNat 347752578246585755279089264), (Int.negOfNat 19005695503801669023808872), (Int.ofNat 408303022122572554143969), (Int.ofNat 59031879406441093410363), (Int.ofNat 11423507650934381932134), (Int.negOfNat 147059343281920324816), (Int.negOfNat 98902410570275044956), (Int.ofNat 913883318394402358), (Int.ofNat 301984155420692163), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(6762369772501801060755957852156647/11258999068426240000000000000000000), (-470630891923223948150028426672667/5629499534213120000000000000000000), (-41088396176541689139452322492261/11258999068426240000000000000000000), (7649342261149032458356620093237/5629499534213120000000000000000000), (-1892491391587770950421009834363/11258999068426240000000000000000000), (-187070036483508982230149104507/5629499534213120000000000000000000), (566528386725685674278068863/140737488355328000000000000000000), (461369220012905330811514041/1407374883553280000000000000000000), (-21734536140411609704943079/703687441776640000000000000000000), (-2375711937975208627976109/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial140.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial140.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial140.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial140 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 4798904646522424401642195670243214), (Int.negOfNat 1002563531827249529204303490855074), (Int.negOfNat 11993294468411391395207181026400), (Int.negOfNat 6203761819987040904880821828154), (Int.negOfNat 2337925060164712003183240792656), (Int.ofNat 291709883562297616222912668441), (Int.ofNat 48091877581400797728481353556), (Int.negOfNat 3673129006437912837288747453), (Int.negOfNat 471265004757310667107669678), (Int.ofNat 14996934469846877782146701), (Int.ofNat 3059734991824319263299102), (Int.ofNat 66245400714803030540991), (Int.negOfNat 15340986215813752369838), (Int.negOfNat 1098328393625943627368), (Int.ofNat 63244419712886055575), (Int.ofNat 6717681277407415833), (Int.ofNat 45843538472814901), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(2399452323261212200821097835121607/5629499534213120000000000000000000), (-501281765913624764602151745427537/5629499534213120000000000000000000), (-14991618085514239244008976283/14073748835532800000000000000000), (-3101880909993520452440410914077/5629499534213120000000000000000000), (-146120316260294500198952549541/703687441776640000000000000000000), (291709883562297616222912668441/11258999068426240000000000000000000), (12022969395350199432120338389/2814749767106560000000000000000000), (-3673129006437912837288747453/11258999068426240000000000000000000), (-235632502378655333553834839/5629499534213120000000000000000000), (14996934469846877782146701/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial140.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial140.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial140.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial140 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 2670600178223031901103603915133530), (Int.negOfNat 1169302621269578620602820218792705), (Int.negOfNat 73655039219676685432697385949837), (Int.negOfNat 8317098019850438229769443473738), (Int.ofNat 2010517145377949953048170176523), (Int.ofNat 404174468696550149297101618608), (Int.negOfNat 35861010610781931855512566713), (Int.negOfNat 6239276829044674157191205773), (Int.ofNat 286691065417948939881768347), (Int.ofNat 56892915142678144729159115), (Int.negOfNat 568837410745829433269254), (Int.negOfNat 364210784494386238841109), (Int.negOfNat 7231229569779890453149), (Int.ofNat 1767040868153781548727), (Int.ofNat 70785722868087634978), (Int.negOfNat 7228719658435729251), (Int.negOfNat 247076258777813802), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(267060017822303190110360391513353/1125899906842624000000000000000000), (-233860524253915724120564043758541/2251799813685248000000000000000000), (-73655039219676685432697385949837/11258999068426240000000000000000000), (-4158549009925219114884721736869/5629499534213120000000000000000000), (2010517145377949953048170176523/11258999068426240000000000000000000), (25260904293534384331068851163/703687441776640000000000000000000), (-35861010610781931855512566713/11258999068426240000000000000000000), (-6239276829044674157191205773/11258999068426240000000000000000000), (286691065417948939881768347/11258999068426240000000000000000000), (11378583028535628945831823/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial140.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial140.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial140.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial140 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.ofNat 12947299334879922482100771584736), (Int.negOfNat 1476320397544188520624246736473040), (Int.negOfNat 55011777430364490632288732827928), (Int.ofNat 15497488435595500233354445285889), (Int.ofNat 2680843010809334227019093035312), (Int.negOfNat 322580440680896813366357212602), (Int.negOfNat 60169527847230469592230560669), (Int.ofNat 4100651327411351473830291717), (Int.ofNat 750407451762393200209575110), (Int.negOfNat 25074133321821011422847514), (Int.negOfNat 6070074067007103088056547), (Int.ofNat 45429240161263153957284), (Int.ofNat 35121083715164668630559), (Int.ofNat 376809551863415744963), (Int.negOfNat 151964693927663067269), (Int.negOfNat 3586879364836942429), (Int.ofNat 332074432413079492), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(404603104214997577565649112023/351843720888320000000000000000000), (-18454004969302356507803084205913/140737488355328000000000000000000), (-6876472178795561329036091603491/1407374883553280000000000000000000), (15497488435595500233354445285889/11258999068426240000000000000000000), (167552688175583389188693314707/703687441776640000000000000000000), (-161290220340448406683178606301/5629499534213120000000000000000000), (-60169527847230469592230560669/11258999068426240000000000000000000), (4100651327411351473830291717/11258999068426240000000000000000000), (75040745176239320020957511/1125899906842624000000000000000000), (-12537066660910505711423757/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial140.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial140.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial140.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial140 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 3006342462339914085792657313751224), (Int.negOfNat 1459451618057939252335493869201926), (Int.ofNat 65984816631332426614966972402901), (Int.ofNat 17832817730360362912193626350605), (Int.negOfNat 2342830102032571594269700657911), (Int.negOfNat 458610795238948598763496399941), (Int.ofNat 46749316518925220275807133609), (Int.ofNat 7770939552276441497919859657), (Int.negOfNat 470297713988979045145073510), (Int.negOfNat 80438716025136927225139514), (Int.ofNat 2571577420745795856212587), (Int.ofNat 564169787829787438846804), (Int.negOfNat 6924121627596955043519), (Int.negOfNat 2872468531389144702057), (Int.negOfNat 2435215531927993791), (Int.ofNat 11652229661173960851), (Int.negOfNat 53676074384229892), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-375792807792489260724082164218903/1407374883553280000000000000000000), (-729725809028969626167746934600963/5629499534213120000000000000000000), (65984816631332426614966972402901/11258999068426240000000000000000000), (3566563546072072582438725270121/2251799813685248000000000000000000), (-2342830102032571594269700657911/11258999068426240000000000000000000), (-458610795238948598763496399941/11258999068426240000000000000000000), (46749316518925220275807133609/11258999068426240000000000000000000), (7770939552276441497919859657/11258999068426240000000000000000000), (-47029771398897904514507351/1125899906842624000000000000000000), (-40219358012568463612569757/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial140.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial140.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial140.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial140 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 5566975924336865947323162757270429), (Int.negOfNat 1081368430996398286391748810820987), (Int.ofNat 95338002638157150648661559983927), (Int.negOfNat 8636122401178543255301545234823), (Int.negOfNat 2742686133321340699256813418580), (Int.ofNat 418084045493292138713714525206), (Int.ofNat 64781668315988557080781192073), (Int.negOfNat 6363271574397442790728103793), (Int.negOfNat 875155681584102008067396827), (Int.ofNat 53398843594574394795967815), (Int.ofNat 7577519596110744624457754), (Int.negOfNat 275824779862005017960989), (Int.negOfNat 45859638477473732095351), (Int.ofNat 907338598242656813807), (Int.ofNat 204646018966654631182), (Int.negOfNat 1101295557227190091), (Int.negOfNat 559616236717952038), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-5566975924336865947323162757270429/11258999068426240000000000000000000), (-1081368430996398286391748810820987/11258999068426240000000000000000000), (95338002638157150648661559983927/11258999068426240000000000000000000), (-8636122401178543255301545234823/11258999068426240000000000000000000), (-137134306666067034962840670929/562949953421312000000000000000000), (209042022746646069356857262603/5629499534213120000000000000000000), (64781668315988557080781192073/11258999068426240000000000000000000), (-6363271574397442790728103793/11258999068426240000000000000000000), (-875155681584102008067396827/11258999068426240000000000000000000), (10679768718914878959193563/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial140.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial140.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial140.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial140 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 7444812197975201984544345773817649), (Int.negOfNat 849120281819546098044119929864269), (Int.ofNat 21169434051814743862916023246079), (Int.negOfNat 8233835859025149853854928156504), (Int.ofNat 2863379294966982600227300908147), (Int.ofNat 425328814545742859246799734768), (Int.negOfNat 67420581716964051161104762436), (Int.negOfNat 7837992991509723018118730113), (Int.ofNat 795658798290934232460221378), (Int.ofNat 85490653932207777855612481), (Int.negOfNat 5752758338518003307280302), (Int.negOfNat 626103161676113339524569), (Int.ofNat 27719039742181465844978), (Int.ofNat 3287198052787960138112), (Int.negOfNat 94203969102973844015), (Int.negOfNat 13070587619868029247), (Int.ofNat 468199309698709859), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-7444812197975201984544345773817649/11258999068426240000000000000000000), (-849120281819546098044119929864269/11258999068426240000000000000000000), (21169434051814743862916023246079/11258999068426240000000000000000000), (-1029229482378143731731866019563/1407374883553280000000000000000000), (2863379294966982600227300908147/11258999068426240000000000000000000), (26583050909108928702924983423/703687441776640000000000000000000), (-16855145429241012790276190609/2814749767106560000000000000000000), (-7837992991509723018118730113/11258999068426240000000000000000000), (397829399145467116230110689/5629499534213120000000000000000000), (85490653932207777855612481/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial140.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial140.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial140.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial140 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 9069898876529870663925297160880137), (Int.negOfNat 753074244921115221050162381580317), (Int.ofNat 54803967723947923028622806491091), (Int.ofNat 18284383417342469323230488762366), (Int.ofNat 2013452760111608823843529595331), (Int.negOfNat 574448210846669426906063751282), (Int.negOfNat 56915891654703890914404137307), (Int.ofNat 9377778057565522098452098108), (Int.ofNat 799977475374678432002566504), (Int.negOfNat 90504509653377248415900092), (Int.negOfNat 7225008269159376982954929), (Int.ofNat 569503571365629400045363), (Int.ofNat 45481051026293325435626), (Int.negOfNat 2499296822601341740716), (Int.negOfNat 208731355441324810084), (Int.ofNat 7657640700056276798), (Int.ofNat 504708340075073677), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-9069898876529870663925297160880137/11258999068426240000000000000000000), (-753074244921115221050162381580317/11258999068426240000000000000000000), (54803967723947923028622806491091/11258999068426240000000000000000000), (9142191708671234661615244381183/5629499534213120000000000000000000), (2013452760111608823843529595331/11258999068426240000000000000000000), (-287224105423334713453031875641/5629499534213120000000000000000000), (-56915891654703890914404137307/11258999068426240000000000000000000), (2344444514391380524613024527/2814749767106560000000000000000000), (99997184421834804000320813/1407374883553280000000000000000000), (-22626127413344312103975023/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial140.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial140.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial140.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial140 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 10199013401630139864861744639301196), (Int.negOfNat 302116707729673378340931535229786), (Int.ofNat 160471255465445621485820390187191), (Int.ofNat 8423430750880629464736734745188), (Int.negOfNat 4057530740455383638258358605460), (Int.negOfNat 331592205459900549842740706506), (Int.ofNat 89301025191751528795964595498), (Int.ofNat 6019212528723610267145340896), (Int.negOfNat 1152019127666823643217810898), (Int.negOfNat 68165287543946278358600214), (Int.ofNat 9323659303599368178681313), (Int.ofNat 527436455882598655012951), (Int.negOfNat 51028107390483912456573), (Int.negOfNat 2909384285617384366601), (Int.ofNat 199860037950416172238), (Int.ofNat 12088131946824986423), (Int.negOfNat 864419912798897039), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-2549753350407534966215436159825299/2814749767106560000000000000000000), (-151058353864836689170465767614893/5629499534213120000000000000000000), (160471255465445621485820390187191/11258999068426240000000000000000000), (2105857687720157366184183686297/2814749767106560000000000000000000), (-202876537022769181912917930273/562949953421312000000000000000000), (-165796102729950274921370353253/5629499534213120000000000000000000), (44650512595875764397982297749/5629499534213120000000000000000000), (188100391522612820848291903/351843720888320000000000000000000), (-576009563833411821608905449/5629499534213120000000000000000000), (-34082643771973139179300107/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial140.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial140.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial140.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial140 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 10163339485952102882110240892506537), (Int.ofNat 303039101375296590523027444024542), (Int.ofNat 110320789942843062077759788955210), (Int.negOfNat 21913396483542970520833474963864), (Int.negOfNat 1754824774613415850526907323118), (Int.ofNat 676993379157500487280462295442), (Int.ofNat 34383913124602565920648040405), (Int.negOfNat 12002690563392942637100386574), (Int.negOfNat 482564484537328364823132533), (Int.ofNat 126823681921949221564827648), (Int.ofNat 4769766204408373566843683), (Int.negOfNat 867757550944575561062579), (Int.negOfNat 33054710486424875979586), (Int.ofNat 4120803555920337943228), (Int.ofNat 163920717368421275049), (Int.negOfNat 13775908313530473485), (Int.negOfNat 449800443432195316), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-10163339485952102882110240892506537/11258999068426240000000000000000000), (151519550687648295261513722012271/5629499534213120000000000000000000), (11032078994284306207775978895521/1125899906842624000000000000000000), (-2739174560442871315104184370483/1407374883553280000000000000000000), (-877412387306707925263453661559/5629499534213120000000000000000000), (338496689578750243640231147721/5629499534213120000000000000000000), (6876782624920513184129608081/2251799813685248000000000000000000), (-6001345281696471318550193287/5629499534213120000000000000000000), (-482564484537328364823132533/11258999068426240000000000000000000), (61925625938451768342201/5497558138880000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial140.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial140.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial140.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial140 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 9297090072679939286043525311786232), (Int.ofNat 480403211385465328632336950673321), (Int.negOfNat 9180950568713643444115579612904), (Int.negOfNat 10241105592680404537847152624938), (Int.ofNat 3713166612190871311921916090906), (Int.ofNat 131793467090563468440703670673), (Int.negOfNat 100242469900347598559739081091), (Int.negOfNat 1803537352196103587301145120), (Int.ofNat 1439465466531714332707859635), (Int.ofNat 25549754482204237969233118), (Int.negOfNat 12576720242534928833103634), (Int.negOfNat 261060294848707852917042), (Int.ofNat 72893288803215616036415), (Int.ofNat 1741041221130828145761), (Int.negOfNat 300040493784693269415), (Int.negOfNat 8164638897073455573), (Int.ofNat 1260640515899084219), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-1162136259084992410755440663973279/1407374883553280000000000000000000), (480403211385465328632336950673321/11258999068426240000000000000000000), (-1147618821089205430514447451613/1407374883553280000000000000000000), (-5120552796340202268923576312469/5629499534213120000000000000000000), (1856583306095435655960958045453/5629499534213120000000000000000000), (131793467090563468440703670673/11258999068426240000000000000000000), (-100242469900347598559739081091/11258999068426240000000000000000000), (-11272108451225647420632157/70368744177664000000000000000000), (287893093306342866541571927/2251799813685248000000000000000000), (12774877241102118984616559/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial140.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial140.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial140.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial140 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 8397586131884611905473750977476257), (Int.ofNat 431563806223212837799714314618770), (Int.ofNat 6311830098738186672542515220226), (Int.ofNat 10208348652857442294390302579792), (Int.ofNat 56274340275054796407299601541), (Int.negOfNat 627722069015905632295938181588), (Int.ofNat 11230348093744171104133712259), (Int.ofNat 13354495602745105920502268179), (Int.negOfNat 120998044893574649453109411), (Int.negOfNat 155527884830954011032078557), (Int.negOfNat 152449365266408416521553), (Int.ofNat 1123937630101293886878281), (Int.ofNat 9191641883714264140332), (Int.negOfNat 5528400319293304928827), (Int.negOfNat 72351881255581356330), (Int.ofNat 19762940500054395672), (Int.ofNat 262819012422587895), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-8397586131884611905473750977476257/11258999068426240000000000000000000), (43156380622321283779971431461877/1125899906842624000000000000000000), (3155915049369093336271257610113/5629499534213120000000000000000000), (638021790803590143399393911237/703687441776640000000000000000000), (56274340275054796407299601541/11258999068426240000000000000000000), (-156930517253976408073984545397/2814749767106560000000000000000000), (11230348093744171104133712259/11258999068426240000000000000000000), (13354495602745105920502268179/11258999068426240000000000000000000), (-120998044893574649453109411/11258999068426240000000000000000000), (-155527884830954011032078557/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial140.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial140.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial140.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial140 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 7444411477100189368988730479952652), (Int.ofNat 538562934075583696520382367546203), (Int.ofNat 29460366513969376717405109328171), (Int.negOfNat 6183379195124567366166412665250), (Int.negOfNat 2525923572268287646546913501534), (Int.ofNat 292169970614020108585954286485), (Int.ofNat 95556312084118824074122954759), (Int.negOfNat 5562080789999883667650108259), (Int.negOfNat 1616465225567589871401598051), (Int.ofNat 43453802974327922239710217), (Int.ofNat 15122677631536580882781147), (Int.negOfNat 157508126164875680492241), (Int.negOfNat 90428474092656519558448), (Int.ofNat 96949616893263377207), (Int.ofNat 378656525061630655430), (Int.ofNat 2350268180231814168), (Int.negOfNat 1488182320203956765), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-1861102869275047342247182619988163/2814749767106560000000000000000000), (538562934075583696520382367546203/11258999068426240000000000000000000), (29460366513969376717405109328171/11258999068426240000000000000000000), (-24733516780498269464665650661/45035996273704960000000000000000), (-1262961786134143823273456750767/5629499534213120000000000000000000), (58433994122804021717190857297/2251799813685248000000000000000000), (95556312084118824074122954759/11258999068426240000000000000000000), (-5562080789999883667650108259/11258999068426240000000000000000000), (-1616465225567589871401598051/11258999068426240000000000000000000), (43453802974327922239710217/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial140.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial140.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial140.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial140 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 6324949624020535969711012208813000), (Int.ofNat 539121230122447748703149180492391), (Int.negOfNat 28225328194397622639506134855782), (Int.negOfNat 4977067739314943916002319428532), (Int.ofNat 3122094102424593150519025930930), (Int.ofNat 443597929206453706221567285989), (Int.negOfNat 90712137478524661494259599591), (Int.negOfNat 13600570233666143066801975500), (Int.ofNat 1038150621828520983494490815), (Int.ofNat 176355762958566634628241382), (Int.negOfNat 6348240181979493068374374), (Int.negOfNat 1316215042859937835122838), (Int.ofNat 23504341904547379456635), (Int.ofNat 6551265383734502460379), (Int.negOfNat 51808494673756762375), (Int.negOfNat 24208420112551376947), (Int.ofNat 37933320739455799), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-6324949624020535969711012208813/11258999068426240000000000000000), (539121230122447748703149180492391/11258999068426240000000000000000000), (-14112664097198811319753067427891/5629499534213120000000000000000000), (-1244266934828735979000579857133/2814749767106560000000000000000000), (312209410242459315051902593093/1125899906842624000000000000000000), (443597929206453706221567285989/11258999068426240000000000000000000), (-90712137478524661494259599591/11258999068426240000000000000000000), (-27201140467332286133603951/22517998136852480000000000000000), (207630124365704196698898163/2251799813685248000000000000000000), (88177881479283317314120691/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial140.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial140.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial140.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial140 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 5342475816074156550239020374093445), (Int.ofNat 479803139970530562092254755770210), (Int.ofNat 23985274166646725891040379201753), (Int.ofNat 18273172957562348332502767379815), (Int.ofNat 45321221045376509498664032481), (Int.negOfNat 1052464732274376068877914780639), (Int.negOfNat 84395547522872852109126395335), (Int.ofNat 16615687365895486097573215314), (Int.ofNat 1759748443845823372993212087), (Int.negOfNat 134352376668913559643471868), (Int.negOfNat 17045391947079452802446157), (Int.ofNat 678386377870505864439219), (Int.ofNat 102220817852436905658674), (Int.negOfNat 2349446549255837066568), (Int.negOfNat 428033919319939484271), (Int.ofNat 5971304589121128165), (Int.ofNat 1565347957927807464), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-1068495163214831310047804074818689/2251799813685248000000000000000000), (47980313997053056209225475577021/1125899906842624000000000000000000), (23985274166646725891040379201753/11258999068426240000000000000000000), (3654634591512469666500553475963/2251799813685248000000000000000000), (45321221045376509498664032481/11258999068426240000000000000000000), (-1052464732274376068877914780639/11258999068426240000000000000000000), (-16879109504574570421825279067/2251799813685248000000000000000000), (8307843682947743048786607657/5629499534213120000000000000000000), (1759748443845823372993212087/11258999068426240000000000000000000), (-33588094167228389910867967/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial140.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial140.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial140.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial140 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 4176605260006980676430910123678682), (Int.ofNat 704930438998822000239362951612642), (Int.ofNat 43789148202356823213195614053055), (Int.negOfNat 25452796922019506939567632777996), (Int.negOfNat 9650211746654284950014983424511), (Int.negOfNat 260197042373744550470560550475), (Int.ofNat 213012940652076690602724072691), (Int.ofNat 14804813727855226371721179464), (Int.negOfNat 2191808858116262160410915558), (Int.negOfNat 196723923566247846349286906), (Int.ofNat 13820435399230223319141133), (Int.ofNat 1446196444595589485859069), (Int.negOfNat 60055501379438957879293), (Int.negOfNat 7089671236914442427019), (Int.ofNat 191982871485241168178), (Int.ofNat 25629306033268644297), (Int.negOfNat 434153923839642979), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-2088302630003490338215455061839341/5629499534213120000000000000000000), (352465219499411000119681475806321/5629499534213120000000000000000000), (8757829640471364642639122810611/2251799813685248000000000000000000), (-6363199230504876734891908194499/2814749767106560000000000000000000), (-9650211746654284950014983424511/11258999068426240000000000000000000), (-10407881694949782018822422019/450359962737049600000000000000000), (213012940652076690602724072691/11258999068426240000000000000000000), (1850601715981903296465147433/1407374883553280000000000000000000), (-1095904429058131080205457779/5629499534213120000000000000000000), (-98361961783123923174643453/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial140.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial140.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial140.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial140 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 2943057025440464799225314191587229), (Int.ofNat 289949531445058487949045706055915), (Int.negOfNat 304915926390914753343579651341135), (Int.negOfNat 75410200177154016485906609336802), (Int.ofNat 1662816332671406749336430034773), (Int.ofNat 2307090593290673509738191741846), (Int.ofNat 105514770579451107248569220540), (Int.negOfNat 29867484708266191161463064068), (Int.negOfNat 2048385751367799736923598556), (Int.ofNat 230375959879816528777196132), (Int.ofNat 18673633960394966926882291), (Int.negOfNat 1209132494862904087251403), (Int.negOfNat 107811259019394335691854), (Int.ofNat 4648210485374039875816), (Int.ofNat 440671263495024460776), (Int.negOfNat 13588684549786753718), (Int.negOfNat 1510440061284929103), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-2943057025440464799225314191587229/11258999068426240000000000000000000), (57989906289011697589809141211183/2251799813685248000000000000000000), (-60983185278182950668715930268227/2251799813685248000000000000000000), (-37705100088577008242953304668401/5629499534213120000000000000000000), (1662816332671406749336430034773/11258999068426240000000000000000000), (1153545296645336754869095870923/5629499534213120000000000000000000), (5275738528972555362428461027/562949953421312000000000000000000), (-7466871177066547790365766017/2814749767106560000000000000000000), (-512096437841949934230899639/2814749767106560000000000000000000), (57593989969954132194299033/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial140.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial140.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial140.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial140 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 4083131587540614842891321547474795), (Int.negOfNat 1591468130339113535637364039342010), (Int.negOfNat 530084150309921573439983693596554), (Int.ofNat 28125587952891830194198274046834), (Int.ofNat 21524740465428302296636066281571), (Int.ofNat 716993353879448167814255699556), (Int.negOfNat 347429882630139191184722342616), (Int.negOfNat 19983002287987815649944913707), (Int.ofNat 3270624260420422453063788278), (Int.ofNat 223395356427074283644573459), (Int.negOfNat 20597025525795083458637342), (Int.negOfNat 1515307617861569711845251), (Int.ofNat 93651830324283327769278), (Int.ofNat 7101674316112125238868), (Int.negOfNat 323107372399432377295), (Int.negOfNat 25044459909827729673), (Int.ofNat 830374526939830159), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-816626317508122968578264309494959/2251799813685248000000000000000000), (-159146813033911353563736403934201/1125899906842624000000000000000000), (-265042075154960786719991846798277/5629499534213120000000000000000000), (14062793976445915097099137023417/5629499534213120000000000000000000), (21524740465428302296636066281571/11258999068426240000000000000000000), (179248338469862041953563924889/2814749767106560000000000000000000), (-43428735328767398898090292827/1407374883553280000000000000000000), (-19983002287987815649944913707/11258999068426240000000000000000000), (1635312130210211226531894139/5629499534213120000000000000000000), (223395356427074283644573459/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial140.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial140.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial140.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial140 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 8817925548581306970251426716577158), (Int.negOfNat 2700061501358011842833761003413370), (Int.ofNat 122428607284652440599032322057807), (Int.ofNat 168917885015442687119997433895062), (Int.ofNat 6490713750059435282242584860922), (Int.negOfNat 3414595766888533843985164634565), (Int.negOfNat 195573608695385400119709871947), (Int.ofNat 39719053364283123680252655393), (Int.ofNat 2539430809691497151589541313), (Int.negOfNat 302815381713353860163942135), (Int.negOfNat 19921227841428728857650646), (Int.ofNat 1633098792903837307427489), (Int.ofNat 106505375709436083794089), (Int.negOfNat 6574611273699520648087), (Int.negOfNat 415816419311291536458), (Int.ofNat 20239692843630573011), (Int.ofNat 1455532164642050742), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-4408962774290653485125713358288579/5629499534213120000000000000000000), (-270006150135801184283376100341337/1125899906842624000000000000000000), (122428607284652440599032322057807/11258999068426240000000000000000000), (84458942507721343559998716947531/5629499534213120000000000000000000), (3245356875029717641121292430461/5629499534213120000000000000000000), (-682919153377706768797032926913/2251799813685248000000000000000000), (-195573608695385400119709871947/11258999068426240000000000000000000), (39719053364283123680252655393/11258999068426240000000000000000000), (2539430809691497151589541313/11258999068426240000000000000000000), (-60563076342670772032788427/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial140.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial140.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial140.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial140 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 12389360984317304880237309479845836), (Int.negOfNat 266731955947178631891242192712709), (Int.ofNat 1001276718766317522485328157673625), (Int.ofNat 77906178130703549305236380560723), (Int.negOfNat 26833144854749196756304075114362), (Int.negOfNat 2001969110581600882261830955608), (Int.ofNat 403221774351907813255526002236), (Int.ofNat 28077417563284417766325747483), (Int.negOfNat 3828272674660949303846164790), (Int.negOfNat 248341933959156683571233506), (Int.ofNat 24878017001563327350907147), (Int.ofNat 1499245766849928621825056), (Int.negOfNat 117653449285547227419159), (Int.negOfNat 6555579314008856630743), (Int.ofNat 423283276403005904829), (Int.ofNat 21577486043454763869), (Int.negOfNat 1208292497825724552), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-3097340246079326220059327369961459/2814749767106560000000000000000000), (-266731955947178631891242192712709/11258999068426240000000000000000000), (8010213750130540179882625261389/90071992547409920000000000000000), (77906178130703549305236380560723/11258999068426240000000000000000000), (-13416572427374598378152037557181/5629499534213120000000000000000000), (-250246138822700110282728869451/1407374883553280000000000000000000), (100805443587976953313881500559/2814749767106560000000000000000000), (28077417563284417766325747483/11258999068426240000000000000000000), (-382827267466094930384616479/1125899906842624000000000000000000), (-124170966979578341785616753/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial140.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial140.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial140.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial140.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial140 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial140 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial140 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 14910143268014752022576695500566305), (Int.ofNat 170658500281763173675750968294643), (Int.ofNat 1116462226340129412265482597150718), (Int.negOfNat 120876671356459579047570126198157), (Int.negOfNat 28927904532117799390507246408343), (Int.ofNat 3202221440539849700531413701059), (Int.ofNat 427898220586605187498108862849), (Int.negOfNat 42164691760206609276002599483), (Int.negOfNat 4019925731677749805823398090), (Int.ofNat 343275996543961999999888406), (Int.ofNat 25890148524930765097443247), (Int.negOfNat 1919759403452937847041256), (Int.negOfNat 121438641190231873857759), (Int.ofNat 7879355627404799719643), (Int.ofNat 433368435017080676829), (Int.negOfNat 24603033627677195469), (Int.negOfNat 1208292497825724552), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-2982028653602950404515339100113261/2251799813685248000000000000000000), (170658500281763173675750968294643/11258999068426240000000000000000000), (558231113170064706132741298575359/5629499534213120000000000000000000), (-120876671356459579047570126198157/11258999068426240000000000000000000), (-28927904532117799390507246408343/11258999068426240000000000000000000), (3202221440539849700531413701059/11258999068426240000000000000000000), (427898220586605187498108862849/11258999068426240000000000000000000), (-42164691760206609276002599483/11258999068426240000000000000000000), (-401992573167774980582339809/1125899906842624000000000000000000), (171637998271980999999944203/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial140.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial140.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial140.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 11409208904249841882431940817817357), (Int.ofNat 2576521711594373024375507152247320), (Int.ofNat 22086597495869599361883751718317), (Int.negOfNat 184412333911508268450019381126487), (Int.ofNat 14098597950742145214666374212165), (Int.ofNat 3828942851526752793820578930306), (Int.negOfNat 328537407984278724029310344247), (Int.negOfNat 44401942841197607373789993093), (Int.ofNat 3707710682589682252051202613), (Int.ofNat 333643770503458931826513435), (Int.negOfNat 26258880389450660074338046), (Int.negOfNat 1767576671961406333663889), (Int.ofNat 130066030916358586993389), (Int.ofNat 6994242299958561721087), (Int.negOfNat 480127095931279932458), (Int.negOfNat 21248208705038050211), (Int.ofNat 1455532164642050742), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-11409208904249841882431940817817357/11258999068426240000000000000000000), (64413042789859325609387678806183/281474976710656000000000000000000), (22086597495869599361883751718317/11258999068426240000000000000000000), (-184412333911508268450019381126487/11258999068426240000000000000000000), (2819719590148429042933274842433/2251799813685248000000000000000000), (1914471425763376396910289465153/5629499534213120000000000000000000), (-328537407984278724029310344247/11258999068426240000000000000000000), (-44401942841197607373789993093/11258999068426240000000000000000000), (3707710682589682252051202613/11258999068426240000000000000000000), (66728754100691786365302687/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial140.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial140.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial140.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 7320633794672901485409651865799640), (Int.ofNat 1130833969367881159085206685606477), (Int.negOfNat 540553626599962288834575750316416), (Int.ofNat 12079285968642326059555394702591), (Int.ofNat 25332045179808235360397253715482), (Int.negOfNat 1758659180655330714824247190962), (Int.negOfNat 416238069184988005878118649116), (Int.ofNat 32251878516632111372605676607), (Int.ofNat 3866720368090626724609019678), (Int.negOfNat 306860241878593978395248359), (Int.negOfNat 23763927183823634660619042), (Int.ofNat 1888271584872410353525751), (Int.ofNat 105192256570877614172178), (Int.negOfNat 8286252948197915165868), (Int.negOfNat 354059905758512998895), (Int.ofNat 27397663586445176473), (Int.ofNat 830374526939830159), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-183015844866822537135241296644991/281474976710656000000000000000000), (1130833969367881159085206685606477/11258999068426240000000000000000000), (-4223075207812205381520123049347/87960930222080000000000000000000), (12079285968642326059555394702591/11258999068426240000000000000000000), (12666022589904117680198626857741/5629499534213120000000000000000000), (-879329590327665357412123595481/5629499534213120000000000000000000), (-104059517296247001469529662279/2814749767106560000000000000000000), (32251878516632111372605676607/11258999068426240000000000000000000), (1933360184045313362304509839/5629499534213120000000000000000000), (-306860241878593978395248359/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial140.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial140.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial140.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 6797208782438709553858605552034317), (Int.negOfNat 278811037418219436890742732849908), (Int.negOfNat 73725192126206594241234020483600), (Int.ofNat 100855682872954261412074695663976), (Int.negOfNat 5334449111389998939782859122759), (Int.negOfNat 3058835734804579510271027842874), (Int.ofNat 214424772027503821213480270053), (Int.ofNat 38737861764229109511479794468), (Int.negOfNat 2993188666569635153762444756), (Int.negOfNat 289369044595416551421083932), (Int.ofNat 23846077857467530706244591), (Int.ofNat 1465894382802916645844703), (Int.negOfNat 127292130244341277446754), (Int.negOfNat 5443904760320436523716), (Int.ofNat 494509692825279418576), (Int.ofNat 14933372364996723318), (Int.negOfNat 1510440061284929103), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-6797208782438709553858605552034317/11258999068426240000000000000000000), (-69702759354554859222685683212477/2814749767106560000000000000000000), (-184312980315516485603085051209/28147497671065600000000000000000), (12606960359119282676509336957997/1407374883553280000000000000000000), (-5334449111389998939782859122759/11258999068426240000000000000000000), (-1529417867402289755135513921437/5629499534213120000000000000000000), (214424772027503821213480270053/11258999068426240000000000000000000), (9684465441057277377869948617/2814749767106560000000000000000000), (-748297166642408788440611189/2814749767106560000000000000000000), (-72342261148854137855270983/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial140.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial140.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial140.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 7008326010564559680308129192841795), (Int.ofNat 276074790310353782174307598165442), (Int.ofNat 229778557957797270423743214339317), (Int.negOfNat 14678962122606524508143044236112), (Int.negOfNat 16364999874868511589514178523858), (Int.ofNat 1065406753230144104986651869171), (Int.ofNat 320540431901938917649992442238), (Int.negOfNat 23780284296593639435787102264), (Int.negOfNat 3104161911417638614227946858), (Int.ofNat 258123816151164138340735106), (Int.ofNat 18650735700460519564319833), (Int.negOfNat 1726258806594760005921469), (Int.negOfNat 77669356125074960102593), (Int.ofNat 7999113078951354941819), (Int.ofNat 239252101408368331578), (Int.negOfNat 27982509709886091097), (Int.negOfNat 434153923839642979), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-1401665202112911936061625838568359/2251799813685248000000000000000000), (138037395155176891087153799082721/5629499534213120000000000000000000), (229778557957797270423743214339317/11258999068426240000000000000000000), (-917435132662907781758940264757/703687441776640000000000000000000), (-8182499937434255794757089261929/5629499534213120000000000000000000), (1065406753230144104986651869171/11258999068426240000000000000000000), (160270215950969458824996221119/5629499534213120000000000000000000), (-2972535537074204929473387783/1407374883553280000000000000000000), (-1552080955708819307113973429/5629499534213120000000000000000000), (129061908075582069170367553/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial140.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial140.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial140.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 5865417358444313324533614979180129), (Int.ofNat 628974856675198112736760511536046), (Int.negOfNat 109084204347495311514851539109076), (Int.negOfNat 68980888493111845516869879583601), (Int.ofNat 4598107883315794899968631202831), (Int.ofNat 2138337587380882962479721217727), (Int.negOfNat 152170481561140088391137688335), (Int.negOfNat 28519001578306106313605190114), (Int.ofNat 2357225647151186055404480887), (Int.ofNat 212330088962588557200653868), (Int.negOfNat 20443831306994795000202757), (Int.negOfNat 1018417080222492166901519), (Int.ofNat 115519002926237665674174), (Int.ofNat 3409270246348176266968), (Int.negOfNat 465711381258423486071), (Int.negOfNat 8324508265738574965), (Int.ofNat 1565347957927807464), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-5865417358444313324533614979180129/11258999068426240000000000000000000), (314487428337599056368380255768023/5629499534213120000000000000000000), (-27271051086873827878712884777269/2814749767106560000000000000000000), (-68980888493111845516869879583601/11258999068426240000000000000000000), (4598107883315794899968631202831/11258999068426240000000000000000000), (2138337587380882962479721217727/11258999068426240000000000000000000), (-30434096312228017678227537667/2251799813685248000000000000000000), (-14259500789153053156802595057/5629499534213120000000000000000000), (2357225647151186055404480887/11258999068426240000000000000000000), (53082522240647139300163467/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial140.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial140.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial140.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 5466354748658481242393654946657812), (Int.negOfNat 356129578946560411117861071961537), (Int.negOfNat 292287075845077987157115228962228), (Int.ofNat 18041814517742205715180521536968), (Int.ofNat 12059756019682061656657787612570), (Int.negOfNat 781837158617132264217284282304), (Int.negOfNat 221276242540541181106491914091), (Int.ofNat 17861108242326931272013684000), (Int.ofNat 2118650350338985269061427115), (Int.negOfNat 208694892912323535254538882), (Int.negOfNat 12083683980380859790356074), (Int.ofNat 1476167234446406226221438), (Int.ofNat 44647225667071018603135), (Int.negOfNat 7101693529230169472079), (Int.negOfNat 109292409270629430575), (Int.ofNat 25113613026892974347), (Int.ofNat 37933320739455799), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-1366588687164620310598413736664453/2814749767106560000000000000000000), (-356129578946560411117861071961537/11258999068426240000000000000000000), (-73071768961269496789278807240557/2814749767106560000000000000000000), (2255226814717775714397565192121/1407374883553280000000000000000000), (1205975601968206165665778761257/1125899906842624000000000000000000), (-12216205603392691628395066911/175921860444160000000000000000000), (-221276242540541181106491914091/11258999068426240000000000000000000), (4465277060581732818003421/2814749767106560000000000000000), (423730070067797053812285423/2251799813685248000000000000000000), (-104347446456161767627269441/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial140.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial140.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial140.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 7046939548293498168969764541088736), (Int.negOfNat 1018250013568204433754454518491555), (Int.ofNat 4486533360880832943225358222595), (Int.ofNat 60398737723265076228613887782057), (Int.negOfNat 2599685472510502647697835638474), (Int.negOfNat 1460037590731739333813391218470), (Int.ofNat 108107320072813252232363648059), (Int.ofNat 18245473098126040181652959559), (Int.negOfNat 1804036803249433232737376251), (Int.negOfNat 127467229566305650192235917), (Int.ofNat 16497383813349906675115247), (Int.ofNat 530565943993711977734641), (Int.negOfNat 96649470126086087488248), (Int.negOfNat 1280644208814348778707), (Int.ofNat 397923138878792134230), (Int.ofNat 778602351056497232), (Int.negOfNat 1488182320203956765), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-220216860884171817780305141909023/351843720888320000000000000000000), (-203650002713640886750890903698311/2251799813685248000000000000000000), (897306672176166588645071644519/2251799813685248000000000000000000), (60398737723265076228613887782057/11258999068426240000000000000000000), (-1299842736255251323848917819237/5629499534213120000000000000000000), (-146003759073173933381339121847/1125899906842624000000000000000000), (108107320072813252232363648059/11258999068426240000000000000000000), (18245473098126040181652959559/11258999068426240000000000000000000), (-1804036803249433232737376251/11258999068426240000000000000000000), (-127467229566305650192235917/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial140.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial140.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial140.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 8661874938232815234607575698839723), (Int.negOfNat 448634365840320427051159576659155), (Int.ofNat 222268414023144248950262162164372), (Int.ofNat 5061131506131444107426666117695), (Int.negOfNat 7907536505966201844730109202759), (Int.ofNat 443591547293698602263144512433), (Int.ofNat 133411624133797431698637234919), (Int.negOfNat 12755693843910970616235506679), (Int.negOfNat 1173147417947257088926695811), (Int.ofNat 158629899819152355893908257), (Int.ofNat 5623577092130219833898047), (Int.negOfNat 1161655569953705209385181), (Int.negOfNat 12700934050411200801768), (Int.ofNat 5707550714744677129027), (Int.negOfNat 11660486789605817730), (Int.negOfNat 20771456361461872872), (Int.ofNat 262819012422587895), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-8661874938232815234607575698839723/11258999068426240000000000000000000), (-89726873168064085410231915331831/2251799813685248000000000000000000), (55567103505786062237565540541093/2814749767106560000000000000000000), (1012226301226288821485333223539/2251799813685248000000000000000000), (-7907536505966201844730109202759/11258999068426240000000000000000000), (443591547293698602263144512433/11258999068426240000000000000000000), (133411624133797431698637234919/11258999068426240000000000000000000), (-12755693843910970616235506679/11258999068426240000000000000000000), (-1173147417947257088926695811/11258999068426240000000000000000000), (158629899819152355893908257/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial140.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial140.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial140.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 8735216735091782118792897924525872), (Int.ofNat 302699378626232221244256172892123), (Int.ofNat 120449404043828842979783587881555), (Int.negOfNat 27464807768624775667437653940974), (Int.ofNat 314078750453542100397743762856), (Int.ofNat 778802614639719415190466391644), (Int.negOfNat 67795677064259981115170395991), (Int.negOfNat 9149802499741997493225944180), (Int.ofNat 1277799743574186119259764535), (Int.ofNat 51817196529819069368523282), (Int.negOfNat 12143639568231632745990934), (Int.negOfNat 97791059323712417625858), (Int.ofNat 72497809299795411327015), (Int.negOfNat 565326401993516335661), (Int.negOfNat 301516197162927504015), (Int.ofNat 5139091312851023973), (Int.ofNat 1260640515899084219), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-545951045943236382424556120282867/703687441776640000000000000000000), (302699378626232221244256172892123/11258999068426240000000000000000000), (24089880808765768595956717576311/2251799813685248000000000000000000), (-13732403884312387833718826970487/5629499534213120000000000000000000), (39259843806692762549717970357/1407374883553280000000000000000000), (194700653659929853797616597911/2814749767106560000000000000000000), (-67795677064259981115170395991/11258999068426240000000000000000000), (-457490124987099874661297209/562949953421312000000000000000000), (255559948714837223851952907/2251799813685248000000000000000000), (25908598264909534684261641/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial140.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial140.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial140.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 7842960678818227216268522354089903), (Int.ofNat 511524444725784609120984922543912), (Int.ofNat 5473672003380259953453606852199), (Int.negOfNat 7385752580179638122867592993262), (Int.ofNat 2953832135192660233474339798427), (Int.negOfNat 220351842311590741639528878989), (Int.negOfNat 56255575842186708791952776995), (Int.ofNat 8238433263769697478778064174), (Int.ofNat 395378669272516667221415567), (Int.negOfNat 107957149575624532688486048), (Int.negOfNat 388360015728477165916117), (Int.ofNat 804507247361773125805579), (Int.negOfNat 12627195263677709103286), (Int.negOfNat 3969164209788775997028), (Int.ofNat 105710563135380383849), (Int.ofNat 13775908313530473485), (Int.negOfNat 449800443432195316), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-7842960678818227216268522354089903/11258999068426240000000000000000000), (63940555590723076140123115317989/1407374883553280000000000000000000), (5473672003380259953453606852199/11258999068426240000000000000000000), (-3692876290089819061433796496631/5629499534213120000000000000000000), (2953832135192660233474339798427/11258999068426240000000000000000000), (-220351842311590741639528878989/11258999068426240000000000000000000), (-11251115168437341758390555399/2251799813685248000000000000000000), (4119216631884848739389032087/5629499534213120000000000000000000), (395378669272516667221415567/11258999068426240000000000000000000), (-3373660924238266646515189/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial140.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial140.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial140.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 6819391793441512540707809812885092), (Int.ofNat 514737031859047018452286031167880), (Int.ofNat 6685665130239756661294949645591), (Int.ofNat 3197136702028262902425354559614), (Int.negOfNat 284866046440990252927639207271), (Int.negOfNat 225688237732798866000312356508), (Int.ofNat 39900300885394981711176039858), (Int.ofNat 2203679056732442341418395204), (Int.negOfNat 789419736253193880762147498), (Int.ofNat 4000546187635797506167114), (Int.ofNat 7616982768673225268129513), (Int.negOfNat 211807054045279037161851), (Int.negOfNat 45382758662443261000073), (Int.ofNat 1834842529342879194301), (Int.ofNat 186388446189065155438), (Int.negOfNat 9502079263470927023), (Int.negOfNat 864419912798897039), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-1704847948360378135176952453221273/2814749767106560000000000000000000), (12868425796476175461307150779197/281474976710656000000000000000000), (6685665130239756661294949645591/11258999068426240000000000000000000), (1598568351014131451212677279807/5629499534213120000000000000000000), (-284866046440990252927639207271/11258999068426240000000000000000000), (-56422059433199716500078089127/2814749767106560000000000000000000), (19950150442697490855588019929/5629499534213120000000000000000000), (550919764183110585354598801/2814749767106560000000000000000000), (-394709868126596940381073749/5629499534213120000000000000000000), (2000273093817898753083557/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial140.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial140.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial140.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 5746735011059603498490217570173727), (Int.ofNat 560559132147050653820970081633294), (Int.ofNat 10716449906068446299508844460981), (Int.negOfNat 1780750614537942628248034249314), (Int.negOfNat 310211705912547509025448877597), (Int.ofNat 143952836318361466277917767014), (Int.ofNat 5322351831269459544651877920), (Int.negOfNat 4541409066882939984376425808), (Int.ofNat 117082772410919674089341904), (Int.ofNat 59269423782378870795541392), (Int.negOfNat 2919005051798204561550929), (Int.negOfNat 435774354205456879772763), (Int.ofNat 27660105333081032466226), (Int.ofNat 2087643098166230047616), (Int.negOfNat 156287041144782463484), (Int.negOfNat 6649124838648799598), (Int.ofNat 504708340075073677), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-5746735011059603498490217570173727/11258999068426240000000000000000000), (280279566073525326910485040816647/5629499534213120000000000000000000), (10716449906068446299508844460981/11258999068426240000000000000000000), (-890375307268971314124017124657/5629499534213120000000000000000000), (-310211705912547509025448877597/11258999068426240000000000000000000), (71976418159180733138958883507/5629499534213120000000000000000000), (33264698945434122154074237/70368744177664000000000000000000), (-283838066680183749023526613/703687441776640000000000000000000), (7317673275682479630583869/703687441776640000000000000000000), (3704338986398679424721337/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial140.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial140.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial140.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 4597537953189173390817018938885894), (Int.ofNat 582870084181886018283524817185474), (Int.ofNat 2767796772345514417323897094280), (Int.ofNat 272857956977936601662042708034), (Int.ofNat 493625264458536745143507188376), (Int.negOfNat 34825764180177581973955809641), (Int.negOfNat 19604525939266504243020837036), (Int.ofNat 1617138624737975385701279613), (Int.ofNat 354524937667536090155116878), (Int.negOfNat 33766550176861200423203381), (Int.negOfNat 3280740074088893835278902), (Int.ofNat 360525808133160865343969), (Int.ofNat 18283786692944688916878), (Int.negOfNat 2357575890424328728712), (Int.negOfNat 67775910812247677215), (Int.ofNat 10717383943250582447), (Int.ofNat 468199309698709859), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-2298768976594586695408509469442947/5629499534213120000000000000000000), (291435042090943009141762408592737/5629499534213120000000000000000000), (69194919308637860433097427357/281474976710656000000000000000000), (136428978488968300831021354017/5629499534213120000000000000000000), (61703158057317093142938398547/1407374883553280000000000000000000), (-34825764180177581973955809641/11258999068426240000000000000000000), (-4901131484816626060755209259/2814749767106560000000000000000000), (1617138624737975385701279613/11258999068426240000000000000000000), (177262468833768045077558439/5629499534213120000000000000000000), (-33766550176861200423203381/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial140.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial140.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial140.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 3412736946598237926940042464066410), (Int.ofNat 607458740932176879557317393840585), (Int.ofNat 10300434634358964983054599082757), (Int.ofNat 1017658049245081014377198285218), (Int.negOfNat 344633571687444470633465274403), (Int.negOfNat 58241723761474727464256209208), (Int.ofNat 14896901802006897903218232873), (Int.ofNat 1373728710556645505005472493), (Int.negOfNat 324351822369116913026150827), (Int.negOfNat 15767884427088132544716515), (Int.ofNat 4018013762686945198031054), (Int.ofNat 94492594677879434473989), (Int.negOfNat 30846813119990316095851), (Int.negOfNat 298443643548407325207), (Int.ofNat 159804133547898876982), (Int.negOfNat 243392257982779509), (Int.negOfNat 559616236717952038), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-341273694659823792694004246406641/1125899906842624000000000000000000), (121491748186435375911463478768117/2251799813685248000000000000000000), (10300434634358964983054599082757/11258999068426240000000000000000000), (508829024622540507188599142609/5629499534213120000000000000000000), (-344633571687444470633465274403/11258999068426240000000000000000000), (-7280215470184340933032026151/1407374883553280000000000000000000), (14896901802006897903218232873/11258999068426240000000000000000000), (1373728710556645505005472493/11258999068426240000000000000000000), (-324351822369116913026150827/11258999068426240000000000000000000), (-3153576885417626508943303/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial140.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial140.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial140.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 2154812020574778315704539010790096), (Int.ofNat 648312814742331165764827540697120), (Int.ofNat 7367219332819851378505766333568), (Int.negOfNat 1520030471953297635233452254569), (Int.negOfNat 21307011379965662940858517992), (Int.ofNat 90946090997128267441380797842), (Int.ofNat 332450943549831649435949109), (Int.negOfNat 2477447885851706200729610557), (Int.ofNat 12297155025177588052666290), (Int.ofNat 37187701690947438265643914), (Int.negOfNat 425326195336832445279213), (Int.negOfNat 342875941929476965471804), (Int.ofNat 5402194310448710829681), (Int.ofNat 2099850687379001374757), (Int.negOfNat 37315410481969706291), (Int.negOfNat 9299025984556514051), (Int.negOfNat 53676074384229892), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-134675751285923644731533688174381/703687441776640000000000000000000), (4051955092139569786030172129357/70368744177664000000000000000000), (57556401037655088894576299481/87960930222080000000000000000000), (-1520030471953297635233452254569/11258999068426240000000000000000000), (-2663376422495707867607314749/1407374883553280000000000000000000), (45473045498564133720690398921/5629499534213120000000000000000000), (332450943549831649435949109/11258999068426240000000000000000000), (-2477447885851706200729610557/11258999068426240000000000000000000), (1229715502517758805266629/1125899906842624000000000000000000), (18593850845473719132821957/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial140.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial140.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial140.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 838583142426749904304023060868776), (Int.ofNat 665181594228885269504096320726446), (Int.ofNat 3605819868292191656205300902939), (Int.ofNat 815298822799978190641354501315), (Int.ofNat 359319920155906966668819929351), (Int.negOfNat 45084263560692191980942539379), (Int.negOfNat 13752662271855080965859376169), (Int.ofNat 1192840339013383823359957383), (Int.ofNat 267812582748236567011835310), (Int.negOfNat 18176881012368477536648086), (Int.negOfNat 3073170450924474786564747), (Int.ofNat 175864605739047319417716), (Int.ofNat 22794767777119002757359), (Int.negOfNat 1149427395873559072263), (Int.negOfNat 117084498977621354769), (Int.ofNat 5940083041454389229), (Int.ofNat 332074432413079492), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-104822892803343738038002882608597/1407374883553280000000000000000000), (332590797114442634752048160363223/5629499534213120000000000000000000), (3605819868292191656205300902939/11258999068426240000000000000000000), (163059764559995638128270900263/2251799813685248000000000000000000), (359319920155906966668819929351/11258999068426240000000000000000000), (-45084263560692191980942539379/11258999068426240000000000000000000), (-13752662271855080965859376169/11258999068426240000000000000000000), (1192840339013383823359957383/11258999068426240000000000000000000), (26781258274823656701183531/1125899906842624000000000000000000), (-9088440506184238768324043/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial140.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial140.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial140.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 516361200488927828563299993269309), (Int.ofNat 695392931205996751606591258141627), (Int.ofNat 11382528784157728145610791943033), (Int.ofNat 698633667901292357957231813583), (Int.negOfNat 387535416254024062140546388620), (Int.negOfNat 44332146964481518196302595926), (Int.ofNat 14023755903199727322050392487), (Int.ofNat 1249733965203876871468574473), (Int.negOfNat 264112793797036155159477653), (Int.negOfNat 19261955975191882477907815), (Int.ofNat 2990668422677969993157446), (Int.ofNat 182878599310260655354109), (Int.negOfNat 22244054927263306452649), (Int.negOfNat 1158145913459532060127), (Int.ofNat 115627608286843389178), (Int.ofNat 5884031843225759651), (Int.negOfNat 247076258777813802), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(516361200488927828563299993269309/11258999068426240000000000000000000), (695392931205996751606591258141627/11258999068426240000000000000000000), (11382528784157728145610791943033/11258999068426240000000000000000000), (698633667901292357957231813583/11258999068426240000000000000000000), (-19376770812701203107027319431/562949953421312000000000000000000), (-22166073482240759098151297963/5629499534213120000000000000000000), (14023755903199727322050392487/11258999068426240000000000000000000), (1249733965203876871468574473/11258999068426240000000000000000000), (-264112793797036155159477653/11258999068426240000000000000000000), (-3852391195038376495581563/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial140.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial140.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial140.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1951630401742262415072716737012969), (Int.ofNat 736313334190257144245618902013269), (Int.ofNat 6408342811041339267058013070041), (Int.negOfNat 1757216082059327140976904948656), (Int.ofNat 31828970345709152369230949013), (Int.ofNat 98793166802898817945051079232), (Int.ofNat 275821803703250810397428156), (Int.negOfNat 2547725360333834795128703047), (Int.negOfNat 30131144133912524802565178), (Int.ofNat 36727169285499699650262399), (Int.ofNat 587716727395209791297702), (Int.negOfNat 331822754257755504721591), (Int.negOfNat 5905733166576975441738), (Int.ofNat 2027950555989575036768), (Int.ofNat 36816361422159888775), (Int.negOfNat 9070884954024862633), (Int.ofNat 45843538472814901), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(1951630401742262415072716737012969/11258999068426240000000000000000000), (736313334190257144245618902013269/11258999068426240000000000000000000), (6408342811041339267058013070041/11258999068426240000000000000000000), (-109826005128707946311056559291/703687441776640000000000000000000), (31828970345709152369230949013/11258999068426240000000000000000000), (1543643231295294030391423113/175921860444160000000000000000000), (68955450925812702599357039/2814749767106560000000000000000000), (-2547725360333834795128703047/11258999068426240000000000000000000), (-15065572066956262401282589/5629499534213120000000000000000000), (36727169285499699650262399/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial140.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial140.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial140.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3439205907038645354333552525194337), (Int.ofNat 748746671072987969293661040262277), (Int.ofNat 2999121641321591973209642541669), (Int.ofNat 1204948280505505476729370791554), (Int.ofNat 431173074434681866542253206189), (Int.negOfNat 56355301561484716878235039798), (Int.negOfNat 16915972547881891252381920613), (Int.ofNat 1145415230579339467583559972), (Int.ofNat 335142124717173002634135336), (Int.negOfNat 12229390367196708596549828), (Int.negOfNat 3897700195238599867260031), (Int.ofNat 74697337753731426862237), (Int.ofNat 29244453344146674901534), (Int.negOfNat 264594381153191368284), (Int.negOfNat 151346724866817391556), (Int.ofNat 94632543013074842), (Int.ofNat 301984155420692163), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(3439205907038645354333552525194337/11258999068426240000000000000000000), (748746671072987969293661040262277/11258999068426240000000000000000000), (2999121641321591973209642541669/11258999068426240000000000000000000), (602474140252752738364685395777/5629499534213120000000000000000000), (431173074434681866542253206189/11258999068426240000000000000000000), (-28177650780742358439117519899/5629499534213120000000000000000000), (-16915972547881891252381920613/11258999068426240000000000000000000), (286353807644834866895889993/2814749767106560000000000000000000), (41892765589646625329266917/1407374883553280000000000000000000), (-3057347591799177149137457/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial140.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial140.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial140.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4962570524306992410348859516107036), (Int.ofNat 782053512440790790821215022909946), (Int.ofNat 13281729588096575872997118314929), (Int.ofNat 816221096288410985206260446292), (Int.negOfNat 546342165586948472938379034860), (Int.negOfNat 64136379920866260039661776694), (Int.ofNat 18006393159045122274108393302), (Int.ofNat 2048913400473601282352012784), (Int.negOfNat 294148570396221371545675422), (Int.negOfNat 34059355455575752878790626), (Int.ofNat 2755324430914246946329247), (Int.ofNat 336587270923265861888129), (Int.negOfNat 16283078681815565289507), (Int.negOfNat 2165554475871274174759), (Int.ofNat 64902686802840707842), (Int.ofNat 9991903031268269657), (Int.negOfNat 442064141573002081), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(1240642631076748102587214879026759/2814749767106560000000000000000000), (391026756220395395410607511454973/5629499534213120000000000000000000), (13281729588096575872997118314929/11258999068426240000000000000000000), (204055274072102746301565111573/2814749767106560000000000000000000), (-27317108279347423646918951743/562949953421312000000000000000000), (-32068189960433130019830888347/5629499534213120000000000000000000), (9003196579522561137054196651/5629499534213120000000000000000000), (128057087529600080147000799/703687441776640000000000000000000), (-147074285198110685772837711/5629499534213120000000000000000000), (-17029677727787876439395313/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial140.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial140.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial140.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 6576865754874651616103818178011457), (Int.ofNat 826374076881293467798147834679578), (Int.ofNat 4990083590754475364703412073750), (Int.negOfNat 2747637942497098834267269968656), (Int.ofNat 48084519318507355960892402678), (Int.ofNat 153508069196859365831271953158), (Int.ofNat 3726808899123924281023634835), (Int.negOfNat 3747264268937169558016507506), (Int.negOfNat 165560374040852724035882147), (Int.ofNat 48498026318858160306289272), (Int.ofNat 2717224851686250132754637), (Int.negOfNat 376230196222504232591741), (Int.negOfNat 24331232120145992468214), (Int.ofNat 1916381702223752673372), (Int.ofNat 138665257056979112751), (Int.negOfNat 6367324688468730795), (Int.negOfNat 356892052063570524), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(6576865754874651616103818178011457/11258999068426240000000000000000000), (413187038440646733899073917339789/5629499534213120000000000000000000), (3992066872603580291762729659/9007199254740992000000000000000), (-171727371406068677141704373041/703687441776640000000000000000000), (24042259659253677980446201339/5629499534213120000000000000000000), (76754034598429682915635976579/5629499534213120000000000000000000), (745361779824784856204726967/2251799813685248000000000000000000), (-1873632134468584779008253753/5629499534213120000000000000000000), (-165560374040852724035882147/11258999068426240000000000000000000), (6062253289857270038286159/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial140.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial140.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial140.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 8233017993426177195643897816510592), (Int.ofNat 826170276962925919970073230866359), (Int.ofNat 261411387259967657823014538144), (Int.ofNat 2262976833186901003219672647098), (Int.ofNat 786020910261106857562925238974), (Int.negOfNat 83871053103867064913632603153), (Int.negOfNat 32052452649928037676649413629), (Int.ofNat 849992435534382584588090760), (Int.ofNat 605488527181367022268765405), (Int.ofNat 5169119082537892924387242), (Int.negOfNat 6266428298320894192920846), (Int.negOfNat 166786957447031006557758), (Int.ofNat 39968135460459015811385), (Int.ofNat 1484114010149084831159), (Int.negOfNat 173489980807159235105), (Int.negOfNat 7898673202946017507), (Int.ofNat 838284744673189261), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(64320453073642009340967951691489/87960930222080000000000000000000), (826170276962925919970073230866359/11258999068426240000000000000000000), (8169105851873989306969204317/351843720888320000000000000000000), (1131488416593450501609836323549/5629499534213120000000000000000000), (393010455130553428781462619487/5629499534213120000000000000000000), (-83871053103867064913632603153/11258999068426240000000000000000000), (-32052452649928037676649413629/11258999068426240000000000000000000), (21249810888359564614702269/281474976710656000000000000000000), (121097705436273404453753081/2251799813685248000000000000000000), (2584559541268946462193621/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial140.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial140.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial140.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 9912608976558455424649420438276177), (Int.ofNat 867640362026573165094094688815790), (Int.ofNat 19907533288558487148212619212014), (Int.ofNat 1558228421527550012667836774768), (Int.negOfNat 1124702331067861294621060316901), (Int.negOfNat 166540467099801957922832192972), (Int.ofNat 30156399429103696869821250101), (Int.ofNat 5476485628036919186577911501), (Int.negOfNat 309511696125629729618459669), (Int.negOfNat 82173360479679249078628683), (Int.ofNat 825719000929657146250633), (Int.ofNat 674331725122231958358199), (Int.ofNat 6921741649008846903228), (Int.negOfNat 3550906249487618141613), (Int.negOfNat 75423116824731201270), (Int.ofNat 13240886695545823728), (Int.ofNat 279726414339719825), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(9912608976558455424649420438276177/11258999068426240000000000000000000), (86764036202657316509409468881579/1125899906842624000000000000000000), (9953766644279243574106309606007/5629499534213120000000000000000000), (97389276345471875791739798423/703687441776640000000000000000000), (-1124702331067861294621060316901/11258999068426240000000000000000000), (-41635116774950489480708048243/2814749767106560000000000000000000), (30156399429103696869821250101/11258999068426240000000000000000000), (5476485628036919186577911501/11258999068426240000000000000000000), (-309511696125629729618459669/11258999068426240000000000000000000), (-82173360479679249078628683/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial140.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial140.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial140.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 11719173045903485598213359601394692), (Int.ofNat 924404550226260272098359184336437), (Int.negOfNat 1046369352354802227810942605651), (Int.negOfNat 7164685919445514293785694003350), (Int.negOfNat 86163001284974223423180486146), (Int.ofNat 377132981423102750409972706915), (Int.ofNat 29292421068933180812039475961), (Int.negOfNat 7180011517006873608308041461), (Int.negOfNat 844171235288987904938833269), (Int.ofNat 53957158590291173434730543), (Int.ofNat 9517843034359073303826373), (Int.negOfNat 178413303394105438479879), (Int.negOfNat 62048591544249214822712), (Int.negOfNat 27487146210535583247), (Int.ofNat 272139565824859790570), (Int.ofNat 3556516537514916032), (Int.negOfNat 1139037077835232955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(2929793261475871399553339900348673/2814749767106560000000000000000000), (924404550226260272098359184336437/11258999068426240000000000000000000), (-1046369352354802227810942605651/11258999068426240000000000000000000), (-143293718388910285875713880067/225179981368524800000000000000000), (-43081500642487111711590243073/5629499534213120000000000000000000), (75426596284620550081994541383/2251799813685248000000000000000000), (29292421068933180812039475961/11258999068426240000000000000000000), (-7180011517006873608308041461/11258999068426240000000000000000000), (-844171235288987904938833269/11258999068426240000000000000000000), (53957158590291173434730543/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial140.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial140.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial140.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 13517945151693634347702154193781040), (Int.ofNat 863368876789876955585972309380169), (Int.negOfNat 14890139266776289856074262939618), (Int.ofNat 6806494630486593876429268940092), (Int.ofNat 2817184423682337057085945143670), (Int.negOfNat 78431978526358240081129840389), (Int.negOfNat 103638800848771327334877296889), (Int.negOfNat 6177949713938754914718342660), (Int.ofNat 1164097587638776680257786945), (Int.ofNat 112642440155307644119743378), (Int.negOfNat 6660892586428859784861546), (Int.negOfNat 942958594140593972613562), (Int.ofNat 21385288622227053603165), (Int.ofNat 4966184923189391660741), (Int.negOfNat 29155698491471285105), (Int.negOfNat 19158580359453344933), (Int.negOfNat 52184610034847279), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(168974314396170429346276927422263/140737488355328000000000000000000), (863368876789876955585972309380169/11258999068426240000000000000000000), (-7445069633388144928037131469809/5629499534213120000000000000000000), (1701623657621648469107317235023/2814749767106560000000000000000000), (281718442368233705708594514367/1125899906842624000000000000000000), (-78431978526358240081129840389/11258999068426240000000000000000000), (-103638800848771327334877296889/11258999068426240000000000000000000), (-308897485696937745735917133/562949953421312000000000000000000), (232819517527755336051557389/2251799813685248000000000000000000), (56321220077653822059871689/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial140.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial140.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial140.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 15275062829047665132964679601164405), (Int.ofNat 948102848151026954839976237972950), (Int.ofNat 60765845434860583715187567470247), (Int.ofNat 8718123920105549053328414049025), (Int.negOfNat 4282233206599039259114210797201), (Int.negOfNat 1170320555844657334433296066921), (Int.negOfNat 18091318079136214219849978105), (Int.ofNat 18339069532589893033614243006), (Int.ofNat 1101260872975724315323658793), (Int.negOfNat 141210944001580849310451012), (Int.negOfNat 12562726714268153259866963), (Int.ofNat 660033699794574542924061), (Int.ofNat 80544151570347057706526), (Int.negOfNat 2003530116244511015832), (Int.negOfNat 350521645655201932329), (Int.ofNat 3878526411284855555), (Int.ofNat 1326018508844840376), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(3055012565809533026592935920232881/2251799813685248000000000000000000), (18962056963020539096799524759459/225179981368524800000000000000000), (60765845434860583715187567470247/11258999068426240000000000000000000), (348724956804221962133136561961/450359962737049600000000000000000), (-4282233206599039259114210797201/11258999068426240000000000000000000), (-1170320555844657334433296066921/11258999068426240000000000000000000), (-3618263615827242843969995621/2251799813685248000000000000000000), (9169534766294946516807121503/5629499534213120000000000000000000), (1101260872975724315323658793/11258999068426240000000000000000000), (-35302736000395212327612753/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial140.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial140.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial140.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 17379498884151696251433964744048602), (Int.ofNat 1070616268618285903764502108435518), (Int.negOfNat 74141092384187214406237536529135), (Int.negOfNat 63919833425200643238956931231244), (Int.negOfNat 11403759141462409441130687507329), (Int.ofNat 287126639831877710936028419875), (Int.ofNat 238722645080452835315894235589), (Int.ofNat 8729629724843999384707160216), (Int.negOfNat 2335827413560042034241051322), (Int.negOfNat 148079207088604499457032734), (Int.ofNat 13933183270662550042573707), (Int.ofNat 1175350058790296668176211), (Int.negOfNat 56145701357927178093227), (Int.negOfNat 6004802975946869902741), (Int.ofNat 160810238851007376542), (Int.ofNat 22409729501599890983), (Int.negOfNat 344035993065339901), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(8689749442075848125716982372024301/5629499534213120000000000000000000), (535308134309142951882251054217759/5629499534213120000000000000000000), (-14828218476837442881247507305827/2251799813685248000000000000000000), (-15979958356300160809739232807811/2814749767106560000000000000000000), (-11403759141462409441130687507329/11258999068426240000000000000000000), (2297013118655021687488227359/90071992547409920000000000000000), (238722645080452835315894235589/11258999068426240000000000000000000), (1091203715605499923088395027/1407374883553280000000000000000000), (-1167913706780021017120525661/5629499534213120000000000000000000), (-74039603544302249728516367/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial140.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial140.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial140.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 18555274543036088169923792947289709), (Int.negOfNat 287840802089683408311770424422435), (Int.negOfNat 649899654572662867094900444211465), (Int.negOfNat 105306765285443650164735890933998), (Int.ofNat 5249798756382908685417350383387), (Int.ofNat 2679776763635220920521712188834), (Int.ofNat 59544180152317092230913068700), (Int.negOfNat 32363868826406833892572333052), (Int.negOfNat 1586534042598611657821426084), (Int.ofNat 238173894436429516641463948), (Int.ofNat 15612714051421339543908869), (Int.negOfNat 1186513496494122116505397), (Int.negOfNat 93983502293553183403106), (Int.ofNat 4265483760712390381184), (Int.ofNat 395853151502886586464), (Int.negOfNat 11341481839969021842), (Int.negOfNat 1380926405487718737), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(18555274543036088169923792947289709/11258999068426240000000000000000000), (-57568160417936681662354084884487/2251799813685248000000000000000000), (-129979930914532573418980088842293/2251799813685248000000000000000000), (-52653382642721825082367945466999/5629499534213120000000000000000000), (5249798756382908685417350383387/11258999068426240000000000000000000), (1339888381817610460260856094417/5629499534213120000000000000000000), (595441801523170922309130687/112589990684262400000000000000000), (-8090967206601708473143083263/2814749767106560000000000000000000), (-396633510649652914455356521/2814749767106560000000000000000000), (59543473609107379160365987/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial140.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial140.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial140.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 14706687092916217211511351899645275), (Int.negOfNat 3772822759816038477214073120076190), (Int.negOfNat 950425504179325477734263041644646), (Int.ofNat 33903975558230725536087461393886), (Int.ofNat 25891466269298239359113318031949), (Int.ofNat 528189005445001950687240004164), (Int.negOfNat 380627176913845418002187627704), (Int.negOfNat 16493176938032347373076357053), (Int.ofNat 3438895801046597262701802522), (Int.ofNat 192835875544859381340149621), (Int.negOfNat 20860867428652826624916058), (Int.negOfNat 1354935123017708755795909), (Int.ofNat 90607999314944632794082), (Int.ofNat 6543547766839356999012), (Int.negOfNat 295306768978105895865), (Int.negOfNat 23728357128445426207), (Int.ofNat 740256596165527081), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(588267483716648688460454075985811/450359962737049600000000000000000), (-377282275981603847721407312007619/1125899906842624000000000000000000), (-475212752089662738867131520822323/5629499534213120000000000000000000), (16951987779115362768043730696943/5629499534213120000000000000000000), (25891466269298239359113318031949/11258999068426240000000000000000000), (132047251361250487671810001041/2814749767106560000000000000000000), (-47578397114230677250273453463/1407374883553280000000000000000000), (-16493176938032347373076357053/11258999068426240000000000000000000), (1719447900523298631350901261/5629499534213120000000000000000000), (192835875544859381340149621/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial140.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial140.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial140.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 4036220975591996490366098769290518), (Int.negOfNat 6373518200421019047931906338795670), (Int.negOfNat 179005619934260729850542855460007), (Int.ofNat 198860132996492597554169676243938), (Int.ofNat 8022627254365897571370107597198), (Int.negOfNat 3692691246834063935020337309515), (Int.negOfNat 180397301330581170464726150613), (Int.ofNat 41969351137864554291757056487), (Int.ofNat 2280748643305247807787775967), (Int.negOfNat 313096365931532884518855665), (Int.negOfNat 18231225435050564826163154), (Int.ofNat 1638241003869300287915831), (Int.ofNat 100224043375433025982111), (Int.negOfNat 6342998557226890220233), (Int.negOfNat 402745085706364369902), (Int.ofNat 18570170890403093349), (Int.ofNat 1435834302130597098), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(2018110487795998245183049384645259/5629499534213120000000000000000000), (-637351820042101904793190633879567/1125899906842624000000000000000000), (-179005619934260729850542855460007/11258999068426240000000000000000000), (99430066498246298777084838121969/5629499534213120000000000000000000), (4011313627182948785685053798599/5629499534213120000000000000000000), (-738538249366812787004067461903/2251799813685248000000000000000000), (-180397301330581170464726150613/11258999068426240000000000000000000), (41969351137864554291757056487/11258999068426240000000000000000000), (2280748643305247807787775967/11258999068426240000000000000000000), (-62619273186306576903771133/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial140.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial140.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial140.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 7831525669867314252136546959930084), (Int.negOfNat 4756203018046472026269989585500531), (Int.ofNat 898677075469518769278541419741695), (Int.ofNat 112175004665097960438287145777677), (Int.negOfNat 26850472597184174121103139172198), (Int.negOfNat 2032311612320774316092602849832), (Int.ofNat 419460939087428476791102511924), (Int.ofNat 26227332491728552336595655557), (Int.negOfNat 3999980688023515460357945410), (Int.negOfNat 231742420892418577846452494), (Int.ofNat 25620276922286350372932613), (Int.ofNat 1432741881989593880526664), (Int.negOfNat 118069296495012413042881), (Int.negOfNat 6460592610213688560577), (Int.ofNat 411175730369678489531), (Int.ofNat 21973827215948865411), (Int.negOfNat 1154779831480007048), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-1957881417466828563034136739982521/2814749767106560000000000000000000), (-4756203018046472026269989585500531/11258999068426240000000000000000000), (179735415093903753855708283948339/2251799813685248000000000000000000), (112175004665097960438287145777677/11258999068426240000000000000000000), (-13425236298592087060551569586099/5629499534213120000000000000000000), (-254038951540096789511575356229/1407374883553280000000000000000000), (104865234771857119197775627981/2814749767106560000000000000000000), (26227332491728552336595655557/11258999068426240000000000000000000), (-399998068802351546035794541/1125899906842624000000000000000000), (-115871210446209288923226247/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial140.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial140.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial140.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial140.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial140.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial140.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial140.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial140.reflect := by
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

end Bin140
end
end ErdosOverlap.OuterNumerics
