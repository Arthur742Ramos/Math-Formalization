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

/-! # Exact integer weighted outer models for source bin 143

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin143

def weightDenominator : ℤ := (Int.ofNat 50000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 12799753468107795000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 12623841121973020000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 11149468075993060000)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 7626573706493446000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 4919330125440824500)⟩, ⟨(19494472361809/1000000000000), (Int.negOfNat 10128254024225853)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 2784872948529723200)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 1682055319279113500)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 2556073639747578000)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 867320362598409200)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial143.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial143.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 49492638484975080000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 11506575185469904000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 7570475157460621000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 4764004663497929000)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 1498100281204641100)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 248171619234675100)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 579088457455063300)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 574185088670456350)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 4583069150884190)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial143.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial143.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 49492638484975080000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 11506575185469904000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 7570475157460621000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 4764004663497929000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 1498100281204641100)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 248171619234675100)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 579088457455063300)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 574185088670456350)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 4583069150884190)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial143.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial143.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial143.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 44649972603449312106857185428800864), (Int.ofNat 25026955440999010651794171865454580), (Int.ofNat 4810752268198436763011377567695010), (Int.negOfNat 823510739077423252289720255777720), (Int.negOfNat 141183681485958283920073897160661), (Int.ofNat 16714345056701040347663791405875), (Int.ofNat 2223076046390064867872685795095), (Int.negOfNat 207019739322937211543968191327), (Int.negOfNat 21809197591883337182210444839), (Int.ofNat 1690482455575877572155759267), (Int.ofNat 145113925828891354781501164), (Int.negOfNat 9729510396642526324508044), (Int.negOfNat 696340624345311261639691), (Int.ofNat 41544126167091617382475), (Int.ofNat 2521330393810984890380), (Int.negOfNat 135757239494379686350), (Int.negOfNat 7439362126504775210), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1395311643857791003339287044650027/1759218604441600000000000000000000), (1251347772049950532589708593272729/2814749767106560000000000000000000), (481075226819843676301137756769501/5629499534213120000000000000000000), (-20587768476935581307243006394443/1407374883553280000000000000000000), (-141183681485958283920073897160661/56294995342131200000000000000000000), (133714760453608322781310331247/450359962737049600000000000000000), (444615209278012973574537159019/11258999068426240000000000000000000), (-207019739322937211543968191327/56294995342131200000000000000000000), (-21809197591883337182210444839/56294995342131200000000000000000000), (1690482455575877572155759267/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial143.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial143.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial143.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial143 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 16445968484733507703382512607236913), (Int.ofNat 31523372194369861326675491564768405), (Int.negOfNat 1817086154579041999338704905909407), (Int.negOfNat 1072886018612779268457843238779832), (Int.ofNat 85237013424882199859864555111990), (Int.ofNat 20466816673338494957430984883733), (Int.negOfNat 1668596627483578359541666263204), (Int.negOfNat 236835718466732933063444888874), (Int.ofNat 18446905778529358225097328887), (Int.ofNat 1811932241817432593287150461), (Int.negOfNat 133072401155548948048109928), (Int.negOfNat 9785176180036677644551992), (Int.ofNat 680699111250662020071730), (Int.ofNat 39242483535984819203644), (Int.negOfNat 2610098023633011392399), (Int.negOfNat 120365744253962784390), (Int.ofNat 8071463365869522810), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(16445968484733507703382512607236913/56294995342131200000000000000000000), (6304674438873972265335098312953681/11258999068426240000000000000000000), (-1817086154579041999338704905909407/56294995342131200000000000000000000), (-134110752326597408557230404847479/7036874417766400000000000000000000), (8523701342488219985986455511199/5629499534213120000000000000000000), (20466816673338494957430984883733/56294995342131200000000000000000000), (-417149156870894589885416565801/14073748835532800000000000000000000), (-118417859233366466531722444437/28147497671065600000000000000000000), (18446905778529358225097328887/56294995342131200000000000000000000), (1811932241817432593287150461/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial143.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial143.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial143.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial143 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 65528402172990418052377604527046283), (Int.ofNat 15341143428500928750429871791913238), (Int.negOfNat 5091336495273044744746089917867134), (Int.ofNat 68505814423006660575299036032773), (Int.ofNat 149337484097420163339202799869448), (Int.negOfNat 8816931079430049831131094041841), (Int.negOfNat 2245783785215615809781539339586), (Int.ofNat 160084239722269909750771296304), (Int.ofNat 20626903145065031209292985053), (Int.negOfNat 1548474900909556477943724271), (Int.negOfNat 127785851169527784967900544), (Int.ofNat 9788766958971956613412152), (Int.ofNat 570508135595553528001242), (Int.negOfNat 44330800834726080987269), (Int.negOfNat 1924787015076136535886), (Int.ofNat 151659532248766356710), (Int.ofNat 4832817969558663420), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(65528402172990418052377604527046283/56294995342131200000000000000000000), (7670571714250464375214935895956619/28147497671065600000000000000000000), (-2545668247636522372373044958933567/28147497671065600000000000000000000), (68505814423006660575299036032773/56294995342131200000000000000000000), (18667185512177520417400349983681/7036874417766400000000000000000000), (-8816931079430049831131094041841/56294995342131200000000000000000000), (-1122891892607807904890769669793/28147497671065600000000000000000000), (10005264982641869359423206019/3518437208883200000000000000000000), (20626903145065031209292985053/56294995342131200000000000000000000), (-1548474900909556477943724271/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial143.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial143.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial143.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial143 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 78381786945832829080088659278828200), (Int.negOfNat 471138783347544351101988380804989), (Int.negOfNat 2204305482653568421183769670167135), (Int.ofNat 667989854028879545082730324278997), (Int.negOfNat 13146004127418430169020650268933), (Int.negOfNat 16899406605344092126525809901070), (Int.ofNat 1003329795411725392500620340341), (Int.ofNat 205160091577789504366600798832), (Int.negOfNat 14867004637329922342683888224), (Int.negOfNat 1523741571617108006334754905), (Int.ofNat 122011297906303750266712641), (Int.ofNat 7720047847865149758042422), (Int.negOfNat 669668407255515181693380), (Int.negOfNat 28524234272692076618907), (Int.ofNat 2675829506148243487395), (Int.ofNat 77510068544234124840), (Int.negOfNat 8057714158416870240), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(391908934729164145400443296394141/281474976710656000000000000000000), (-471138783347544351101988380804989/56294995342131200000000000000000000), (-440861096530713684236753934033427/11258999068426240000000000000000000), (667989854028879545082730324278997/56294995342131200000000000000000000), (-13146004127418430169020650268933/56294995342131200000000000000000000), (-1689940660534409212652580990107/5629499534213120000000000000000000), (1003329795411725392500620340341/56294995342131200000000000000000000), (12822505723611844022912549927/3518437208883200000000000000000000), (-464593894916560073208871507/1759218604441600000000000000000000), (-304748314323421601266950981/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial143.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial143.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial143.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial143 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 73301114512672712878234749780448210), (Int.negOfNat 2778596595276057845704033315896916), (Int.ofNat 482754875339688285158184029013662), (Int.ofNat 129553179488686289863471576073232), (Int.negOfNat 85416696771257887665079893282945), (Int.ofNat 3779513337477250523786732390591), (Int.ofNat 1666931565001558754948545976928), (Int.negOfNat 113084000784628422591372952085), (Int.negOfNat 16067741158388257749764838600), (Int.ofNat 1294673346306894065217850424), (Int.ofNat 95995031525019052171832929), (Int.negOfNat 8901702696135558341055096), (Int.negOfNat 393692606727930387245711), (Int.ofNat 42299171234413763203679), (Int.ofNat 1174450011670620868997), (Int.negOfNat 151290886198103588130), (Int.negOfNat 2230856881763435820), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(7330111451267271287823474978044821/5629499534213120000000000000000000), (-694649148819014461426008328974229/14073748835532800000000000000000000), (241377437669844142579092014506831/28147497671065600000000000000000000), (8097073718042893116466973504577/3518437208883200000000000000000000), (-17083339354251577533015978656589/11258999068426240000000000000000000), (3779513337477250523786732390591/56294995342131200000000000000000000), (52091611406298711092142061779/1759218604441600000000000000000000), (-22616800156925684518274590417/11258999068426240000000000000000000), (-80338705791941288748824193/281474976710656000000000000000000), (161834168288361758152231303/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial143.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial143.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial143.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial143 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 69554480753314401434152965405006190), (Int.negOfNat 1467609481421760123033482397071731), (Int.negOfNat 185486467164256890715730696559543), (Int.negOfNat 219983971656085706257686474227544), (Int.ofNat 8835599551166249223514256985984), (Int.ofNat 10181005223852792052283444823030), (Int.negOfNat 668351377656930274633259108416), (Int.negOfNat 143649875642784165311233280502), (Int.ofNat 11488597421431013967986692150), (Int.ofNat 1073386477868350173331127043), (Int.negOfNat 102843841101954113580597798), (Int.negOfNat 5034386099452507944189825), (Int.ofNat 594277524084756052147391), (Int.ofNat 15950967350302955284441), (Int.negOfNat 2451097505788335629347), (Int.negOfNat 34693468811605444190), (Int.ofNat 8043964950964217670), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(6955448075331440143415296540500619/5629499534213120000000000000000000), (-1467609481421760123033482397071731/56294995342131200000000000000000000), (-185486467164256890715730696559543/56294995342131200000000000000000000), (-27497996457010713282210809278443/7036874417766400000000000000000000), (69028121493486322058705132703/439804651110400000000000000000000), (1018100522385279205228344482303/5629499534213120000000000000000000), (-10442990275889535541144673569/879609302220800000000000000000000), (-71824937821392082655616640251/28147497671065600000000000000000000), (229771948428620279359733843/1125899906842624000000000000000000), (1073386477868350173331127043/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial143.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial143.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial143.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial143 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 64526821792661382274872306940118061), (Int.negOfNat 3931152707917136287980210693771252), (Int.negOfNat 711543551095345697041611683882372), (Int.ofNat 95196396372548767584414679547225), (Int.ofNat 46001448570027425335192109781505), (Int.negOfNat 3510200408181761011647119403992), (Int.negOfNat 1054657893443200250496468236298), (Int.ofNat 85147842856376001917345346523), (Int.ofNat 10541311012292885241853458858), (Int.negOfNat 1019717193557500680503433820), (Int.negOfNat 58967161717345062849859212), (Int.ofNat 7342943854905508405811147), (Int.ofNat 201357468767106154527409), (Int.negOfNat 36007603889940338454999), (Int.negOfNat 393189669290221590083), (Int.ofNat 131892815460471064577), (Int.negOfNat 371104206031791780), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(64526821792661382274872306940118061/56294995342131200000000000000000000), (-982788176979284071995052673442813/14073748835532800000000000000000000), (-177885887773836424260402920970593/14073748835532800000000000000000000), (3807855854901950703376587181889/2251799813685248000000000000000000), (9200289714005485067038421956301/11258999068426240000000000000000000), (-438775051022720126455889925499/7036874417766400000000000000000000), (-527328946721600125248234118149/28147497671065600000000000000000000), (85147842856376001917345346523/56294995342131200000000000000000000), (5270655506146442620926729429/28147497671065600000000000000000000), (-50985859677875034025171691/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial143.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial143.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial143.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial143 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 55149142590053815472983873254487357), (Int.negOfNat 4599859225948960344234967591173448), (Int.ofNat 500681482690241628787950684131252), (Int.ofNat 214562035037650201091802030036391), (Int.negOfNat 21313933992228878431033841110573), (Int.negOfNat 6596781269326856597011801084269), (Int.ofNat 547234401155908356557932013863), (Int.ofNat 90313249427990497817422243488), (Int.negOfNat 8596677536052866510900911754), (Int.negOfNat 627020851368014777575198321), (Int.ofNat 78674082062223298034985965), (Int.ofNat 2372748077098694187658309), (Int.negOfNat 467345570107439601537397), (Int.negOfNat 3891243484186504890517), (Int.ofNat 1958059262789053381144), (Int.negOfNat 8976530949503047660), (Int.negOfNat 7162895380913155900), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(55149142590053815472983873254487357/56294995342131200000000000000000000), (-574982403243620043029370948896681/7036874417766400000000000000000000), (125170370672560407196987671032813/14073748835532800000000000000000000), (214562035037650201091802030036391/56294995342131200000000000000000000), (-21313933992228878431033841110573/56294995342131200000000000000000000), (-6596781269326856597011801084269/56294995342131200000000000000000000), (547234401155908356557932013863/56294995342131200000000000000000000), (2822289044624703056794445109/1759218604441600000000000000000000), (-4298338768026433255450455877/28147497671065600000000000000000000), (-627020851368014777575198321/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial143.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial143.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial143.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial143 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 49160671225222757326803034785482926), (Int.negOfNat 1096477511832336082628116590539251), (Int.ofNat 923450625753833898407490473440658), (Int.negOfNat 99207574937843400672301813202850), (Int.negOfNat 40217494902830815595282620840269), (Int.ofNat 3098820809832279989754152154776), (Int.ofNat 699807972686927896340170186447), (Int.negOfNat 60925016307503797388929079205), (Int.negOfNat 6099086340548374161725823554), (Int.ofNat 716504562591366284077948122), (Int.ofNat 26466780237981838727843156), (Int.negOfNat 5260848585263592823760404), (Int.negOfNat 32376692094762463101828), (Int.ofNat 26276503762175104039567), (Int.negOfNat 272246085030296656091), (Int.negOfNat 97180128825699225840), (Int.ofNat 2096578792926841800), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(24580335612611378663401517392741463/28147497671065600000000000000000000), (-1096477511832336082628116590539251/56294995342131200000000000000000000), (461725312876916949203745236720329/28147497671065600000000000000000000), (-1984151498756868013446036264057/1125899906842624000000000000000000), (-40217494902830815595282620840269/56294995342131200000000000000000000), (387352601229034998719269019347/7036874417766400000000000000000000), (699807972686927896340170186447/56294995342131200000000000000000000), (-12185003261500759477785815841/11258999068426240000000000000000000), (-3049543170274187080862911777/28147497671065600000000000000000000), (358252281295683142038974061/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial143.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial143.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial143.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial143 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 49359351647946496294289367551245403), (Int.ofNat 470330807402687139646059411378762), (Int.negOfNat 269566060733584465522735651654180), (Int.negOfNat 226033077207629174679730256064959), (Int.ofNat 11896643754497187376219948562069), (Int.ofNat 5153600915333774456669196686459), (Int.negOfNat 340170477653102866765946946880), (Int.negOfNat 55897723600434484933423588148), (Int.ofNat 5322071024947942577878061815), (Int.ofNat 288396696657675464319719348), (Int.negOfNat 49669947737934071578220987), (Int.negOfNat 274822900875779727186275), (Int.ofNat 301150720771367582875664), (Int.negOfNat 5520120452741624716563), (Int.negOfNat 1281279109444104548059), (Int.ofNat 40483301933737368570), (Int.ofNat 5419088517414569120), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(49359351647946496294289367551245403/56294995342131200000000000000000000), (235165403701343569823029705689381/28147497671065600000000000000000000), (-13478303036679223276136782582709/2814749767106560000000000000000000), (-226033077207629174679730256064959/56294995342131200000000000000000000), (11896643754497187376219948562069/56294995342131200000000000000000000), (5153600915333774456669196686459/56294995342131200000000000000000000), (-1063032742665946458643584209/175921860444160000000000000000000), (-13974430900108621233355897037/14073748835532800000000000000000000), (1064414204989588515575612363/11258999068426240000000000000000000), (72099174164418866079929837/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial143.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial143.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial143.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial143 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 47741279965644727856326478705195399), (Int.negOfNat 2611840767389519791032577771606883), (Int.negOfNat 1036856003371925630553845639662930), (Int.negOfNat 101417335455919629747128236249), (Int.ofNat 33850391230556627835770246242204), (Int.negOfNat 1039269642941310547156591594798), (Int.negOfNat 488075171584027143009195572854), (Int.ofNat 28199740365137023078849120896), (Int.ofNat 3165425074887093156260871688), (Int.negOfNat 363079464106094384757933989), (Int.negOfNat 3914419913609161223640696), (Int.ofNat 2785963198054344464868141), (Int.negOfNat 84478141833470617911872), (Int.negOfNat 14214144006348061472295), (Int.ofNat 723002697164962534406), (Int.ofNat 50440743372857284390), (Int.negOfNat 2950149948072598430), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(47741279965644727856326478705195399/56294995342131200000000000000000000), (-2611840767389519791032577771606883/56294995342131200000000000000000000), (-103685600337192563055384563966293/5629499534213120000000000000000000), (-101417335455919629747128236249/56294995342131200000000000000000000), (8462597807639156958942561560551/14073748835532800000000000000000000), (-519634821470655273578295797399/28147497671065600000000000000000000), (-244037585792013571504597786427/28147497671065600000000000000000000), (220310471602632992803508757/439804651110400000000000000000000), (395678134360886644532608961/7036874417766400000000000000000000), (-363079464106094384757933989/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial143.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial143.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial143.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial143 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 38850711165834884006268858819509840), (Int.negOfNat 5839074330209090296311360308951378), (Int.negOfNat 402359448541369040111842615694248), (Int.ofNat 170595772938756318989487908675798), (Int.ofNat 4200468622265986540711500490776), (Int.negOfNat 3802823747887250282216509585055), (Int.ofNat 37833471726628102707275470860), (Int.ofNat 34193423032805394406145109442), (Int.negOfNat 1482578389160033078978546693), (Int.negOfNat 82405210507358705602900545), (Int.ofNat 17168312939981421895120134), (Int.negOfNat 968521266995080987234140), (Int.negOfNat 112577803177644689401587), (Int.ofNat 10839005769570333062608), (Int.ofNat 488839273774927271926), (Int.negOfNat 57741010437002359623), (Int.negOfNat 2817127429619341520), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(485633889572936050078360735243873/703687441776640000000000000000000), (-2919537165104545148155680154475689/28147497671065600000000000000000000), (-50294931067671130013980326961781/7036874417766400000000000000000000), (85297886469378159494743954337899/28147497671065600000000000000000000), (525058577783248317588937561347/7036874417766400000000000000000000), (-760564749577450056443301917011/11258999068426240000000000000000000), (1891673586331405135363773543/2814749767106560000000000000000000), (17096711516402697203072554721/28147497671065600000000000000000000), (-1482578389160033078978546693/56294995342131200000000000000000000), (-16481042101471741120580109/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial143.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial143.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial143.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial143 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 26879799632233646760533646122944272), (Int.negOfNat 5550224250075139387818581641689458), (Int.ofNat 446986806765166337917285462112212), (Int.ofNat 74401997514741400615250676139142), (Int.negOfNat 23796477338925763704017982838256), (Int.negOfNat 1204613167850166984412609719886), (Int.ofNat 334429771182445987230686011613), (Int.ofNat 8427006630518237515536052851), (Int.negOfNat 1554738667185419856461649306), (Int.negOfNat 14194640467208713267233205), (Int.negOfNat 7000832467662314858628221), (Int.negOfNat 167056605685339029882416), (Int.ofNat 134566057862286675313402), (Int.ofNat 1327324904282080203276), (Int.negOfNat 884405997685452501223), (Int.negOfNat 3056025395251408240), (Int.ofNat 2936400740619945860), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(1679987477014602922533352882684017/3518437208883200000000000000000000), (-2775112125037569693909290820844729/28147497671065600000000000000000000), (111746701691291584479321365528053/14073748835532800000000000000000000), (37200998757370700307625338069571/28147497671065600000000000000000000), (-1487279833682860231501123927391/3518437208883200000000000000000000), (-602306583925083492206304859943/28147497671065600000000000000000000), (334429771182445987230686011613/56294995342131200000000000000000000), (8427006630518237515536052851/56294995342131200000000000000000000), (-777369333592709928230824653/28147497671065600000000000000000000), (-2838928093441742653446641/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial143.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial143.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial143.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial143 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 17765292998458473701296517719967824), (Int.negOfNat 3660982772615398295958343735019088), (Int.ofNat 308912498946077470662346820308991), (Int.negOfNat 108888561676907778633978357253841), (Int.negOfNat 15300308721960624353664533431100), (Int.ofNat 2743064407855483608811219232935), (Int.ofNat 250329059838508605294691712560), (Int.negOfNat 22916627927986466531291309725), (Int.negOfNat 2333359493982197251542175244), (Int.ofNat 7822119056159676998091597), (Int.ofNat 14999511447530719309955690), (Int.ofNat 1266598670272814370749323), (Int.negOfNat 74678104687715571151098), (Int.negOfNat 11473734760916484507782), (Int.ofNat 302608878259363569773), (Int.ofNat 59304944361228060090), (Int.ofNat 215166341824113920), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(1110330812403654606331032357497989/3518437208883200000000000000000000), (-228811423288462393497396483438693/3518437208883200000000000000000000), (308912498946077470662346820308991/56294995342131200000000000000000000), (-108888561676907778633978357253841/56294995342131200000000000000000000), (-153003087219606243536645334311/562949953421312000000000000000000), (548612881571096721762243846587/11258999068426240000000000000000000), (3129113247981357566183646407/703687441776640000000000000000000), (-916665117119458661251652389/2251799813685248000000000000000000), (-583339873495549312885543811/14073748835532800000000000000000000), (7822119056159676998091597/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial143.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial143.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial143.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial143 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 10663354033827069362926288626553997), (Int.negOfNat 3966646384777940113517809234915814), (Int.negOfNat 451445721541425178682575675641081), (Int.negOfNat 98215997007152700853832814723458), (Int.ofNat 18393491621675712454363334754441), (Int.ofNat 2939971606957689589848363310873), (Int.negOfNat 264027840626708566958588276257), (Int.negOfNat 40970725905541310485078632479), (Int.ofNat 1215535263135588269475458830), (Int.ofNat 359088771090689076459199245), (Int.ofNat 6339271861841936745256669), (Int.negOfNat 2241818512882508256657798), (Int.negOfNat 115510054311635779143622), (Int.ofNat 10618523813040758322092), (Int.ofNat 755120190798167181025), (Int.negOfNat 40820335154860852210), (Int.negOfNat 2922651533167293290), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(10663354033827069362926288626553997/56294995342131200000000000000000000), (-1983323192388970056758904617457907/28147497671065600000000000000000000), (-451445721541425178682575675641081/56294995342131200000000000000000000), (-49107998503576350426916407361729/28147497671065600000000000000000000), (18393491621675712454363334754441/56294995342131200000000000000000000), (2939971606957689589848363310873/56294995342131200000000000000000000), (-264027840626708566958588276257/56294995342131200000000000000000000), (-40970725905541310485078632479/56294995342131200000000000000000000), (121553526313558826947545883/5629499534213120000000000000000000), (71817754218137815291839849/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial143.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial143.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial143.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial143 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.ofNat 505279880168837266338590232873771), (Int.negOfNat 6194202948796267850451293172445452), (Int.negOfNat 451162233557824006748108823601830), (Int.ofNat 105444694620946149257727161518949), (Int.ofNat 23269381572478661966291628929954), (Int.negOfNat 2424166285763238652910966691461), (Int.negOfNat 476051800425691875615145942298), (Int.ofNat 22927047953790773585021119488), (Int.ofNat 5488296021933064542591849504), (Int.negOfNat 56843248955738033211379143), (Int.negOfNat 42048890986718424043403172), (Int.negOfNat 668363510384453380772400), (Int.ofNat 233590062071782701666256), (Int.ofNat 7589104631957084376300), (Int.negOfNat 978856500633050491761), (Int.negOfNat 42457130840591057350), (Int.ofNat 2382211676820229490), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(505279880168837266338590232873771/56294995342131200000000000000000000), (-1548550737199066962612823293111363/14073748835532800000000000000000000), (-45116223355782400674810882360183/5629499534213120000000000000000000), (105444694620946149257727161518949/56294995342131200000000000000000000), (11634690786239330983145814464977/28147497671065600000000000000000000), (-2424166285763238652910966691461/56294995342131200000000000000000000), (-238025900212845937807572971149/28147497671065600000000000000000000), (22389695267373802329122187/54975581388800000000000000000000), (171509250685408266955995297/1759218604441600000000000000000000), (-56843248955738033211379143/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial143.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial143.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial143.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial143 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 12575680788950451191515986911730724), (Int.negOfNat 6258687015538499774546205805537365), (Int.ofNat 456278804421980073314192957004006), (Int.ofNat 140187027132969116765210011627360), (Int.negOfNat 17760205953736633227070133955750), (Int.negOfNat 4200524044871718402270186757034), (Int.ofNat 284898926959954122845547379461), (Int.ofNat 64932743118198314643644121961), (Int.negOfNat 2034412325081461869322654350), (Int.negOfNat 617736374663223068538936018), (Int.ofNat 4488657300903031162063471), (Int.ofNat 4073962328108313318347762), (Int.ofNat 35290331505479523071841), (Int.negOfNat 19827474327463945197908), (Int.negOfNat 366420422165985293238), (Int.ofNat 75700916498470020550), (Int.ofNat 1178844669668706510), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-3143920197237612797878996727932681/14073748835532800000000000000000000), (-1251737403107699954909241161107473/11258999068426240000000000000000000), (228139402210990036657096478502003/28147497671065600000000000000000000), (876168919581056979782562572671/351843720888320000000000000000000), (-71040823814946532908280535823/225179981368524800000000000000000), (-2100262022435859201135093378517/28147497671065600000000000000000000), (284898926959954122845547379461/56294995342131200000000000000000000), (64932743118198314643644121961/56294995342131200000000000000000000), (-40688246501629237386453087/1125899906842624000000000000000000), (-308868187331611534269468009/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial143.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial143.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial143.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial143 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 22539302699611876520691728241600077), (Int.negOfNat 3575343366861209491741724095414877), (Int.ofNat 640798030074991864239559588504288), (Int.negOfNat 94696966318765420025629863350041), (Int.negOfNat 29030131423404163832366183306907), (Int.ofNat 2669403659591341076386930532976), (Int.ofNat 623944916376425410925714482739), (Int.negOfNat 32068244487971436890943499810), (Int.negOfNat 7511497597292143119316829406), (Int.ofNat 205016935708211639390668777), (Int.ofNat 59644487935924929419049553), (Int.negOfNat 653550138236055497604670), (Int.negOfNat 339212952475102345622996), (Int.negOfNat 7301445532063218623), (Int.ofNat 1446696320175155949210), (Int.ofNat 13469243667469231190), (Int.negOfNat 4107686263715279510), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-22539302699611876520691728241600077/56294995342131200000000000000000000), (-3575343366861209491741724095414877/56294995342131200000000000000000000), (20024938439843495757486237140759/1759218604441600000000000000000000), (-94696966318765420025629863350041/56294995342131200000000000000000000), (-29030131423404163832366183306907/56294995342131200000000000000000000), (166837728724458817274183158311/3518437208883200000000000000000000), (623944916376425410925714482739/56294995342131200000000000000000000), (-3206824448797143689094349981/5629499534213120000000000000000000), (-3755748798646071559658414703/28147497671065600000000000000000000), (205016935708211639390668777/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial143.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial143.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial143.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial143 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 28229366092868215456756651497946834), (Int.negOfNat 2765425472011683542987587766232786), (Int.negOfNat 294227282618952245467859033421416), (Int.negOfNat 149795936526926129867997471225545), (Int.ofNat 19267746346348723071850127262460), (Int.ofNat 4939902883507466553534462575935), (Int.negOfNat 356746105012790578200027028248), (Int.negOfNat 76895586622491372695968288488), (Int.ofNat 3635823857428117027016336868), (Int.ofNat 745944833450986807627938824), (Int.negOfNat 22596673689990152739649734), (Int.negOfNat 5020783179686345406952739), (Int.ofNat 89561757020731910983314), (Int.ofNat 24799859494731320583350), (Int.negOfNat 225426574454085587633), (Int.negOfNat 93285264572135804410), (Int.ofNat 1427699487277405280), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-14114683046434107728378325748973417/28147497671065600000000000000000000), (-1382712736005841771493793883116393/28147497671065600000000000000000000), (-36778410327369030683482379177677/7036874417766400000000000000000000), (-29959187305385225973599494245109/11258999068426240000000000000000000), (963387317317436153592506363123/2814749767106560000000000000000000), (987980576701493310706892515187/11258999068426240000000000000000000), (-44593263126598822275003378531/7036874417766400000000000000000000), (-9611948327811421586996036061/7036874417766400000000000000000000), (908955964357029256754084217/14073748835532800000000000000000000), (93243104181373350953492353/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial143.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial143.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial143.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial143 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 35700527375152753925928605945444473), (Int.negOfNat 4825797237150429784887818706080829), (Int.negOfNat 463116794368563816947300915582946), (Int.ofNat 111784692242982083055204543584443), (Int.ofNat 32315185412934457087040653334042), (Int.negOfNat 2981535759437983828863160905704), (Int.negOfNat 664606872053620627306431983966), (Int.ofNat 45240095830031027267900502589), (Int.ofNat 7983346531519908771875710719), (Int.negOfNat 411276224750502918623974429), (Int.negOfNat 64388645447636465975567779), (Int.ofNat 2428108840570610453852389), (Int.ofNat 372805599808893193943154), (Int.negOfNat 9912872483009567384066), (Int.negOfNat 1607441321203396285554), (Int.ofNat 27704376722980314860), (Int.ofNat 4093937056262626940), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-35700527375152753925928605945444473/56294995342131200000000000000000000), (-4825797237150429784887818706080829/56294995342131200000000000000000000), (-231558397184281908473650457791473/28147497671065600000000000000000000), (111784692242982083055204543584443/56294995342131200000000000000000000), (16157592706467228543520326667021/28147497671065600000000000000000000), (-372691969929747978607895113213/7036874417766400000000000000000000), (-332303436026810313653215991983/28147497671065600000000000000000000), (45240095830031027267900502589/56294995342131200000000000000000000), (7983346531519908771875710719/56294995342131200000000000000000000), (-411276224750502918623974429/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial143.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial143.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial143.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial143 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 45923648151387593762942427183003298), (Int.negOfNat 4641688485325171121826008717104094), (Int.ofNat 627289305580256516137313089876817), (Int.ofNat 181288757073611986462284060456670), (Int.negOfNat 18147012435273685500850518627444), (Int.negOfNat 4823666842782409052389797302335), (Int.ofNat 424810272273793343500128780850), (Int.ofNat 72486862780573673300610558732), (Int.negOfNat 5529318106429799701104171515), (Int.negOfNat 708847254315236325538912855), (Int.ofNat 44214943667356315166909497), (Int.ofNat 4874175082874030368965593), (Int.negOfNat 236936131305279571703074), (Int.negOfNat 24597573735067578456935), (Int.ofNat 903547234835511574316), (Int.ofNat 94598673840752149330), (Int.negOfNat 4029660575072632880), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-22961824075693796881471213591501649/28147497671065600000000000000000000), (-2320844242662585560913004358552047/28147497671065600000000000000000000), (627289305580256516137313089876817/56294995342131200000000000000000000), (18128875707361198646228406045667/5629499534213120000000000000000000), (-4536753108818421375212629656861/14073748835532800000000000000000000), (-964733368556481810477959460467/11258999068426240000000000000000000), (8496205445475866870002575617/1125899906842624000000000000000000), (18121715695143418325152639683/14073748835532800000000000000000000), (-1105863621285959940220834303/11258999068426240000000000000000000), (-141769450863047265107782571/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial143.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial143.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial143.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial143 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 51657525536282334626367007956543437), (Int.negOfNat 816647166610401149491335503789769), (Int.ofNat 1031718015842798351249527729122636), (Int.negOfNat 61139060252749605304152190989471), (Int.negOfNat 28887379879690203397017847762008), (Int.ofNat 2926515010472161198935890260695), (Int.ofNat 546114484878895434906699703356), (Int.negOfNat 58048081086718196412263155430), (Int.negOfNat 6545696523607951145831288956), (Int.ofNat 632167051679119597773659393), (Int.ofNat 54224189516284747825518909), (Int.negOfNat 4345213100770077918444012), (Int.negOfNat 324911455055897245538491), (Int.ofNat 20548907426408565006263), (Int.ofNat 1451600358704166752448), (Int.negOfNat 68838921136329882010), (Int.negOfNat 4080187848809974370), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-51657525536282334626367007956543437/56294995342131200000000000000000000), (-816647166610401149491335503789769/56294995342131200000000000000000000), (257929503960699587812381932280659/14073748835532800000000000000000000), (-61139060252749605304152190989471/56294995342131200000000000000000000), (-3610922484961275424627230970251/7036874417766400000000000000000000), (585303002094432239787178052139/11258999068426240000000000000000000), (136528621219723858726674925839/14073748835532800000000000000000000), (-5804808108671819641226315543/5629499534213120000000000000000000), (-1636424130901987786457822239/14073748835532800000000000000000000), (632167051679119597773659393/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial143.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial143.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial143.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial143 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 49995395256899941963465719172883508), (Int.ofNat 1960105317287575715611461421412055), (Int.ofNat 289434135617034451860079376059667), (Int.negOfNat 128017778038192326126730588577335), (Int.ofNat 12621725978180087161422655761296), (Int.ofNat 3229668608691161353960088657022), (Int.negOfNat 470712242059273600149705756097), (Int.negOfNat 48118489827571204867278555167), (Int.ofNat 7337083629430596717893813441), (Int.ofNat 488100850708087209553829492), (Int.negOfNat 65717713864129855731694345), (Int.negOfNat 3565238256921840625784572), (Int.ofNat 383710370931213181334868), (Int.ofNat 19030323854344319203864), (Int.negOfNat 1582416981599542648194), (Int.negOfNat 76892786676422965130), (Int.ofNat 6631621662867860480), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-12498848814224985490866429793220877/14073748835532800000000000000000000), (392021063457515143122292284282411/11258999068426240000000000000000000), (289434135617034451860079376059667/56294995342131200000000000000000000), (-25603555607638465225346117715467/11258999068426240000000000000000000), (788857873636255447588915985081/3518437208883200000000000000000000), (1614834304345580676980044328511/28147497671065600000000000000000000), (-470712242059273600149705756097/56294995342131200000000000000000000), (-48118489827571204867278555167/56294995342131200000000000000000000), (7337083629430596717893813441/56294995342131200000000000000000000), (122025212677021802388457373/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial143.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial143.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial143.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial143 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 45670522739190403797247859833047434), (Int.ofNat 2140234780021991354607469938422594), (Int.negOfNat 48116097886465518443950621419144), (Int.ofNat 14542023852892342449005202895090), (Int.ofNat 12408011890722258346734984133631), (Int.negOfNat 2781808739510541154992708393068), (Int.negOfNat 242628818012469939069030420251), (Int.ofNat 68674892463413023281636405172), (Int.ofNat 3062086174530925531103478772), (Int.negOfNat 834988039162079115133623754), (Int.negOfNat 29018695576024727327651787), (Int.ofNat 6126616318292977812338826), (Int.ofNat 197880420947843432339476), (Int.negOfNat 30336888299284552805943), (Int.negOfNat 966910910536500558916), (Int.ofNat 109144810258880146860), (Int.ofNat 3199118278758912600), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-22835261369595201898623929916523717/28147497671065600000000000000000000), (1070117390010995677303734969211297/28147497671065600000000000000000000), (-6014512235808189805493827677393/7036874417766400000000000000000000), (1454202385289234244900520289509/5629499534213120000000000000000000), (12408011890722258346734984133631/56294995342131200000000000000000000), (-695452184877635288748177098267/14073748835532800000000000000000000), (-242628818012469939069030420251/56294995342131200000000000000000000), (17168723115853255820409101293/14073748835532800000000000000000000), (765521543632731382775869693/14073748835532800000000000000000000), (-417494019581039557566811877/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial143.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial143.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial143.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial143 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 41363069165197763439978868281738435), (Int.ofNat 2282103337817495861851008700315709), (Int.ofNat 103788371678134999740883839209079), (Int.ofNat 2995419768982109731931192245360), (Int.negOfNat 10793891969505126480017473834599), (Int.negOfNat 279609195577651236187635734948), (Int.ofNat 498328320594657096445353215131), (Int.ofNat 3372333395489021477430824985), (Int.negOfNat 8874826437374332180981182018), (Int.negOfNat 90261664322549176949764656), (Int.ofNat 84555589958279876344667454), (Int.ofNat 1202200073449521410037150), (Int.negOfNat 510196300252918614524588), (Int.negOfNat 8733443076479308165174), (Int.ofNat 2149414460707572456920), (Int.ofNat 42180100041651126393), (Int.negOfNat 8357096249762910500), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-8272613833039552687995773656347687/11258999068426240000000000000000000), (2282103337817495861851008700315709/56294995342131200000000000000000000), (103788371678134999740883839209079/56294995342131200000000000000000000), (37442747112276371649139903067/703687441776640000000000000000000), (-10793891969505126480017473834599/56294995342131200000000000000000000), (-69902298894412809046908933737/14073748835532800000000000000000000), (498328320594657096445353215131/56294995342131200000000000000000000), (674466679097804295486164997/11258999068426240000000000000000000), (-4437413218687166090490591009/28147497671065600000000000000000000), (-5641354020159323559360291/3518437208883200000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial143.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial143.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial143.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial143 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 36511301986878013202347426685818424), (Int.ofNat 2453756357118692104862039220145895), (Int.negOfNat 53142979225250191299411799938143), (Int.negOfNat 28016801883070564481057607835304), (Int.ofNat 8071858229552467291061883857412), (Int.ofNat 2490792787500483614691311484973), (Int.negOfNat 237600721349829913144810341099), (Int.negOfNat 77018394506520528215911380848), (Int.ofNat 2331523332037069811690989280), (Int.ofNat 1008281986783849016963837260), (Int.negOfNat 8847627663306543788088295), (Int.negOfNat 7583966751211182880544693), (Int.negOfNat 7710652130613594682631), (Int.ofNat 38004003023350900266996), (Int.ofNat 244554242940178865866), (Int.negOfNat 140651581243114467770), (Int.negOfNat 1455311415260325820), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-4563912748359751650293428335727303/7036874417766400000000000000000000), (490751271423738420972407844029179/11258999068426240000000000000000000), (-53142979225250191299411799938143/56294995342131200000000000000000000), (-3502100235383820560132200979413/7036874417766400000000000000000000), (2017964557388116822765470964353/14073748835532800000000000000000000), (2490792787500483614691311484973/56294995342131200000000000000000000), (-237600721349829913144810341099/56294995342131200000000000000000000), (-4813649656657533013494461303/3518437208883200000000000000000000), (14572020825231686323068683/351843720888320000000000000000000), (50414099339192450848191863/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial143.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial143.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial143.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial143 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 31855616506903611638701966792069199), (Int.ofNat 2287003787874586272452663408241829), (Int.ofNat 71477978621763163641934154184721), (Int.ofNat 64195906450921794734425846357030), (Int.ofNat 3408823906966937808805152575486), (Int.negOfNat 4036774724946383061416082470468), (Int.negOfNat 511291445650843788192392244929), (Int.ofNat 60797253050698257333992941415), (Int.ofNat 10313948661530751276016426993), (Int.negOfNat 444373234961652464928653869), (Int.negOfNat 99922793175512096375967572), (Int.ofNat 1892334373698683025707140), (Int.ofNat 602726775331688199606764), (Int.negOfNat 4767228311565375625800), (Int.negOfNat 2541807192237689584446), (Int.ofNat 4569413665215040910), (Int.ofNat 9210667404908667130), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-31855616506903611638701966792069199/56294995342131200000000000000000000), (2287003787874586272452663408241829/56294995342131200000000000000000000), (71477978621763163641934154184721/56294995342131200000000000000000000), (6419590645092179473442584635703/5629499534213120000000000000000000), (1704411953483468904402576287743/28147497671065600000000000000000000), (-1009193681236595765354020617617/14073748835532800000000000000000000), (-511291445650843788192392244929/56294995342131200000000000000000000), (12159450610139651466798588283/11258999068426240000000000000000000), (10313948661530751276016426993/56294995342131200000000000000000000), (-444373234961652464928653869/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial143.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial143.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial143.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial143 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 26579389182826302465696925112243972), (Int.ofNat 3067537809059395111515269002894678), (Int.ofNat 149045166625273093190739423163025), (Int.negOfNat 103061253367135439307023615882634), (Int.negOfNat 42044202488969487316397935472649), (Int.negOfNat 2033325751443081934999502168946), (Int.ofNat 921366423417730861811366700061), (Int.ofNat 89584866240661148238755235245), (Int.negOfNat 9054814576122741595988435758), (Int.negOfNat 1170269091208833303716785444), (Int.ofNat 53591337653909406418167423), (Int.ofNat 8626503009085863995224572), (Int.negOfNat 215286348739261024657073), (Int.negOfNat 42621809870856350986200), (Int.ofNat 621022263837353950262), (Int.ofNat 154535050853797005970), (Int.negOfNat 1146649672534901780), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-6644847295706575616424231278060993/14073748835532800000000000000000000), (1533768904529697555757634501447339/28147497671065600000000000000000000), (5961806665010923727629576926521/2251799813685248000000000000000000), (-51530626683567719653511807941317/28147497671065600000000000000000000), (-42044202488969487316397935472649/56294995342131200000000000000000000), (-1016662875721540967499751084473/28147497671065600000000000000000000), (921366423417730861811366700061/56294995342131200000000000000000000), (17916973248132229647751047049/11258999068426240000000000000000000), (-4527407288061370797994217879/28147497671065600000000000000000000), (-292567272802208325929196361/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial143.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial143.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial143.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial143 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 21342808156561423862414467424105180), (Int.ofNat 1124334943184726912024909162420510), (Int.negOfNat 1380499832460935394061700553868175), (Int.negOfNat 344527788760720358690419916244033), (Int.ofNat 4171190131511566997561308748991), (Int.ofNat 10784832981043609112477279080931), (Int.ofNat 661355449949237417220800439102), (Int.negOfNat 136440814290956372227884863155), (Int.negOfNat 12309512503193844610669463906), (Int.ofNat 1017635198660549183578784954), (Int.ofNat 112100941779086725019022118), (Int.negOfNat 5164714337580188041594227), (Int.negOfNat 652346607271654287220972), (Int.ofNat 19242209245530290795876), (Int.ofNat 2694637539186750654204), (Int.negOfNat 53636186962100030560), (Int.negOfNat 9196918197456014560), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-1067140407828071193120723371205259/2814749767106560000000000000000000), (112433494318472691202490916242051/5629499534213120000000000000000000), (-55219993298437415762468022154727/2251799813685248000000000000000000), (-344527788760720358690419916244033/56294995342131200000000000000000000), (4171190131511566997561308748991/56294995342131200000000000000000000), (10784832981043609112477279080931/56294995342131200000000000000000000), (330677724974618708610400219551/28147497671065600000000000000000000), (-27288162858191274445576972631/11258999068426240000000000000000000), (-6154756251596922305334731953/28147497671065600000000000000000000), (508817599330274591789392477/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial143.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial143.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial143.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial143 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 26938172352576622524227163612527819), (Int.negOfNat 7479637611512571260675334205057216), (Int.negOfNat 2433997774568682287627590104464286), (Int.ofNat 134494965655784298515198176682605), (Int.ofNat 105029277339494302232779955881339), (Int.ofNat 4490962753910919889323595968292), (Int.negOfNat 1675810513539530764717080460817), (Int.negOfNat 119878320180695138188255498449), (Int.ofNat 15441941207596321327660641590), (Int.ofNat 1339399850465176247149117910), (Int.negOfNat 95623174520998015694897543), (Int.negOfNat 9170912509179250759267033), (Int.ofNat 430375981191782633250896), (Int.ofNat 43567231290094980990901), (Int.negOfNat 1478007471347789115756), (Int.negOfNat 154427057712767818790), (Int.ofNat 3748610760330129380), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-26938172352576622524227163612527819/56294995342131200000000000000000000), (-116869337679883925948052096954019/879609302220800000000000000000000), (-1216998887284341143813795052232143/28147497671065600000000000000000000), (26898993131156859703039635336521/11258999068426240000000000000000000), (105029277339494302232779955881339/56294995342131200000000000000000000), (1122740688477729972330898992073/14073748835532800000000000000000000), (-1675810513539530764717080460817/56294995342131200000000000000000000), (-119878320180695138188255498449/56294995342131200000000000000000000), (1544194120759632132766064159/5629499534213120000000000000000000), (133939985046517624714911791/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial143.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial143.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial143.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial143 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 48851371700665828003789883141784327), (Int.negOfNat 12238618007773346906999332328040160), (Int.ofNat 802718394528379175995489545903417), (Int.ofNat 852182443842558847915376856076945), (Int.ofNat 36915801386053559870991966864973), (Int.negOfNat 17056552746182782120333898202501), (Int.negOfNat 1147877653630864124526619134847), (Int.ofNat 194666090467281392415983630215), (Int.ofNat 15043368893014830774872801010), (Int.negOfNat 1470538612683394699603063141), (Int.negOfNat 119558495888535482028431913), (Int.ofNat 7933466467148052385261460), (Int.ofNat 650351727022827737336375), (Int.negOfNat 32133899262910484744181), (Int.negOfNat 2588635086639594075277), (Int.ofNat 99194602831491404510), (Int.ofNat 9183168990003361990), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-48851371700665828003789883141784327/56294995342131200000000000000000000), (-76491362548583418168745827050251/351843720888320000000000000000000), (802718394528379175995489545903417/56294995342131200000000000000000000), (170436488768511769583075371215389/11258999068426240000000000000000000), (36915801386053559870991966864973/56294995342131200000000000000000000), (-17056552746182782120333898202501/56294995342131200000000000000000000), (-1147877653630864124526619134847/56294995342131200000000000000000000), (38933218093456278483196726043/11258999068426240000000000000000000), (1504336889301483077487280101/5629499534213120000000000000000000), (-1470538612683394699603063141/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial143.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial143.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial143.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial143 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 63300983994825474178681310494584984), (Int.ofNat 893551735802374756964476811515783), (Int.ofNat 5311658571523138966496185094022756), (Int.ofNat 408212260859413096531216204336129), (Int.negOfNat 138299942658519049645791165814752), (Int.negOfNat 11380788045622574381452210253548), (Int.ofNat 2019402789195722327979788163441), (Int.ofNat 162738391070253411541298582587), (Int.negOfNat 19039214420356915045330679695), (Int.negOfNat 1463150762933976353520916490), (Int.ofNat 124654102666263167165979310), (Int.ofNat 9027001945089851251683544), (Int.negOfNat 597647775434729936496839), (Int.negOfNat 40446791010873774705777), (Int.ofNat 2182839193654562583680), (Int.ofNat 135897188872851702550), (Int.negOfNat 6345988778974472790), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-7912622999353184272335163811823123/7036874417766400000000000000000000), (893551735802374756964476811515783/56294995342131200000000000000000000), (1327914642880784741624046273505689/14073748835532800000000000000000000), (408212260859413096531216204336129/56294995342131200000000000000000000), (-4321873208078720301430973931711/1759218604441600000000000000000000), (-2845197011405643595363052563387/14073748835532800000000000000000000), (2019402789195722327979788163441/56294995342131200000000000000000000), (162738391070253411541298582587/56294995342131200000000000000000000), (-3807842884071383009066135939/11258999068426240000000000000000000), (-146315076293397635352091649/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial143.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial143.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial143.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial143.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial143 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial143 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial143 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 71504094358130680995508939325449424), (Int.negOfNat 1262661387003002427332561607027780), (Int.ofNat 5653937473878146860980458069973810), (Int.negOfNat 548527987040982291862115145778200), (Int.negOfNat 145958601341880253006808766713401), (Int.ofNat 15550229781225896598933518526755), (Int.ofNat 2126062774486263544291213465375), (Int.negOfNat 215599956060640027554551547607), (Int.negOfNat 19929812578806973711502173519), (Int.ofNat 1844739015997891072805243207), (Int.ofNat 129498310993473903361656944), (Int.negOfNat 10813011394778612051416124), (Int.negOfNat 616021015670188698693031), (Int.ofNat 46320553801510788095415), (Int.ofNat 2233300853232935988680), (Int.negOfNat 151035686746363724050), (Int.negOfNat 6345988778974472790), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-4469005897383167562219308707840589/3518437208883200000000000000000000), (-63133069350150121366628080351389/2814749767106560000000000000000000), (565393747387814686098045806997381/5629499534213120000000000000000000), (-2742639935204911459310575728891/281474976710656000000000000000000), (-145958601341880253006808766713401/56294995342131200000000000000000000), (3110045956245179319786703705351/11258999068426240000000000000000000), (17008502195890108354329707723/450359962737049600000000000000000), (-215599956060640027554551547607/56294995342131200000000000000000000), (-19929812578806973711502173519/56294995342131200000000000000000000), (1844739015997891072805243207/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial143.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial143.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial143.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 57535199355062636760798881115375767), (Int.ofNat 11640082003883775427794782793272485), (Int.ofNat 443093516004196219468261551095813), (Int.negOfNat 899072554962655578761774669325252), (Int.ofNat 63080513272049017913476026865190), (Int.ofNat 18422171643786895664438865065833), (Int.negOfNat 1634521654546424136761351747324), (Int.negOfNat 211430334278705539306718876514), (Int.ofNat 19630053140286845204638717227), (Int.ofNat 1589607990384828954600653101), (Int.negOfNat 145971173491575289403779208), (Int.negOfNat 8486552303222408822974492), (Int.ofNat 753248035898743027922630), (Int.ofNat 33946799643051263570424), (Int.negOfNat 2879772452431219872719), (Int.negOfNat 104240768789328745010), (Int.ofNat 9183168990003361990), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-57535199355062636760798881115375767/56294995342131200000000000000000000), (2328016400776755085558956558654497/11258999068426240000000000000000000), (443093516004196219468261551095813/56294995342131200000000000000000000), (-224768138740663894690443667331313/14073748835532800000000000000000000), (6308051327204901791347602686519/5629499534213120000000000000000000), (18422171643786895664438865065833/56294995342131200000000000000000000), (-408630413636606034190337936831/14073748835532800000000000000000000), (-105715167139352769653359438257/28147497671065600000000000000000000), (19630053140286845204638717227/56294995342131200000000000000000000), (1589607990384828954600653101/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial143.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial143.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial143.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 38202440855338312914978241709528737), (Int.ofNat 5730327251739653419001191759847538), (Int.negOfNat 2457365560927533460989950875062114), (Int.ofNat 3748651021817987986361747880713), (Int.ofNat 116209772756643100971444864833848), (Int.negOfNat 8297012292018668996569487291661), (Int.negOfNat 1894100196421654056302376052246), (Int.ofNat 168046456684006013382579465384), (Int.ofNat 17519832136369440272859383573), (Int.negOfNat 1687486828342186898106105191), (Int.negOfNat 107633121706314500680740624), (Int.ofNat 10801157407818757258515172), (Int.ofNat 477232038638822574907042), (Int.negOfNat 48930419776128242663269), (Int.negOfNat 1610991124111081340786), (Int.ofNat 166201444947721613290), (Int.ofNat 3748610760330129380), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-38202440855338312914978241709528737/56294995342131200000000000000000000), (2865163625869826709500595879923769/28147497671065600000000000000000000), (-1228682780463766730494975437531057/28147497671065600000000000000000000), (3748651021817987986361747880713/56294995342131200000000000000000000), (14526221594580387621430608104231/7036874417766400000000000000000000), (-8297012292018668996569487291661/56294995342131200000000000000000000), (-947050098210827028151188026123/28147497671065600000000000000000000), (21005807085500751672822433173/7036874417766400000000000000000000), (17519832136369440272859383573/56294995342131200000000000000000000), (-1687486828342186898106105191/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial143.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial143.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial143.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 35043585361258988946698463765623140), (Int.negOfNat 1273949957484524374585501068784649), (Int.negOfNat 628549105928724964357678589399795), (Int.ofNat 413761483610278446374069146564177), (Int.negOfNat 21484034824699029251982436443373), (Int.negOfNat 12980837257147787485824980790370), (Int.ofNat 1101504674268980936858726649061), (Int.ofNat 165372510282815744222373457652), (Int.negOfNat 16370650827748382375628435744), (Int.negOfNat 1230126914986388414930570365), (Int.ofNat 135285692277985585509309701), (Int.ofNat 6167028113174623108011442), (Int.negOfNat 742312951132234894543260), (Int.negOfNat 22546180209291776070747), (Int.ofNat 2948698790176066373675), (Int.ofNat 60364408239216484560), (Int.negOfNat 9196918197456014560), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-1752179268062949447334923188281157/2814749767106560000000000000000000), (-1273949957484524374585501068784649/56294995342131200000000000000000000), (-125709821185744992871535717879959/11258999068426240000000000000000000), (413761483610278446374069146564177/56294995342131200000000000000000000), (-21484034824699029251982436443373/56294995342131200000000000000000000), (-1298083725714778748582498079037/5629499534213120000000000000000000), (1101504674268980936858726649061/56294995342131200000000000000000000), (41343127570703936055593364413/14073748835532800000000000000000000), (-511582838367136949238388617/1759218604441600000000000000000000), (-246025382997277682986114073/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial143.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial143.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial143.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 37467729924375546485269565879671930), (Int.negOfNat 282243615928106912148957016330136), (Int.ofNat 642102317843553789175895864977842), (Int.negOfNat 42193758346911975563555724369428), (Int.negOfNat 60213276541281059083664193130005), (Int.ofNat 5508268344894271317533955618591), (Int.ofNat 1255800119942810699935989228988), (Int.negOfNat 131202916487336429079457461265), (Int.negOfNat 12239885143359385616224095360), (Int.ofNat 1463739958787316968530559644), (Int.ofNat 72033495565647100953898669), (Int.negOfNat 9985631683236863134807996), (Int.negOfNat 287311937796754277601651), (Int.ofNat 47068815947063466670379), (Int.ofNat 824702881280490071557), (Int.negOfNat 166309438088750800470), (Int.negOfNat 1146649672534901780), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-3746772992437554648526956587967193/5629499534213120000000000000000000), (-35280451991013364018619627041267/7036874417766400000000000000000000), (321051158921776894587947932488921/28147497671065600000000000000000000), (-10548439586727993890888931092357/14073748835532800000000000000000000), (-12042655308256211816732838626001/11258999068426240000000000000000000), (5508268344894271317533955618591/56294995342131200000000000000000000), (313950029985702674983997307247/14073748835532800000000000000000000), (-26240583297467285815891492253/11258999068426240000000000000000000), (-19124820536499040025350149/87960930222080000000000000000000), (365934989696829242132639911/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial143.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial143.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial143.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 36527260002078879120550712407764390), (Int.ofNat 467102536916613352313804273526269), (Int.negOfNat 416945796830113463933900294621183), (Int.negOfNat 189513290103998994826824569416224), (Int.ofNat 26201267530361793573256044731164), (Int.ofNat 7296596543793182517029638608430), (Int.negOfNat 880311113621584831693291307496), (Int.negOfNat 101856272189698112528201049042), (Int.ofNat 13578494932292801145541671650), (Int.ofNat 740818901074491325493683863), (Int.negOfNat 118177522866911257427290498), (Int.negOfNat 3280189451764866797905565), (Int.ofNat 672881896837446230475431), (Int.ofNat 9328896798878462452761), (Int.negOfNat 2736895224511994072887), (Int.negOfNat 16343800900168835410), (Int.ofNat 9210667404908667130), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-3652726000207887912055071240776439/5629499534213120000000000000000000), (467102536916613352313804273526269/56294995342131200000000000000000000), (-416945796830113463933900294621183/56294995342131200000000000000000000), (-5922290315749968588338267794257/1759218604441600000000000000000000), (6550316882590448393314011182791/14073748835532800000000000000000000), (729659654379318251702963860843/5629499534213120000000000000000000), (-110038889202698103961661413437/7036874417766400000000000000000000), (-50928136094849056264100524521/28147497671065600000000000000000000), (271569898645856022910833433/1125899906842624000000000000000000), (740818901074491325493683863/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial143.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial143.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial143.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 38189880130502140545250552214524379), (Int.negOfNat 2252337262170071120289049590094152), (Int.negOfNat 594850945097792484339880467010332), (Int.ofNat 140509458690959752481981830155445), (Int.ofNat 34382739812238280179161700005845), (Int.negOfNat 5227871954038251996125261446892), (Int.negOfNat 693484835540422780260726568538), (Int.ofNat 108205110665151485548857258743), (Int.ofNat 6512479108021180001371678678), (Int.negOfNat 1222016424071183372386653520), (Int.negOfNat 32632443459274079491957612), (Int.ofNat 8560225047567203232162627), (Int.ofNat 84430324869996503082909), (Int.negOfNat 41177140172788860617779), (Int.negOfNat 14613943531119549223), (Int.ofNat 147369674266206695917), (Int.negOfNat 1455311415260325820), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-38189880130502140545250552214524379/56294995342131200000000000000000000), (-281542157771258890036131198761769/7036874417766400000000000000000000), (-148712736274448121084970116752583/14073748835532800000000000000000000), (28101891738191950496396366031089/11258999068426240000000000000000000), (6876547962447656035832340001169/11258999068426240000000000000000000), (-1306967988509562999031315361723/14073748835532800000000000000000000), (-346742417770211390130363284269/28147497671065600000000000000000000), (108205110665151485548857258743/56294995342131200000000000000000000), (3256239554010590000685839339/28147497671065600000000000000000000), (-15275205300889792154833169/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial143.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial143.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial143.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 43596557955768758144341050685947983), (Int.negOfNat 2344500307575119872243002966830328), (Int.ofNat 567342963530628782807647852212112), (Int.ofNat 161052637915450118545126446649531), (Int.negOfNat 26921831269764890892675051346133), (Int.negOfNat 4021091867035445985085428330629), (Int.ofNat 742788634293698363998547281903), (Int.ofNat 48141826886944912274489506448), (Int.negOfNat 10976390814752231768552326054), (Int.negOfNat 271933121504105853539739721), (Int.ofNat 96147528657081364178083105), (Int.ofNat 472495893239148630673689), (Int.negOfNat 554456610619355549624357), (Int.ofNat 3262086332490518433103), (Int.ofNat 2272082959966657032184), (Int.negOfNat 28713529233393992540), (Int.negOfNat 8357096249762910500), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-43596557955768758144341050685947983/56294995342131200000000000000000000), (-293062538446889984030375370853791/7036874417766400000000000000000000), (35458935220664298925477990763257/3518437208883200000000000000000000), (161052637915450118545126446649531/56294995342131200000000000000000000), (-26921831269764890892675051346133/56294995342131200000000000000000000), (-4021091867035445985085428330629/56294995342131200000000000000000000), (742788634293698363998547281903/56294995342131200000000000000000000), (3008864180434057017155594153/3518437208883200000000000000000000), (-5488195407376115884276163027/28147497671065600000000000000000000), (-271933121504105853539739721/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial143.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial143.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial143.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 45236341198613781957574572925207794), (Int.ofNat 827118244967397653168688873526989), (Int.ofNat 756630095280424934542486636350278), (Int.negOfNat 89054788040609677148062591618030), (Int.negOfNat 21230392692696317733197556334169), (Int.ofNat 4207003973714694408884897917456), (Int.ofNat 304273686670562195384856556287), (Int.negOfNat 84619923768953862117652237565), (Int.negOfNat 1804275610880380192396658654), (Int.ofNat 944195266239783522580506522), (Int.negOfNat 1725323494289648645722504), (Int.negOfNat 6625689996677130364079384), (Int.ofNat 92844661486503647356412), (Int.ofNat 31963551972869445674747), (Int.negOfNat 674182643711813680651), (Int.negOfNat 114190976216717487360), (Int.ofNat 3199118278758912600), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-22618170599306890978787286462603897/28147497671065600000000000000000000), (827118244967397653168688873526989/56294995342131200000000000000000000), (378315047640212467271243318175139/28147497671065600000000000000000000), (-8905478804060967714806259161803/5629499534213120000000000000000000), (-21230392692696317733197556334169/56294995342131200000000000000000000), (262937748357168400555306119841/3518437208883200000000000000000000), (304273686670562195384856556287/56294995342131200000000000000000000), (-16923984753790772423530447513/11258999068426240000000000000000000), (-902137805440190096198329327/28147497671065600000000000000000000), (472097633119891761290253261/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial143.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial143.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial143.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 41464435797228072798600837103637857), (Int.ofNat 2462928005965548857123951077002522), (Int.ofNat 66415530146647371879448391746380), (Int.negOfNat 87765654308803493269049484497859), (Int.ofNat 16908125220171550720774898740249), (Int.ofNat 1654513180022211935413119209259), (Int.negOfNat 540001991874313311188087508920), (Int.negOfNat 8760580685801462108469723768), (Int.ofNat 7976762842076869481480356435), (Int.negOfNat 92392144348047516996268352), (Int.negOfNat 69380836971423103035232187), (Int.ofNat 1744269164511430809903045), (Int.ofNat 397963263866103224301964), (Int.negOfNat 13091888525162753880983), (Int.negOfNat 1622634385451877984399), (Int.ofNat 61754288802910943630), (Int.ofNat 6631621662867860480), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-41464435797228072798600837103637857/56294995342131200000000000000000000), (1231464002982774428561975538501261/28147497671065600000000000000000000), (3320776507332368593972419587319/2814749767106560000000000000000000), (-87765654308803493269049484497859/56294995342131200000000000000000000), (16908125220171550720774898740249/56294995342131200000000000000000000), (1654513180022211935413119209259/56294995342131200000000000000000000), (-13500049796857832779702187723/1407374883553280000000000000000000), (-1095072585725182763558715471/7036874417766400000000000000000000), (1595352568415373896296071287/11258999068426240000000000000000000), (-1443627255438242453066693/879609302220800000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial143.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial143.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial143.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 36685321184428690352112522413449081), (Int.ofNat 2248846879169227010600519353871717), (Int.negOfNat 44367196500334528202853073262690), (Int.ofNat 35219193653229826273023828333331), (Int.ofNat 6346999698765347605346370532604), (Int.negOfNat 2647392111413394171047778848598), (Int.negOfNat 19070785446536558609484948934), (Int.ofNat 56227510381597532895215611236), (Int.negOfNat 1507884398604113576661283212), (Int.negOfNat 624228336933025906916151409), (Int.ofNat 25927172387619578943963804), (Int.ofNat 4319212192568588248246281), (Int.negOfNat 215930978276281899953432), (Int.negOfNat 20478310035826270226215), (Int.ofNat 1147209115438792564066), (Int.ofNat 68838921136329882010), (Int.negOfNat 4080187848809974370), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-36685321184428690352112522413449081/56294995342131200000000000000000000), (2248846879169227010600519353871717/56294995342131200000000000000000000), (-4436719650033452820285307326269/5629499534213120000000000000000000), (35219193653229826273023828333331/56294995342131200000000000000000000), (1586749924691336901336592633151/14073748835532800000000000000000000), (-1323696055706697085523889424299/28147497671065600000000000000000000), (-9535392723268279304742474467/28147497671065600000000000000000000), (14056877595399383223803902809/14073748835532800000000000000000000), (-376971099651028394165320803/14073748835532800000000000000000000), (-624228336933025906916151409/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial143.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial143.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial143.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 32061201883759486127908229597103600), (Int.ofNat 2504042224457052027747064724202702), (Int.ofNat 135516838385649571827774484160952), (Int.ofNat 3028935132924861103847998608598), (Int.negOfNat 9235804046898941628233583413404), (Int.ofNat 222390598078700717881873118065), (Int.ofNat 314474726062631787880286315520), (Int.negOfNat 17222606122834119559224421178), (Int.negOfNat 4667096731845543357469536653), (Int.ofNat 319046220529029766317362035), (Int.ofNat 39692966088948013275955074), (Int.negOfNat 3068664583746262303099640), (Int.negOfNat 220110593879241048339527), (Int.ofNat 18691738010549793283508), (Int.ofNat 858030458674733251286), (Int.negOfNat 79470304221264353683), (Int.negOfNat 4029660575072632880), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-80153004709398715319770573992759/140737488355328000000000000000000), (1252021112228526013873532362101351/28147497671065600000000000000000000), (16939604798206196478471810520119/7036874417766400000000000000000000), (1514467566462430551923999304299/28147497671065600000000000000000000), (-2308951011724735407058395853351/14073748835532800000000000000000000), (44478119615740143576374623613/11258999068426240000000000000000000), (61420844934107771070368421/10995116277760000000000000000000), (-8611303061417059779612210589/28147497671065600000000000000000000), (-4667096731845543357469536653/56294995342131200000000000000000000), (63809244105805953263472407/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial143.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial143.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial143.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 26610550878154167004546042421740948), (Int.ofNat 2853486039967597798780138458624122), (Int.ofNat 7188678998607629336506020401232), (Int.negOfNat 27477591132657050831176605404098), (Int.ofNat 3476952737353796200519401800584), (Int.ofNat 1315543524050530301365127124814), (Int.negOfNat 155422481496185644345391583087), (Int.negOfNat 27338507962816852635179982569), (Int.ofNat 3291404637436754340117868374), (Int.ofNat 291904396053371397943391655), (Int.negOfNat 37639074608473919758062761), (Int.negOfNat 1890278128858102944209036), (Int.ofNat 269062866472663616916722), (Int.ofNat 8176141208760315625116), (Int.negOfNat 1316577418270424586143), (Int.negOfNat 22658210765142974360), (Int.ofNat 4093937056262626940), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-6652637719538541751136510605435237/14073748835532800000000000000000000), (1426743019983798899390069229312061/28147497671065600000000000000000000), (449292437412976833531626275077/3518437208883200000000000000000000), (-13738795566328525415588302702049/28147497671065600000000000000000000), (434619092169224525064925225073/7036874417766400000000000000000000), (657771762025265150682563562407/28147497671065600000000000000000000), (-155422481496185644345391583087/56294995342131200000000000000000000), (-27338507962816852635179982569/56294995342131200000000000000000000), (1645702318718377170058934187/28147497671065600000000000000000000), (58380879210674279588678331/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial143.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial143.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial143.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 21009411754740306173882137219248816), (Int.ofNat 2730762698281773011492789210228452), (Int.negOfNat 17883947636250542998312438792129), (Int.ofNat 19623794883773429789274498591959), (Int.ofNat 3965572968028908040751862182860), (Int.negOfNat 1113764836934336884679864024765), (Int.negOfNat 111111805238346857322512761500), (Int.ofNat 28367142045816965548793535795), (Int.ofNat 1484269415027046624638839276), (Int.negOfNat 395367487000698115508200083), (Int.negOfNat 10629461430277512491027990), (Int.ofNat 3378940637819922395343903), (Int.ofNat 43691305914156856764302), (Int.negOfNat 19399014522811337471782), (Int.negOfNat 97570113680824509927), (Int.ofNat 81510877337182009910), (Int.ofNat 1427699487277405280), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-1313088234671269135867633576203051/3518437208883200000000000000000000), (682690674570443252873197302557113/14073748835532800000000000000000000), (-17883947636250542998312438792129/56294995342131200000000000000000000), (19623794883773429789274498591959/56294995342131200000000000000000000), (198278648401445402037593109143/2814749767106560000000000000000000), (-222752967386867376935972804953/11258999068426240000000000000000000), (-222223610476693714645025523/112589990684262400000000000000000), (5673428409163393109758707159/11258999068426240000000000000000000), (371067353756761656159709819/14073748835532800000000000000000000), (-395367487000698115508200083/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial143.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial143.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial143.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 15437929656839336852847753304728363), (Int.ofNat 2924477259775007453861657709708606), (Int.ofNat 99137816302288256253874607966919), (Int.ofNat 5418586082893120261037922428782), (Int.negOfNat 5829299320100794147338882054139), (Int.negOfNat 184000580933986870969637485627), (Int.ofNat 199268098531349745588383858223), (Int.ofNat 1881536831008132441406626961), (Int.negOfNat 3493544200639052116708876430), (Int.ofNat 8482593783965495743178805), (Int.ofNat 36446190351989193110251389), (Int.negOfNat 336434681541981102636098), (Int.negOfNat 248713661261951280745122), (Int.ofNat 3244376777044249056912), (Int.ofNat 1189493780135814971505), (Int.negOfNat 20197464944585685190), (Int.negOfNat 4107686263715279510), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-15437929656839336852847753304728363/56294995342131200000000000000000000), (1462238629887503726930828854854303/28147497671065600000000000000000000), (99137816302288256253874607966919/56294995342131200000000000000000000), (2709293041446560130518961214391/28147497671065600000000000000000000), (-5829299320100794147338882054139/56294995342131200000000000000000000), (-184000580933986870969637485627/56294995342131200000000000000000000), (199268098531349745588383858223/56294995342131200000000000000000000), (1881536831008132441406626961/56294995342131200000000000000000000), (-349354420063905211670887643/5629499534213120000000000000000000), (1696518756793099148635761/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial143.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial143.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial143.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 9236092341941688480124653765831109), (Int.ofNat 3220515496706194349532389142183148), (Int.ofNat 20288011736777989445628425889110), (Int.negOfNat 21334730140699196984941626275251), (Int.ofNat 1381481322752579044209486551174), (Int.ofNat 1078199134581379907109142475379), (Int.negOfNat 55639308096442627869950001818), (Int.negOfNat 25057782612425830835310997232), (Int.ofNat 1140711447141215648934949624), (Int.ofNat 327826503810822701019397117), (Int.negOfNat 13720607045156399082693392), (Int.negOfNat 2712014380059002820984720), (Int.ofNat 106101941615609802490916), (Int.ofNat 15345322217058281498160), (Int.negOfNat 558867277167488321061), (Int.negOfNat 63926529263516226050), (Int.ofNat 1178844669668706510), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-9236092341941688480124653765831109/56294995342131200000000000000000000), (805128874176548587383097285545787/14073748835532800000000000000000000), (2028801173677798944562842588911/5629499534213120000000000000000000), (-21334730140699196984941626275251/56294995342131200000000000000000000), (690740661376289522104743275587/28147497671065600000000000000000000), (1078199134581379907109142475379/56294995342131200000000000000000000), (-27819654048221313934975000909/28147497671065600000000000000000000), (-1566111413276614427206937327/3518437208883200000000000000000000), (142588930892651956116868703/7036874417766400000000000000000000), (327826503810822701019397117/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial143.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial143.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial143.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 2834308566823742131659634026977884), (Int.ofNat 3156031429964942764933663862018255), (Int.negOfNat 15171440872129797438070932487074), (Int.ofNat 13407602371305941602077418986920), (Int.ofNat 4127694295996869270893769537230), (Int.negOfNat 698158624527100482849345035714), (Int.negOfNat 135513565369295124899648561019), (Int.ofNat 16947912551981710223312005241), (Int.ofNat 2313172249710387024334245530), (Int.negOfNat 233066621896662334308159758), (Int.negOfNat 23839626640658993798646309), (Int.ofNat 2030311458433763878135442), (Int.ofNat 162778451961652422247181), (Int.negOfNat 12071256742362748076048), (Int.negOfNat 786409645631547463938), (Int.ofNat 54231518075544851850), (Int.ofNat 2382211676820229490), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-708577141705935532914908506744471/14073748835532800000000000000000000), (631206285992988552986732772403651/11258999068426240000000000000000000), (-7585720436064898719035466243537/28147497671065600000000000000000000), (335190059282648540051935474673/1407374883553280000000000000000000), (412769429599686927089376953723/5629499534213120000000000000000000), (-349079312263550241424672517857/28147497671065600000000000000000000), (-135513565369295124899648561019/56294995342131200000000000000000000), (16947912551981710223312005241/56294995342131200000000000000000000), (231317224971038702433424553/5629499534213120000000000000000000), (-116533310948331167154079879/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial143.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial143.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial143.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 3561980991074224826533743346069043), (Int.ofNat 3315780277694134416887565158646643), (Int.ofNat 90214492231581134312583270415648), (Int.ofNat 8937616771265528868871023766539), (Int.negOfNat 4807340481621394100520957061567), (Int.negOfNat 454568528299848847930170127224), (Int.ofNat 160648977218367098378742348259), (Int.ofNat 10784018248578006035541759630), (Int.negOfNat 2802418133517502733132494146), (Int.negOfNat 145589241598511941325351663), (Int.ofNat 29537569445777673054054833), (Int.ofNat 1251833693104471656417030), (Int.negOfNat 206009345524786844021496), (Int.negOfNat 7381448481528572483803), (Int.ofNat 1012322730837508158730), (Int.ofNat 34092113877744398210), (Int.negOfNat 2922651533167293290), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(3561980991074224826533743346069043/56294995342131200000000000000000000), (3315780277694134416887565158646643/56294995342131200000000000000000000), (2819202882236910447268227200489/1759218604441600000000000000000000), (8937616771265528868871023766539/56294995342131200000000000000000000), (-4807340481621394100520957061567/56294995342131200000000000000000000), (-56821066037481105991271265903/7036874417766400000000000000000000), (160648977218367098378742348259/56294995342131200000000000000000000), (1078401824857800603554175963/5629499534213120000000000000000000), (-1401209066758751366566247073/28147497671065600000000000000000000), (-145589241598511941325351663/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial143.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial143.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial143.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 10545338660356261941265473328208086), (Int.ofNat 3626319998889054828254328610674554), (Int.ofNat 32569163963618969487682538570804), (Int.negOfNat 21283579966241429132038635992025), (Int.ofNat 1864656360122601687452728940), (Int.ofNat 1083073638715340153550395724455), (Int.ofNat 4694760064064884417177445812), (Int.negOfNat 25611816648687940615883442968), (Int.negOfNat 181805051581126849164677652), (Int.ofNat 342755227394129015121647144), (Int.ofNat 3032299187818079061333946), (Int.negOfNat 2908441212139237382358159), (Int.negOfNat 28807653581140516932086), (Int.ofNat 16874579732836467619350), (Int.ofNat 174752417486102492067), (Int.negOfNat 71079331596181854590), (Int.ofNat 215166341824113920), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(5272669330178130970632736664104043/28147497671065600000000000000000000), (1813159999444527414127164305337277/28147497671065600000000000000000000), (8142290990904742371920634642701/14073748835532800000000000000000000), (-851343198649657165281545439681/2251799813685248000000000000000000), (93232818006130084372636447/2814749767106560000000000000000000), (216614727743068030710079144891/11258999068426240000000000000000000), (1173690016016221104294361453/14073748835532800000000000000000000), (-3201477081085992576985430371/7036874417766400000000000000000000), (-45451262895281712291169413/14073748835532800000000000000000000), (42844403424266126890205893/7036874417766400000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial143.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial143.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial143.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 17789823135268595959329794953872887), (Int.ofNat 3577913052896589781544331199575991), (Int.negOfNat 23318666601957284820708095171406), (Int.ofNat 9905103595526714166343672376023), (Int.ofNat 5041755336646639385192635160862), (Int.negOfNat 461379067537276736347854847104), (Int.negOfNat 174754619374979829592052620886), (Int.ofNat 9474581236695937117184467169), (Int.ofNat 3137203226897734575296193039), (Int.negOfNat 105177188229922807413349569), (Int.negOfNat 33750403306824861076133239), (Int.ofNat 704887317397846539525769), (Int.ofNat 238308791198516252339834), (Int.negOfNat 3064056178531331962226), (Int.negOfNat 1175269900618424200634), (Int.ofNat 8102191353088748740), (Int.ofNat 2936400740619945860), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(17789823135268595959329794953872887/56294995342131200000000000000000000), (3577913052896589781544331199575991/56294995342131200000000000000000000), (-11659333300978642410354047585703/28147497671065600000000000000000000), (9905103595526714166343672376023/56294995342131200000000000000000000), (2520877668323319692596317580431/28147497671065600000000000000000000), (-3604523965134974502717615993/439804651110400000000000000000000), (-87377309687489914796026310443/28147497671065600000000000000000000), (9474581236695937117184467169/56294995342131200000000000000000000), (3137203226897734575296193039/56294995342131200000000000000000000), (-105177188229922807413349569/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial143.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial143.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial143.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 24988264898248451988081932528019042), (Int.ofNat 3701428069344435849896325402370766), (Int.ofNat 89413018652784563628062952900857), (Int.ofNat 13721919267676501690549759803890), (Int.negOfNat 4710739766118684257694475237984), (Int.negOfNat 798452496814142979660129237055), (Int.ofNat 148169017937789658327117936190), (Int.ofNat 21070833624934159335241028112), (Int.negOfNat 2344799763744289422613181555), (Int.negOfNat 307395823278847853618650275), (Int.ofNat 21690290518389723786074557), (Int.ofNat 2774031766122849053100093), (Int.negOfNat 129403340603683212765134), (Int.negOfNat 16744841494088118236035), (Int.ofNat 534356049935705594956), (Int.ofNat 72869380056490155270), (Int.negOfNat 2817127429619341520), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(12494132449124225994040966264009521/28147497671065600000000000000000000), (1850714034672217924948162701185383/28147497671065600000000000000000000), (89413018652784563628062952900857/56294995342131200000000000000000000), (1372191926767650169054975980389/5629499534213120000000000000000000), (-147210617691208883052952351187/1759218604441600000000000000000000), (-159690499362828595932025847411/11258999068426240000000000000000000), (14816901793778965832711793619/5629499534213120000000000000000000), (1316927101558384958452564257/3518437208883200000000000000000000), (-468959952748857884522636311/11258999068426240000000000000000000), (-12295832931153914144746011/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial143.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial143.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial143.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 32769075613837078524088076133231943), (Int.ofNat 4044040479948710609225128800963931), (Int.ofNat 39229208970198363378455627417436), (Int.negOfNat 25818449264123825816922381079391), (Int.negOfNat 1383988347872555397600458014848), (Int.ofNat 1318392541998900425253921898015), (Int.ofNat 77110098741404850506989079436), (Int.negOfNat 30020311070257686595896665090), (Int.negOfNat 1872387050116744412909134056), (Int.ofNat 371018178852188075615441973), (Int.ofNat 24382597215056007657914409), (Int.negOfNat 2811964106255834135065872), (Int.negOfNat 193458618613085963496931), (Int.ofNat 14284741396930356252343), (Int.ofNat 1027393940430336722788), (Int.negOfNat 50440743372857284390), (Int.negOfNat 2950149948072598430), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(32769075613837078524088076133231943/56294995342131200000000000000000000), (4044040479948710609225128800963931/56294995342131200000000000000000000), (9807302242549590844613906854359/14073748835532800000000000000000000), (-25818449264123825816922381079391/56294995342131200000000000000000000), (-10812408967754339043753578241/439804651110400000000000000000000), (263678508399780085050784379603/11258999068426240000000000000000000), (19277524685351212626747269859/14073748835532800000000000000000000), (-3002031107025768659589666509/5629499534213120000000000000000000), (-234048381264593051613641757/7036874417766400000000000000000000), (371018178852188075615441973/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial143.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial143.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial143.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 40828392188317008691231931301228612), (Int.ofNat 3952702515846633622611788899595795), (Int.negOfNat 46547455264148869387044853354233), (Int.ofNat 10249644860701669743735663971625), (Int.ofNat 7610244512505102548437906234296), (Int.negOfNat 269419126622210730550503063758), (Int.negOfNat 270880727838063155727565194057), (Int.negOfNat 981346912938182042324690787), (Int.ofNat 4682391812301669814291518821), (Int.ofNat 107312009702364228237841792), (Int.negOfNat 46006824630640824274683145), (Int.negOfNat 1546146191534630088695252), (Int.ofNat 286897827836477539908568), (Int.ofNat 11458555781923190039444), (Int.negOfNat 1241061705591769211854), (Int.negOfNat 55621799807249390070), (Int.ofNat 5419088517414569120), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(10207098047079252172807982825307153/14073748835532800000000000000000000), (790540503169326724522357779919159/11258999068426240000000000000000000), (-46547455264148869387044853354233/56294995342131200000000000000000000), (81997158885613357949885311773/450359962737049600000000000000000), (951280564063137818554738279287/7036874417766400000000000000000000), (-134709563311105365275251531879/28147497671065600000000000000000000), (-270880727838063155727565194057/56294995342131200000000000000000000), (-981346912938182042324690787/56294995342131200000000000000000000), (4682391812301669814291518821/56294995342131200000000000000000000), (838375075799720533108139/439804651110400000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial143.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial143.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial143.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 48726489684677730014506978220659426), (Int.ofNat 4063830536815092831290220959682034), (Int.ofNat 118704432586453801443653177199956), (Int.ofNat 24694810750167280560223667680970), (Int.negOfNat 6579090319428586218788481256249), (Int.negOfNat 1673625575628107762986091648108), (Int.ofNat 152905468003895761886283209909), (Int.ofNat 44979985001962958552913246812), (Int.negOfNat 1232724555137068438225686128), (Int.negOfNat 607297335513661876631065354), (Int.negOfNat 826591843753239954086127), (Int.ofNat 4761774906879440272019846), (Int.ofNat 72659067366577321881236), (Int.negOfNat 24649840088590211170763), (Int.negOfNat 564974351854983534356), (Int.ofNat 92133962867861885340), (Int.ofNat 2096578792926841800), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(24363244842338865007253489110329713/28147497671065600000000000000000000), (2031915268407546415645110479841017/28147497671065600000000000000000000), (29676108146613450360913294299989/14073748835532800000000000000000000), (2469481075016728056022366768097/5629499534213120000000000000000000), (-6579090319428586218788481256249/56294995342131200000000000000000000), (-418406393907026940746522912027/14073748835532800000000000000000000), (152905468003895761886283209909/56294995342131200000000000000000000), (11244996250490739638228311703/14073748835532800000000000000000000), (-77045284696066777389105383/3518437208883200000000000000000000), (-303648667756830938315532677/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial143.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial143.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial143.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 57382631380641290515867749625601565), (Int.ofNat 4537462256182782039490532207888909), (Int.ofNat 37126890837249134985834131658099), (Int.negOfNat 50513977353254444860935694922040), (Int.negOfNat 5185994691960279882433315622159), (Int.ofNat 2296080206717223459146630739072), (Int.ofNat 302774087456867089004737947091), (Int.negOfNat 38799089145556564065501912055), (Int.negOfNat 6495113158674966923329767718), (Int.ofNat 264826065541359747085693944), (Int.ofNat 67082143363421810201570314), (Int.negOfNat 698052110410024146947470), (Int.negOfNat 423085259741002666437628), (Int.negOfNat 1580113259802284841554), (Int.ofNat 1835390763529968805880), (Int.ofNat 22443101757760181513), (Int.negOfNat 7162895380913155900), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(11476526276128258103173549925120313/11258999068426240000000000000000000), (4537462256182782039490532207888909/56294995342131200000000000000000000), (37126890837249134985834131658099/56294995342131200000000000000000000), (-1262849433831361121523392373051/1407374883553280000000000000000000), (-5185994691960279882433315622159/56294995342131200000000000000000000), (17938126614978308274583052649/439804651110400000000000000000000), (302774087456867089004737947091/56294995342131200000000000000000000), (-7759817829111312813100382411/11258999068426240000000000000000000), (-3247556579337483461664883859/28147497671065600000000000000000000), (33103258192669968385711743/7036874417766400000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial143.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial143.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial143.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 66205399936282768182134049850772456), (Int.ofNat 4132571802855260534475540610051775), (Int.negOfNat 169835585223127439924236381165623), (Int.ofNat 17296260435389936175470640011076), (Int.ofNat 19690566987360763322059949797392), (Int.ofNat 773121241643477314098829109593), (Int.negOfNat 598773779252607383380552008859), (Int.negOfNat 53961126697745044584399468628), (Int.ofNat 6360355236308775052172769460), (Int.ofNat 805982756270166325080617560), (Int.negOfNat 35182345921377527145989895), (Int.negOfNat 6366685558549488054193213), (Int.ofNat 109216491766496056761869), (Int.ofNat 32834466740502378104216), (Int.negOfNat 134021482818923174994), (Int.negOfNat 125174722437378836430), (Int.negOfNat 371104206031791780), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(8275674992035346022766756231346557/7036874417766400000000000000000000), (165302872114210421379021624402071/2251799813685248000000000000000000), (-169835585223127439924236381165623/56294995342131200000000000000000000), (4324065108847484043867660002769/14073748835532800000000000000000000), (1230660436710047707628746862337/3518437208883200000000000000000000), (773121241643477314098829109593/56294995342131200000000000000000000), (-598773779252607383380552008859/56294995342131200000000000000000000), (-13490281674436261146099867157/14073748835532800000000000000000000), (318017761815438752608638473/2814749767106560000000000000000000), (20149568906754158127015439/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial143.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial143.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial143.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 74226124248465391128913042751699281), (Int.ofNat 4221715806202463929372433209133029), (Int.ofNat 302937308288126527887698540265021), (Int.ofNat 94666588003169441321554021744550), (Int.negOfNat 13956844072238449049222040774834), (Int.negOfNat 6921183405008299143762139724368), (Int.negOfNat 299331709686189231132360045849), (Int.ofNat 102590856503784310117025172875), (Int.ofNat 8224051150668964098461447493), (Int.negOfNat 776940811755511312766097049), (Int.negOfNat 84589111410554952529274872), (Int.ofNat 3646531021386324171991400), (Int.ofNat 524122402578998021278724), (Int.negOfNat 11389298862989868457480), (Int.negOfNat 2256009473514031140906), (Int.ofNat 22919081576651649690), (Int.ofNat 8043964950964217670), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(74226124248465391128913042751699281/56294995342131200000000000000000000), (4221715806202463929372433209133029/56294995342131200000000000000000000), (302937308288126527887698540265021/56294995342131200000000000000000000), (1893331760063388826431080434891/1125899906842624000000000000000000), (-6978422036119224524611020387417/28147497671065600000000000000000000), (-432573962813018696485133732773/3518437208883200000000000000000000), (-299331709686189231132360045849/56294995342131200000000000000000000), (820726852030274480936201383/450359962737049600000000000000000), (8224051150668964098461447493/56294995342131200000000000000000000), (-776940811755511312766097049/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial143.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial143.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial143.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 84189455254180131805016805801309688), (Int.ofNat 5563890788400802249622848427042238), (Int.negOfNat 10302275877217595645683619499795), (Int.negOfNat 274808191202684682625181303292074), (Int.negOfNat 67247622718968738507935576224469), (Int.negOfNat 304570744027191179153016316886), (Int.ofNat 1332497868476488082962225216381), (Int.ofNat 71465950537953141750670726065), (Int.negOfNat 12882670591151613729529178998), (Int.negOfNat 1001202478728410400404076224), (Int.ofNat 77552873613281357636101683), (Int.ofNat 7542574021984559201471672), (Int.negOfNat 321667017670437134301133), (Int.negOfNat 37852165158206647519500), (Int.ofNat 970769394227484747702), (Int.ofNat 139516498963149793630), (Int.negOfNat 2230856881763435820), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(10523681906772516475627100725163711/7036874417766400000000000000000000), (2781945394200401124811424213521119/28147497671065600000000000000000000), (-2060455175443519129136723899959/11258999068426240000000000000000000), (-137404095601342341312590651646037/28147497671065600000000000000000000), (-67247622718968738507935576224469/56294995342131200000000000000000000), (-152285372013595589576508158443/28147497671065600000000000000000000), (1332497868476488082962225216381/56294995342131200000000000000000000), (14293190107590628350134145213/11258999068426240000000000000000000), (-6441335295575806864764589499/28147497671065600000000000000000000), (-15643788730131412506313691/879609302220800000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial143.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial143.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial143.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 92082564150480662755270025106598420), (Int.ofNat 321523769046138726602706049189590), (Int.negOfNat 2956256209184780371945634314230295), (Int.negOfNat 598756159179479673814224621396433), (Int.ofNat 12509220828772862605207345134471), (Int.ofNat 14703402329242220300270359230931), (Int.ofNat 563180571091972706724392362002), (Int.negOfNat 176228395585930132372112204335), (Int.negOfNat 10805866312775384577724916386), (Int.ofNat 1311249855291268774982969494), (Int.ofNat 98826547407404889776425058), (Int.negOfNat 6717734072270714691625207), (Int.negOfNat 579702063394934574371092), (Int.ofNat 25220263308930591344036), (Int.ofNat 2421768255158927767924), (Int.negOfNat 70781847267117670840), (Int.negOfNat 8057714158416870240), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(4604128207524033137763501255329921/2814749767106560000000000000000000), (32152376904613872660270604918959/5629499534213120000000000000000000), (-591251241836956074389126862846059/11258999068426240000000000000000000), (-598756159179479673814224621396433/56294995342131200000000000000000000), (12509220828772862605207345134471/56294995342131200000000000000000000), (14703402329242220300270359230931/56294995342131200000000000000000000), (281590285545986353362196181001/28147497671065600000000000000000000), (-35245679117186026474422440867/11258999068426240000000000000000000), (-5402933156387692288862458193/28147497671065600000000000000000000), (655624927645634387491484747/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial143.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial143.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial143.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 76792670675701544434956352064940021), (Int.negOfNat 17090453788273644999197534738181116), (Int.negOfNat 5067968708914246819292387224955226), (Int.ofNat 69737802254456216314717015544345), (Int.ofNat 138156988680292436685491312103399), (Int.ofNat 5010881541324579131963281007112), (Int.negOfNat 2027494102333492518196243748157), (Int.negOfNat 111916103218959034556447329369), (Int.ofNat 18549012216291912264094243070), (Int.ofNat 1200387923032545826986736990), (Int.negOfNat 115775903984211299982057463), (Int.negOfNat 8158522060332450114164013), (Int.ofNat 523652078148513586345096), (Int.ofNat 38967612348692819314901), (Int.negOfNat 1791803362312844310856), (Int.negOfNat 139885145013812562210), (Int.ofNat 4832817969558663420), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(76792670675701544434956352064940021/56294995342131200000000000000000000), (-4272613447068411249799383684545279/14073748835532800000000000000000000), (-2533984354457123409646193612477613/28147497671065600000000000000000000), (13947560450891243262943403108869/11258999068426240000000000000000000), (138156988680292436685491312103399/56294995342131200000000000000000000), (626360192665572391495410125889/7036874417766400000000000000000000), (-2027494102333492518196243748157/56294995342131200000000000000000000), (-111916103218959034556447329369/56294995342131200000000000000000000), (1854901221629191226409424307/5629499534213120000000000000000000), (120038792303254582698673699/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial143.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial143.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial143.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 25129796139079292739804336152666893), (Int.negOfNat 32121908198260215615132776585733080), (Int.negOfNat 1457461276054999826464254443880363), (Int.ofNat 1025995907492741059577963372853165), (Int.ofNat 59072301538911670046233556662013), (Int.negOfNat 19101197775736678794279967291321), (Int.negOfNat 1181952626568018347306933650727), (Int.ofNat 220071474655308786172709642575), (Int.ofNat 13860221531257343795331412670), (Int.negOfNat 1692862864115998338289560501), (Int.negOfNat 106659723552509140672762633), (Int.ofNat 9232090343962321206838960), (Int.ofNat 577802802374746729485475), (Int.negOfNat 37429583155844040377401), (Int.negOfNat 2318960657841385594957), (Int.ofNat 115319578296125443890), (Int.ofNat 8071463365869522810), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(25129796139079292739804336152666893/56294995342131200000000000000000000), (-803047704956505390378319414643327/1407374883553280000000000000000000), (-1457461276054999826464254443880363/56294995342131200000000000000000000), (205199181498548211915592674570633/11258999068426240000000000000000000), (59072301538911670046233556662013/56294995342131200000000000000000000), (-19101197775736678794279967291321/56294995342131200000000000000000000), (-1181952626568018347306933650727/56294995342131200000000000000000000), (8802858986212351446908385703/2251799813685248000000000000000000), (1386022153125734379533141267/5629499534213120000000000000000000), (-1692862864115998338289560501/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial143.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial143.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial143.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 36446862240197120887617585826659304), (Int.negOfNat 25396065092200417269992215792516957), (Int.ofNat 4468473365843714664332485346975296), (Int.ofNat 683195012895928651803317374445209), (Int.negOfNat 133525022802616469984842165221012), (Int.negOfNat 12544903321101163881313773316288), (Int.ofNat 2116416061099514485422958724781), (Int.ofNat 154158174332550595530715226307), (Int.negOfNat 20918599433433278516038951015), (Int.negOfNat 1308894202511962852871432550), (Int.ofNat 140269717501680618585823530), (Int.ofNat 7943500946953765524775464), (Int.negOfNat 677967384109852499443499), (Int.negOfNat 35670363376454603992837), (Int.ofNat 2470868734232611485380), (Int.ofNat 120618741620867664850), (Int.negOfNat 7439362126504775210), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-4555857780024640110952198228332413/7036874417766400000000000000000000), (-25396065092200417269992215792516957/56294995342131200000000000000000000), (69819896341308041630195083546489/879609302220800000000000000000000), (683195012895928651803317374445209/56294995342131200000000000000000000), (-33381255700654117496210541305253/14073748835532800000000000000000000), (-196014114392205685645527708067/879609302220800000000000000000000), (2116416061099514485422958724781/56294995342131200000000000000000000), (154158174332550595530715226307/56294995342131200000000000000000000), (-4183719886686655703207790203/11258999068426240000000000000000000), (-26177884050239257057428651/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial143.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial143.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial143.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial143.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial143.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial143.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial143.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial143.reflect := by
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

end Bin143
end
end ErdosOverlap.OuterNumerics
