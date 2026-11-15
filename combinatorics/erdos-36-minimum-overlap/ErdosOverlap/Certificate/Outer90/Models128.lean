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

/-! # Exact integer weighted outer models for source bin 128

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin128

def weightDenominator : ℤ := (Int.ofNat 2000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 1031161515282901400)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 584301576660738400)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 501832065415329000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 297386134062419760)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 110388392347149100)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 76950276350653920)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 163260455529594920)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 133482685810142220)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 16600624426769368)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial128.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial128.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 1531352372570645000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 141862080279399540)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 312817609533117880)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 42530762025091270)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 66341613707222080)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 52773332078471450)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 14616926269798522)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 17394159516241584)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 10176741602809061)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial128.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial128.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 1531352372570645000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 141862080279399540)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 312817609533117880)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 42530762025091270)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 66341613707222080)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 52773332078471450)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 14616926269798522)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 17394159516241584)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 10176741602809061)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial128.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial128.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial128.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 2725344996011830354573288303976803), (Int.ofNat 804046538916181350300184434629027), (Int.ofNat 223057806199208084484174394449254), (Int.negOfNat 30564406781283199763730824469343), (Int.negOfNat 6048960559366728351324602286143), (Int.ofNat 688595541872909086725442160679), (Int.ofNat 91133360838271612041841797957), (Int.negOfNat 8906049030435512337074706329), (Int.negOfNat 841541843663013668019096894), (Int.ofNat 72743351594113916662982636), (Int.ofNat 5152800813062220116205267), (Int.negOfNat 408127981654192739142526), (Int.negOfNat 22313185389370712345217), (Int.ofNat 1675365938763618969219), (Int.ofNat 72031842583755995973), (Int.negOfNat 5285080624684479197), (Int.negOfNat 172819517843376278), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-2725344996011830354573288303976803/2251799813685248000000000000000000), (804046538916181350300184434629027/2251799813685248000000000000000000), (111528903099604042242087197224627/1125899906842624000000000000000000), (-30564406781283199763730824469343/2251799813685248000000000000000000), (-6048960559366728351324602286143/2251799813685248000000000000000000), (688595541872909086725442160679/2251799813685248000000000000000000), (91133360838271612041841797957/2251799813685248000000000000000000), (-8906049030435512337074706329/2251799813685248000000000000000000), (-420770921831506834009548447/1125899906842624000000000000000000), (18185837898528479165745659/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial128.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial128.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial128.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial128 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.negOfNat 539765524592835138151735500105057), (Int.ofNat 1203860677844332876372460022412910), (Int.negOfNat 35655095536782023950082266250175), (Int.negOfNat 42875365892030933806840053662091), (Int.ofNat 3211935160222499996805676340155), (Int.ofNat 831558500918943086143741539354), (Int.negOfNat 68551684899372592994529522547), (Int.negOfNat 9463274875085377478231184343), (Int.ofNat 757954237090561835496748869), (Int.ofNat 68649297435251253169713227), (Int.negOfNat 5295111101810212697330354), (Int.negOfNat 340471609468780291664757), (Int.ofNat 25846247532823893753263), (Int.ofNat 1220066802103758777955), (Int.negOfNat 94007699401895144900), (Int.negOfNat 3281372793804470627), (Int.ofNat 272999863692522456), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-539765524592835138151735500105057/2251799813685248000000000000000000), (120386067784433287637246002241291/225179981368524800000000000000000), (-1426203821471280958003290650007/90071992547409920000000000000000), (-42875365892030933806840053662091/2251799813685248000000000000000000), (642387032044499999361135268031/450359962737049600000000000000000), (415779250459471543071870769677/1125899906842624000000000000000000), (-68551684899372592994529522547/2251799813685248000000000000000000), (-9463274875085377478231184343/2251799813685248000000000000000000), (757954237090561835496748869/2251799813685248000000000000000000), (68649297435251253169713227/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial128.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial128.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial128.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial128 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 1454957928863510059318911180572950), (Int.ofNat 699545095343789096400561594256163), (Int.negOfNat 170501985100729543057638098905346), (Int.ofNat 1449543811828485601024751580185), (Int.ofNat 5808475438160578776056267907718), (Int.negOfNat 357864934908020481920031405512), (Int.negOfNat 91121371989078121051595344900), (Int.ofNat 6412490066416257247947132941), (Int.ofNat 826213284427374096845083368), (Int.negOfNat 59366702083917170147348993), (Int.negOfNat 4845338265267871770086028), (Int.ofNat 355037420968403319539043), (Int.ofNat 19734362303846922102808), (Int.negOfNat 1514461816035986858462), (Int.negOfNat 58497714297672712639), (Int.ofNat 4843111860484451353), (Int.ofNat 112840902960259113), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(29099158577270201186378223611459/45035996273704960000000000000000), (699545095343789096400561594256163/2251799813685248000000000000000000), (-85250992550364771528819049452673/1125899906842624000000000000000000), (289908762365697120204950316037/450359962737049600000000000000000), (2904237719080289388028133953859/1125899906842624000000000000000000), (-44733116863502560240003925689/281474976710656000000000000000000), (-911213719890781210515953449/22517998136852480000000000000000), (6412490066416257247947132941/2251799813685248000000000000000000), (103276660553421762105635421/281474976710656000000000000000000), (-59366702083917170147348993/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial128.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial128.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial128.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial128 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 2260286437628961768253077866796415), (Int.ofNat 178240043450168864980934899964486), (Int.negOfNat 67428176113374935104360798185910), (Int.ofNat 23718061234837442510969752690254), (Int.negOfNat 804190641488930894604890937027), (Int.negOfNat 689329632535951911035637076162), (Int.ofNat 41066043927423774886738840175), (Int.ofNat 8622797394021712017882776626), (Int.negOfNat 558945816601626640323927348), (Int.negOfNat 62836868722761613939292604), (Int.ofNat 4276099002346183765320015), (Int.ofNat 300298860468496638163261), (Int.negOfNat 21921790634046257122354), (Int.negOfNat 1004506349854409761060), (Int.ofNat 81944140422295420304), (Int.ofNat 2313307374693664834), (Int.negOfNat 242469638884095273), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(452057287525792353650615573359283/450359962737049600000000000000000), (89120021725084432490467449982243/1125899906842624000000000000000000), (-6742817611337493510436079818591/225179981368524800000000000000000), (11859030617418721255484876345127/1125899906842624000000000000000000), (-804190641488930894604890937027/2251799813685248000000000000000000), (-344664816267975955517818538081/1125899906842624000000000000000000), (1642641757096950995469553607/90071992547409920000000000000000), (4311398697010856008941388313/1125899906842624000000000000000000), (-139736454150406660080981837/562949953421312000000000000000000), (-15709217180690403484823151/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial128.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial128.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial128.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial128 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 2505434290847850490837995448583685), (Int.ofNat 123318853535079732483311892667502), (Int.ofNat 14848539773695639667266678935921), (Int.negOfNat 153090844638412487735746669956), (Int.negOfNat 3631419729310985226396704540040), (Int.ofNat 191588894116549414612547939483), (Int.ofNat 74314562565094142060700523534), (Int.negOfNat 4305473120833707710719429476), (Int.negOfNat 721931695970061735968454136), (Int.ofNat 44356483578744838231971884), (Int.ofNat 4219888745579153667660559), (Int.negOfNat 281265580100498697905041), (Int.negOfNat 16389312879515377192113), (Int.ofNat 1241488332768757432015), (Int.ofNat 44266406957362385560), (Int.negOfNat 4156713687391978181), (Int.negOfNat 63039029679951009), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(501086858169570098167599089716737/450359962737049600000000000000000), (61659426767539866241655946333751/1125899906842624000000000000000000), (14848539773695639667266678935921/2251799813685248000000000000000000), (-38272711159603121933936667489/562949953421312000000000000000000), (-90785493232774630659917613501/56294995342131200000000000000000), (191588894116549414612547939483/2251799813685248000000000000000000), (37157281282547071030350261767/1125899906842624000000000000000000), (-1076368280208426927679857369/562949953421312000000000000000000), (-90241461996257716996056767/281474976710656000000000000000000), (11089120894686209557992971/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial128.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial128.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial128.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial128 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 2762316175407216081658870391231677), (Int.ofNat 91718191027041358369296909901676), (Int.negOfNat 44004260930388272824799570037708), (Int.negOfNat 13065389588704143606822086732669), (Int.ofNat 951338113354288605564160403471), (Int.ofNat 512193764598175866481282419535), (Int.negOfNat 27663622733347138954908726041), (Int.negOfNat 7169619828132554905574170220), (Int.ofNat 391122703833701651361261757), (Int.ofNat 53705257870281266270954784), (Int.negOfNat 3154067916536922979833211), (Int.negOfNat 250900661594961232303557), (Int.ofNat 16763466081260767531144), (Int.ofNat 781334271475053278414), (Int.negOfNat 64098329174057143547), (Int.negOfNat 1678835994315096445), (Int.ofNat 211939414075668090), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(2762316175407216081658870391231677/2251799813685248000000000000000000), (22929547756760339592324227475419/562949953421312000000000000000000), (-11001065232597068206199892509427/562949953421312000000000000000000), (-13065389588704143606822086732669/2251799813685248000000000000000000), (951338113354288605564160403471/2251799813685248000000000000000000), (102438752919635173296256483907/450359962737049600000000000000000), (-27663622733347138954908726041/2251799813685248000000000000000000), (-358480991406627745278708511/112589990684262400000000000000000), (391122703833701651361261757/2251799813685248000000000000000000), (1678289308446289570967337/70368744177664000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial128.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial128.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial128.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial128 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 2694259778985709118018948222360426), (Int.negOfNat 177682894685519017609967213576669), (Int.negOfNat 69140038218686645963295553446664), (Int.ofNat 7524533116843893497154132150024), (Int.ofNat 3009914630954039477519894855300), (Int.negOfNat 169490194722552374028297673126), (Int.negOfNat 61338552868670996575457135791), (Int.ofNat 2950172730491574960565733740), (Int.ofNat 610803332562626486349617699), (Int.negOfNat 30484684299875683258526990), (Int.negOfNat 3547860264464173125502996), (Int.ofNat 198915782093137273548830), (Int.ofNat 13151941771771363463271), (Int.negOfNat 896968355373795277001), (Int.negOfNat 31506390809241808543), (Int.ofNat 2995396053440140851), (Int.ofNat 13237156399642905), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(1347129889492854559009474111180213/1125899906842624000000000000000000), (-177682894685519017609967213576669/2251799813685248000000000000000000), (-8642504777335830745411944180833/281474976710656000000000000000000), (940566639605486687144266518753/281474976710656000000000000000000), (30099146309540394775198948553/22517998136852480000000000000000), (-84745097361276187014148836563/1125899906842624000000000000000000), (-61338552868670996575457135791/2251799813685248000000000000000000), (147508636524578748028286687/112589990684262400000000000000000), (610803332562626486349617699/2251799813685248000000000000000000), (-3048468429987568325852699/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial128.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial128.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial128.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial128 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 2161854582231820595859970798079966), (Int.negOfNat 291106348303194498593165112998161), (Int.ofNat 22866712062198161509371767769047), (Int.ofNat 17547952388173510538446946632265), (Int.negOfNat 1016033431812187179276253810880), (Int.negOfNat 467269336530915228446142801576), (Int.ofNat 19472249606544958505426873211), (Int.ofNat 6203459830062457633790937793), (Int.negOfNat 250332882183215312954086297), (Int.negOfNat 45852991958411682601433707), (Int.ofNat 2030951938321630660932327), (Int.ofNat 207880201799516344721811), (Int.negOfNat 10991034916185054703800), (Int.negOfNat 600779635788710291221), (Int.ofNat 42150540097670598516), (Int.ofNat 944032005143481724), (Int.negOfNat 164808564840471539), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(1080927291115910297929985399039983/1125899906842624000000000000000000), (-291106348303194498593165112998161/2251799813685248000000000000000000), (22866712062198161509371767769047/2251799813685248000000000000000000), (3509590477634702107689389326453/450359962737049600000000000000000), (-3175104474413084935238293159/7036874417766400000000000000000), (-58408667066364403555767850197/281474976710656000000000000000000), (19472249606544958505426873211/2251799813685248000000000000000000), (6203459830062457633790937793/2251799813685248000000000000000000), (-250332882183215312954086297/2251799813685248000000000000000000), (-45852991958411682601433707/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial128.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial128.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial128.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial128 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 1782238360398046664409571199652535), (Int.negOfNat 52790409389316831192843307069891), (Int.ofNat 74598683046507363396272890810994), (Int.negOfNat 3338098002555097642625337968219), (Int.negOfNat 3214165559806149767714239977197), (Int.ofNat 104157126297214621268832447469), (Int.ofNat 56619832818632244870468049959), (Int.negOfNat 1682284361406815644691388473), (Int.negOfNat 538899111629183189879913025), (Int.ofNat 17154903989549420500686707), (Int.ofNat 3045513815340554905549279), (Int.negOfNat 113782325180744114760395), (Int.negOfNat 10787675884136715838684), (Int.ofNat 518700148242793134357), (Int.ofNat 23223455199386670956), (Int.negOfNat 1758900759064763476), (Int.negOfNat 389390751722291), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(356447672079609332881914239930507/450359962737049600000000000000000), (-52790409389316831192843307069891/2251799813685248000000000000000000), (37299341523253681698136445405497/1125899906842624000000000000000000), (-3338098002555097642625337968219/2251799813685248000000000000000000), (-3214165559806149767714239977197/2251799813685248000000000000000000), (104157126297214621268832447469/2251799813685248000000000000000000), (56619832818632244870468049959/2251799813685248000000000000000000), (-1682284361406815644691388473/2251799813685248000000000000000000), (-21555964465167327595196521/90071992547409920000000000000000), (17154903989549420500686707/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial128.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial128.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial128.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial128 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 1903535876876911088399642531055424), (Int.ofNat 120645531802335714518720129462917), (Int.negOfNat 2634459746486673930958995367031), (Int.negOfNat 17600602025447052966783658115240), (Int.ofNat 254125058003114386267112478262), (Int.ofNat 455731257597276785125591029868), (Int.negOfNat 7720526350912497716953018803), (Int.negOfNat 5720499212859465013187427616), (Int.ofNat 106864007215731490445909727), (Int.ofNat 40919629992273768845052634), (Int.negOfNat 911114073372836014715172), (Int.negOfNat 180279377782124863510670), (Int.ofNat 5077477729297134749359), (Int.ofNat 496005108141968915401), (Int.negOfNat 19591307010613722959), (Int.negOfNat 734523830267639315), (Int.ofNat 111253832781314681), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(29742748076201735756244414547741/35184372088832000000000000000000), (120645531802335714518720129462917/2251799813685248000000000000000000), (-2634459746486673930958995367031/2251799813685248000000000000000000), (-440015050636176324169591452881/56294995342131200000000000000000), (127062529001557193133556239131/1125899906842624000000000000000000), (113932814399319196281397757467/562949953421312000000000000000000), (-7720526350912497716953018803/2251799813685248000000000000000000), (-178765600401858281662107113/70368744177664000000000000000000), (106864007215731490445909727/2251799813685248000000000000000000), (20459814996136884422526317/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial128.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial128.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial128.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial128 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 2010954379238843031314132175187715), (Int.negOfNat 60356992943818234409922937898118), (Int.negOfNat 71012771903502828784780704367943), (Int.negOfNat 1386539099445567709957271572928), (Int.ofNat 3012084736177667800217428104197), (Int.ofNat 910571256249563203379276291), (Int.negOfNat 53674681347546904175365448113), (Int.ofNat 228842281939040764491669940), (Int.ofNat 497887544648878318769188117), (Int.negOfNat 3768157214758085553392968), (Int.negOfNat 2759800419179330467450983), (Int.ofNat 30404452935155194041333), (Int.ofNat 9629003789729112432596), (Int.negOfNat 145136887274453778638), (Int.negOfNat 20157264253618777947), (Int.ofNat 322765381683503741), (Int.ofNat 14318991133380106), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(402190875847768606262826435037543/450359962737049600000000000000000), (-30178496471909117204961468949059/1125899906842624000000000000000000), (-71012771903502828784780704367943/2251799813685248000000000000000000), (-21664673428836995468082368327/35184372088832000000000000000000), (3012084736177667800217428104197/2251799813685248000000000000000000), (910571256249563203379276291/2251799813685248000000000000000000), (-53674681347546904175365448113/2251799813685248000000000000000000), (11442114096952038224583497/112589990684262400000000000000000), (497887544648878318769188117/2251799813685248000000000000000000), (-471019651844760694174121/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial128.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial128.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial128.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial128 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 1640036403286139586026501264959492), (Int.negOfNat 274302415971926906326724854164184), (Int.negOfNat 18852734155953009993417697533593), (Int.ofNat 15118642715497829447958155737738), (Int.ofNat 372566327524085240915191476253), (Int.negOfNat 428952922222170959500300237414), (Int.negOfNat 5539968551692425141986873822), (Int.ofNat 5383530273806929465676317016), (Int.ofNat 40218539068171365319366012), (Int.negOfNat 38128267536066217121840064), (Int.negOfNat 156770013649638754000121), (Int.ofNat 168584974285429601546677), (Int.ofNat 440644887007452136555), (Int.negOfNat 475202428930487404823), (Int.negOfNat 1795275053911513396), (Int.ofNat 754140812126303005), (Int.negOfNat 61451959501006577), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(410009100821534896506625316239873/562949953421312000000000000000000), (-34287801996490863290840606770523/281474976710656000000000000000000), (-18852734155953009993417697533593/2251799813685248000000000000000000), (7559321357748914723979077868869/1125899906842624000000000000000000), (372566327524085240915191476253/2251799813685248000000000000000000), (-214476461111085479750150118707/1125899906842624000000000000000000), (-2769984275846212570993436911/1125899906842624000000000000000000), (672941284225866183209539627/281474976710656000000000000000000), (10054634767042841329841503/562949953421312000000000000000000), (-595754180251034642528751/35184372088832000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial128.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial128.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial128.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial128 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 1129529834973529909431470167841369), (Int.negOfNat 189381185638840306183381470226766), (Int.ofNat 48671891974351646246886598301317), (Int.ofNat 2941156226499783023573953902454), (Int.negOfNat 2845764537193295872577296971265), (Int.negOfNat 98455356609881088361987256554), (Int.ofNat 50599744700176147739208227406), (Int.ofNat 1235714877391036612330167594), (Int.negOfNat 467535854879777523147875800), (Int.negOfNat 8691845102054386960509432), (Int.ofNat 2630186920014586580337855), (Int.ofNat 43415593433425696223959), (Int.negOfNat 9591892570897444487598), (Int.negOfNat 179973842615849912396), (Int.ofNat 22612651096856921652), (Int.ofNat 769228178321942142), (Int.negOfNat 44849215941807289), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(1129529834973529909431470167841369/2251799813685248000000000000000000), (-94690592819420153091690735113383/1125899906842624000000000000000000), (48671891974351646246886598301317/2251799813685248000000000000000000), (1470578113249891511786976951227/1125899906842624000000000000000000), (-569152907438659174515459394253/450359962737049600000000000000000), (-49227678304940544180993628277/1125899906842624000000000000000000), (25299872350088073869604113703/1125899906842624000000000000000000), (617857438695518306165083797/1125899906842624000000000000000000), (-2337679274398887615739379/11258999068426240000000000000000), (-1086480637756798370063679/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial128.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial128.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial128.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial128 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 923576635010419976390600846148822), (Int.negOfNat 48556955229547468753637889699732), (Int.ofNat 2271368953472583014857532388406), (Int.negOfNat 15818648249287329427325476345400), (Int.negOfNat 971092102945607744562261240740), (Int.ofNat 407049418460587167713024392943), (Int.ofNat 18586034691252426109895279060), (Int.negOfNat 4994371790690042865455009357), (Int.negOfNat 171877237918952508432922696), (Int.ofNat 36121951458628953299333481), (Int.ofNat 1045745084504410588804000), (Int.negOfNat 168503857859087341266795), (Int.negOfNat 4887842461995829829332), (Int.ofNat 527751912251773059574), (Int.ofNat 18866012217368093169), (Int.negOfNat 962863310196377257), (Int.ofNat 11650086220698473), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(461788317505209988195300423074411/1125899906842624000000000000000000), (-12139238807386867188409472424933/562949953421312000000000000000000), (1135684476736291507428766194203/1125899906842624000000000000000000), (-79093241246436647136627381727/11258999068426240000000000000000), (-48554605147280387228113062037/112589990684262400000000000000000), (407049418460587167713024392943/2251799813685248000000000000000000), (929301734562621305494763953/112589990684262400000000000000000), (-4994371790690042865455009357/2251799813685248000000000000000000), (-21484654739869063554115337/281474976710656000000000000000000), (36121951458628953299333481/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial128.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial128.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial128.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial128 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 707012552933395543613868414470472), (Int.negOfNat 226564623395736659158200185352431), (Int.negOfNat 82412839205573392467835132099031), (Int.negOfNat 7233742499649801059547154795332), (Int.ofNat 2775808254351425935565023405649), (Int.ofNat 209519961958113689941627251500), (Int.negOfNat 45450745472948724017413455663), (Int.negOfNat 2488352975341234902384572365), (Int.ofNat 429708945220528880337657769), (Int.ofNat 18184916583899346248556425), (Int.negOfNat 2572905679227885449385802), (Int.negOfNat 96917274492928569741659), (Int.ofNat 10380654918583243715735), (Int.ofNat 412346890775650309957), (Int.negOfNat 29306227231776485972), (Int.negOfNat 1461225201888073149), (Int.ofNat 75379440750234472), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(88376569116674442951733551808809/281474976710656000000000000000000), (-226564623395736659158200185352431/2251799813685248000000000000000000), (-82412839205573392467835132099031/2251799813685248000000000000000000), (-1808435624912450264886788698833/562949953421312000000000000000000), (2775808254351425935565023405649/2251799813685248000000000000000000), (419039923916227379883254503/4503599627370496000000000000000), (-45450745472948724017413455663/2251799813685248000000000000000000), (-497670595068246980476914473/450359962737049600000000000000000), (429708945220528880337657769/2251799813685248000000000000000000), (727396663355973849942257/90071992547409920000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial128.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial128.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial128.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial128 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 85631248313684315350581215673410), (Int.negOfNat 546806825914559511135039912350988), (Int.negOfNat 54192430325757287952254574548026), (Int.ofNat 15513377926906056507160822118063), (Int.ofNat 1964579249869131834297199353526), (Int.negOfNat 338199312189593810560302537800), (Int.negOfNat 29338927785183314827773050575), (Int.ofNat 4317491861947289767760413201), (Int.ofNat 258616789140050814833580130), (Int.negOfNat 33833842816159773451973908), (Int.negOfNat 1589230220125001883225629), (Int.ofNat 175082011355850910739950), (Int.ofNat 7554016971923715296467), (Int.negOfNat 632830420696458228179), (Int.negOfNat 29316125705025453235), (Int.ofNat 1591181376444780901), (Int.ofNat 27975045456800570), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-8563124831368431535058121567341/225179981368524800000000000000000), (-136701706478639877783759978087747/562949953421312000000000000000000), (-27096215162878643976127287274013/1125899906842624000000000000000000), (15513377926906056507160822118063/2251799813685248000000000000000000), (982289624934565917148599676763/1125899906842624000000000000000000), (-1690996560947969052801512689/11258999068426240000000000000000), (-1173557111407332593110922023/90071992547409920000000000000000), (4317491861947289767760413201/2251799813685248000000000000000000), (25861678914005081483358013/225179981368524800000000000000000), (-8458460704039943362993477/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial128.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial128.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial128.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial128 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 1252574120937368255676377230024482), (Int.negOfNat 545123404118584487279214330041680), (Int.ofNat 55136363578942796693836053100389), (Int.ofNat 15690789114645675187666884978607), (Int.negOfNat 1828881978815823490782299121087), (Int.negOfNat 287051388370073891400853226687), (Int.ofNat 34873455667682003143032918647), (Int.ofNat 3094367920243353401011879833), (Int.negOfNat 375574186780170940259080050), (Int.negOfNat 22274908187653069380908708), (Int.ofNat 2537612641685153463573181), (Int.ofNat 119686490147639292268806), (Int.negOfNat 11665949914088219746875), (Int.negOfNat 513806289816675531675), (Int.ofNat 38499387576812554147), (Int.ofNat 1896768694338848685), (Int.negOfNat 128934172809391330), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-626287060468684127838188615012241/1125899906842624000000000000000000), (-6814042551482306090990179125521/28147497671065600000000000000000), (55136363578942796693836053100389/2251799813685248000000000000000000), (15690789114645675187666884978607/2251799813685248000000000000000000), (-1828881978815823490782299121087/2251799813685248000000000000000000), (-287051388370073891400853226687/2251799813685248000000000000000000), (34873455667682003143032918647/2251799813685248000000000000000000), (3094367920243353401011879833/2251799813685248000000000000000000), (-7511483735603418805181601/45035996273704960000000000000000), (-5568727046913267345227177/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial128.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial128.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial128.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial128 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 2032673697192866723632297819293393), (Int.negOfNat 210116712373552528501787326909917), (Int.ofNat 92128941498954264730777895700027), (Int.negOfNat 3859901709262117921937987641093), (Int.negOfNat 2213482488429691758165438996766), (Int.ofNat 200888006660816774015764041740), (Int.ofNat 30688096231283045700569458431), (Int.negOfNat 3387135499660727057962755661), (Int.negOfNat 266774226595453376079522953), (Int.ofNat 31286118547302750385568505), (Int.ofNat 1648369933741289945076242), (Int.negOfNat 185201090306749076266283), (Int.negOfNat 7926183520288337216935), (Int.ofNat 766211252354499641021), (Int.ofNat 31088436986612228140), (Int.negOfNat 2199728078758190781), (Int.negOfNat 40822811104721184), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-2032673697192866723632297819293393/2251799813685248000000000000000000), (-210116712373552528501787326909917/2251799813685248000000000000000000), (92128941498954264730777895700027/2251799813685248000000000000000000), (-3859901709262117921937987641093/2251799813685248000000000000000000), (-1106741244214845879082719498383/1125899906842624000000000000000000), (10044400333040838700788202087/112589990684262400000000000000000), (30688096231283045700569458431/2251799813685248000000000000000000), (-3387135499660727057962755661/2251799813685248000000000000000000), (-266774226595453376079522953/2251799813685248000000000000000000), (6257223709460550077113701/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial128.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial128.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial128.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial128 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 2142778381241869929807187018144133), (Int.ofNat 61499620664556533581643916968595), (Int.ofNat 36685457098020675602497526736865), (Int.negOfNat 10811961172004721785490225672844), (Int.ofNat 529275658902920651220890326631), (Int.ofNat 235472801854962621011407374492), (Int.negOfNat 23069073291877691460637768564), (Int.negOfNat 2653223401747853171826413165), (Int.ofNat 321160283503465294720050296), (Int.ofNat 19449707454226538665954585), (Int.negOfNat 2529925660400456093995480), (Int.negOfNat 106099541334714185880803), (Int.ofNat 13166921447870297185764), (Int.ofNat 463927656343948821958), (Int.negOfNat 49172105829704554481), (Int.negOfNat 1618060385668415761), (Int.ofNat 188912787692508495), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-2142778381241869929807187018144133/2251799813685248000000000000000000), (12299924132911306716328783393719/450359962737049600000000000000000), (7337091419604135120499505347373/450359962737049600000000000000000), (-2702990293001180446372556418211/562949953421312000000000000000000), (529275658902920651220890326631/2251799813685248000000000000000000), (58868200463740655252851843623/562949953421312000000000000000000), (-5767268322969422865159442141/562949953421312000000000000000000), (-530644680349570634365282633/450359962737049600000000000000000), (40145035437933161840006287/281474976710656000000000000000000), (3889941490845307733190917/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial128.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial128.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial128.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial128 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 1945256069751030062082701627901241), (Int.ofNat 109014528333310632940371921131585), (Int.negOfNat 3331458168269474784261405065911), (Int.negOfNat 1697381125797460283789762951546), (Int.ofNat 1158378117301424285540998478371), (Int.negOfNat 103241322697363909410214363964), (Int.negOfNat 20403393300770168973179626411), (Int.ofNat 2658401520717852824868503738), (Int.ofNat 188903178005510971810164752), (Int.negOfNat 29462607831340903303947568), (Int.negOfNat 1193440752088236028296223), (Int.ofNat 197152295781564972072119), (Int.ofNat 5880231888609466479046), (Int.negOfNat 902093557731400506276), (Int.negOfNat 23672461617142843164), (Int.ofNat 3004533042339401654), (Int.ofNat 10292586296294001), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-1945256069751030062082701627901241/2251799813685248000000000000000000), (21802905666662126588074384226317/450359962737049600000000000000000), (-3331458168269474784261405065911/2251799813685248000000000000000000), (-848690562898730141894881475773/1125899906842624000000000000000000), (1158378117301424285540998478371/2251799813685248000000000000000000), (-25810330674340977352553590991/562949953421312000000000000000000), (-20403393300770168973179626411/2251799813685248000000000000000000), (1329200760358926412434251869/1125899906842624000000000000000000), (11806448625344435738135297/140737488355328000000000000000000), (-1841412989458806456496723/140737488355328000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial128.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial128.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial128.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial128 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 1739834636537457249449845415934228), (Int.ofNat 101524188298455334633658954086876), (Int.ofNat 3110456850039817481115882383511), (Int.ofNat 1834659172053878544699929933716), (Int.negOfNat 268420636476524684978487446776), (Int.negOfNat 103054453146361861848126522404), (Int.ofNat 17216776667710567592616319230), (Int.ofNat 1378303931333663106296088360), (Int.negOfNat 288498849703565224448610348), (Int.negOfNat 10417974920111370982818336), (Int.ofNat 2561963204283348993382089), (Int.ofNat 58016705969515995246781), (Int.negOfNat 14600800489586346928699), (Int.negOfNat 268042806422482077151), (Int.ofNat 58564103144331480940), (Int.ofNat 1094922668105537509), (Int.negOfNat 238714660972816599), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-434958659134364312362461353983557/562949953421312000000000000000000), (25381047074613833658414738521719/562949953421312000000000000000000), (3110456850039817481115882383511/2251799813685248000000000000000000), (458664793013469636174982483429/562949953421312000000000000000000), (-33552579559565585622310930847/281474976710656000000000000000000), (-25763613286590465462031630601/562949953421312000000000000000000), (1721677666771056759261631923/225179981368524800000000000000000), (34457598283341577657402209/56294995342131200000000000000000), (-72124712425891306112152587/562949953421312000000000000000000), (-325561716253480343213073/70368744177664000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial128.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial128.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial128.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial128 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 1516057843696872460121939371389601), (Int.ofNat 122765189120014630853311454725122), (Int.ofNat 3955351377106421814194202845904), (Int.negOfNat 1441222513091713887127343574540), (Int.negOfNat 210160758108044676764821285090), (Int.ofNat 89942546906207479778302653200), (Int.ofNat 5790120725071750408685693825), (Int.negOfNat 2345137177997484968883926124), (Int.negOfNat 53442218178737138329666981), (Int.ofNat 28642726574135391957640808), (Int.ofNat 315831449009495345803799), (Int.negOfNat 208034827241707493376363), (Int.negOfNat 1706558909765436899036), (Int.ofNat 1014799860568872470282), (Int.ofNat 8794191475370563427), (Int.negOfNat 3475743967188375123), (Int.ofNat 20237638512133182), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-1516057843696872460121939371389601/2251799813685248000000000000000000), (61382594560007315426655727362561/1125899906842624000000000000000000), (247209461069151363387137677869/140737488355328000000000000000000), (-72061125654585694356367178727/112589990684262400000000000000000), (-21016075810804467676482128509/225179981368524800000000000000000), (224856367265518699445756633/5629499534213120000000000000000), (231604829002870016347427753/90071992547409920000000000000000), (-586284294499371242220981531/562949953421312000000000000000000), (-53442218178737138329666981/2251799813685248000000000000000000), (3580340821766923994705101/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial128.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial128.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial128.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial128 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 1266648977942935845013535210620080), (Int.ofNat 121833819655325975611375466541283), (Int.negOfNat 2692697103892917715451929867968), (Int.ofNat 142719131720527856490400528380), (Int.ofNat 431277165022475378338833319854), (Int.negOfNat 7211069730236770279370917665), (Int.negOfNat 15674395734095093926454411173), (Int.ofNat 195197624674720007164619856), (Int.ofNat 271362415859595752663736945), (Int.negOfNat 2788526808312934238762878), (Int.negOfNat 2589793604355356189251172), (Int.ofNat 17168426612527740828890), (Int.ofNat 15640348782718992847841), (Int.negOfNat 46923277383226784223), (Int.negOfNat 65649140076359857937), (Int.negOfNat 96865489683295099), (Int.ofNat 288516534253124703), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-15833112224286698062669190132751/28147497671065600000000000000000), (121833819655325975611375466541283/2251799813685248000000000000000000), (-42073392248326839303936404187/35184372088832000000000000000000), (7135956586026392824520026419/112589990684262400000000000000000), (215638582511237689169416659927/1125899906842624000000000000000000), (-1442213946047354055874183533/450359962737049600000000000000000), (-15674395734095093926454411173/2251799813685248000000000000000000), (12199851542170000447788741/140737488355328000000000000000000), (54272483171919150532747389/450359962737049600000000000000000), (-1394263404156467119381439/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial128.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial128.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial128.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial128 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 1026853382732734556385871876937747), (Int.ofNat 123336367535471313658277826665342), (Int.ofNat 4751808354294582616322531280596), (Int.ofNat 1339837326472622607333413945924), (Int.negOfNat 266141989075373807074136017417), (Int.negOfNat 81830360090241649644262245866), (Int.ofNat 7994963764304098819773652697), (Int.ofNat 2103458238013397894505931151), (Int.negOfNat 112359225761416377161244319), (Int.negOfNat 27736085913682876423678605), (Int.ofNat 857577353743866942731585), (Int.ofNat 213463524675682725436589), (Int.negOfNat 4032551176978910345428), (Int.negOfNat 1082730009161259378595), (Int.ofNat 12538310270885582924), (Int.ofNat 3884027045300800004), (Int.negOfNat 67368487747329733), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-1026853382732734556385871876937747/2251799813685248000000000000000000), (61668183767735656829138913332671/1125899906842624000000000000000000), (1187952088573645654080632820149/562949953421312000000000000000000), (334959331618155651833353486481/562949953421312000000000000000000), (-266141989075373807074136017417/2251799813685248000000000000000000), (-40915180045120824822131122933/1125899906842624000000000000000000), (7994963764304098819773652697/2251799813685248000000000000000000), (2103458238013397894505931151/2251799813685248000000000000000000), (-112359225761416377161244319/2251799813685248000000000000000000), (-5547217182736575284735721/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial128.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial128.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial128.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial128 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 756592313210062092085786436905192), (Int.ofNat 145663739806009182308203498809509), (Int.ofNat 2875608211480911020910703103189), (Int.negOfNat 1934405017421267228211784747206), (Int.negOfNat 233795222913597284646402629910), (Int.ofNat 97032789072276740515226100181), (Int.ofNat 11800664181561133816837718845), (Int.negOfNat 1947450076914767533464239703), (Int.negOfNat 246582808257125678722383719), (Int.ofNat 18850506496316850852337101), (Int.ofNat 2551141773342050454928849), (Int.negOfNat 110435182057616090260685), (Int.negOfNat 16024812597932795902048), (Int.ofNat 439084215976151116587), (Int.ofNat 68679085664542618364), (Int.negOfNat 1139629804692082276), (Int.negOfNat 301364299901045317), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-94574039151257761510723304613149/281474976710656000000000000000000), (145663739806009182308203498809509/2251799813685248000000000000000000), (2875608211480911020910703103189/2251799813685248000000000000000000), (-967202508710633614105892373603/1125899906842624000000000000000000), (-23379522291359728464640262991/225179981368524800000000000000000), (97032789072276740515226100181/2251799813685248000000000000000000), (2360132836312226763367543769/450359962737049600000000000000000), (-1947450076914767533464239703/2251799813685248000000000000000000), (-246582808257125678722383719/2251799813685248000000000000000000), (18850506496316850852337101/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial128.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial128.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial128.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial128 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 469418494818873776438742075920172), (Int.ofNat 135430144033039475164710913114025), (Int.negOfNat 5385533830829624041776873372712), (Int.ofNat 566435261227508460774801720320), (Int.ofNat 726937143344254256734109617512), (Int.ofNat 18480524394455438289353951503), (Int.negOfNat 24277388856964860846493268713), (Int.negOfNat 1643236840671514329957243868), (Int.ofNat 308855415031774865038109469), (Int.ofNat 26113843369790838559186738), (Int.negOfNat 2222293469278852382476580), (Int.negOfNat 211412399654235974009690), (Int.ofNat 10626428946782543708129), (Int.ofNat 1093422055006271481335), (Int.negOfNat 36460353482512126161), (Int.negOfNat 4093535220176642413), (Int.ofNat 120923219806486591), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-117354623704718444109685518980043/562949953421312000000000000000000), (5417205761321579006588436524561/90071992547409920000000000000000), (-673191728853703005222109171589/281474976710656000000000000000000), (110631886958497746245078461/439804651110400000000000000000), (90867142918031782091763702189/281474976710656000000000000000000), (18480524394455438289353951503/2251799813685248000000000000000000), (-24277388856964860846493268713/2251799813685248000000000000000000), (-410809210167878582489310967/562949953421312000000000000000000), (308855415031774865038109469/2251799813685248000000000000000000), (13056921684895419279593369/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial128.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial128.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial128.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial128 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 205020795686102313440550062283249), (Int.ofNat 140391222595346948115841503818306), (Int.ofNat 10650305851066179973010121803153), (Int.ofNat 2968833803327339811518674907173), (Int.negOfNat 590897007483698249864827220863), (Int.negOfNat 242650313564938278781251731283), (Int.negOfNat 4903745108515743265645488031), (Int.ofNat 4176595975780096135796729956), (Int.ofNat 219096587668155418613848987), (Int.negOfNat 37066954523954534134839880), (Int.negOfNat 2466246479288498155404005), (Int.ofNat 211254899534870264211387), (Int.ofNat 15719268352473501255936), (Int.negOfNat 855552016040819384906), (Int.negOfNat 67749747511258807733), (Int.ofNat 2575765182073342011), (Int.ofNat 287434699519387502), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-205020795686102313440550062283249/2251799813685248000000000000000000), (70195611297673474057920751909153/1125899906842624000000000000000000), (10650305851066179973010121803153/2251799813685248000000000000000000), (2968833803327339811518674907173/2251799813685248000000000000000000), (-590897007483698249864827220863/2251799813685248000000000000000000), (-242650313564938278781251731283/2251799813685248000000000000000000), (-4903745108515743265645488031/2251799813685248000000000000000000), (1044148993945024033949182489/562949953421312000000000000000000), (219096587668155418613848987/2251799813685248000000000000000000), (-926673863098863353370997/56294995342131200000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial128.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial128.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial128.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial128 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.ofNat 125150219808746312600642582803874), (Int.ofNat 181356357043817291898416078479734), (Int.negOfNat 3300213448877892230864236423293), (Int.negOfNat 9744193862893367071640386172760), (Int.negOfNat 2068848551351555086496289691989), (Int.ofNat 60377743564480597432556316365), (Int.ofNat 48732908333240034324467766797), (Int.ofNat 1372426458543604913185464348), (Int.negOfNat 534166149075626248652494048), (Int.negOfNat 25274237971395049544150108), (Int.ofNat 3629649714816427384291073), (Int.ofNat 204669700534045946691223), (Int.negOfNat 17174173516519311203103), (Int.negOfNat 1046085052749214249593), (Int.ofNat 60372133235282968176), (Int.ofNat 3747397327258788883), (Int.negOfNat 170725093086794695), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(62575109904373156300321291401937/1125899906842624000000000000000000), (90678178521908645949208039239867/1125899906842624000000000000000000), (-3300213448877892230864236423293/2251799813685248000000000000000000), (-243604846572334176791009654319/56294995342131200000000000000000), (-2068848551351555086496289691989/2251799813685248000000000000000000), (12075548712896119486511263273/450359962737049600000000000000000), (48732908333240034324467766797/2251799813685248000000000000000000), (343106614635901228296366087/562949953421312000000000000000000), (-16692692158613320270390439/70368744177664000000000000000000), (-6318559492848762386037527/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial128.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial128.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial128.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial128 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.ofNat 368687988053795566208004340520517), (Int.negOfNat 760990622132182363791336782741), (Int.negOfNat 94996768618263909550635545663413), (Int.negOfNat 16344941488784462419535318459480), (Int.ofNat 1197950438757770620169412551829), (Int.ofNat 503504400380872636535183122504), (Int.ofNat 5166573098681923017181700878), (Int.negOfNat 6767136220615734273549084830), (Int.negOfNat 230629896697992059585003804), (Int.ofNat 54940668727204057445088340), (Int.ofNat 2431503646038391237858593), (Int.negOfNat 304533390601462195819339), (Int.negOfNat 14877206020226632501534), (Int.ofNat 1234786720435089820980), (Int.ofNat 62297168828283508488), (Int.negOfNat 3831019197608382814), (Int.negOfNat 256904474710960319), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(368687988053795566208004340520517/2251799813685248000000000000000000), (-760990622132182363791336782741/2251799813685248000000000000000000), (-94996768618263909550635545663413/2251799813685248000000000000000000), (-408623537219611560488382961487/56294995342131200000000000000000), (1197950438757770620169412551829/2251799813685248000000000000000000), (62938050047609079566897890313/281474976710656000000000000000000), (2583286549340961508590850439/1125899906842624000000000000000000), (-676713622061573427354908483/225179981368524800000000000000000), (-57657474174498014896250951/562949953421312000000000000000000), (2747033436360202872254417/112589990684262400000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial128.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial128.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial128.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial128 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 108865879891405258275767912475783), (Int.negOfNat 500413148307932904431249739761946), (Int.negOfNat 127484268481849336048312381617480), (Int.ofNat 10321174570729799511255540477076), (Int.ofNat 4629840688103124832259005103437), (Int.ofNat 14054564721497814493383924570), (Int.negOfNat 75387865449340165824598130636), (Int.negOfNat 2040722308825625590173718987), (Int.ofNat 735342149518036606771192912), (Int.ofNat 27068018761572465429147631), (Int.negOfNat 4811686874189250756183412), (Int.negOfNat 196573439616888963741325), (Int.ofNat 22611000680206589762320), (Int.ofNat 950343966812555431202), (Int.negOfNat 80083890594146355129), (Int.negOfNat 3375414373659119711), (Int.ofNat 220526966367102799), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-108865879891405258275767912475783/2251799813685248000000000000000000), (-250206574153966452215624869880973/1125899906842624000000000000000000), (-3187106712046233401207809540437/56294995342131200000000000000000), (2580293642682449877813885119269/562949953421312000000000000000000), (4629840688103124832259005103437/2251799813685248000000000000000000), (1405456472149781449338392457/225179981368524800000000000000000), (-18846966362335041456149532659/562949953421312000000000000000000), (-2040722308825625590173718987/2251799813685248000000000000000000), (45958884344877287923199557/140737488355328000000000000000000), (27068018761572465429147631/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial128.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial128.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial128.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial128 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 1467421816971415721418594694804962), (Int.negOfNat 751816472496926477062740712775696), (Int.ofNat 28602011673807131939404296223225), (Int.ofNat 36101020158618524842091154704826), (Int.ofNat 538584866508851652181662211692), (Int.negOfNat 720116640686528682374248353153), (Int.negOfNat 21005590343724111248183940821), (Int.ofNat 8603614991117737467346174921), (Int.ofNat 297884325827670313223403315), (Int.negOfNat 67576414630564892114023293), (Int.negOfNat 2465995762747535753390486), (Int.ofNat 372353767765415761869459), (Int.ofNat 13584807372254241563697), (Int.negOfNat 1516019736139371119541), (Int.negOfNat 53605330499565182948), (Int.ofNat 4686276676704108741), (Int.ofNat 226374249902533136), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-733710908485707860709297347402481/1125899906842624000000000000000000), (-46988529531057904816421294548481/140737488355328000000000000000000), (1144080466952285277576171848929/90071992547409920000000000000000), (18050510079309262421045577352413/1125899906842624000000000000000000), (134646216627212913045415552923/562949953421312000000000000000000), (-720116640686528682374248353153/2251799813685248000000000000000000), (-21005590343724111248183940821/2251799813685248000000000000000000), (8603614991117737467346174921/2251799813685248000000000000000000), (59576865165534062644680663/450359962737049600000000000000000), (-67576414630564892114023293/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial128.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial128.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial128.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial128 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 2582468084527337917375426309910604), (Int.negOfNat 244608299243324069547101283314619), (Int.ofNat 201470279871674325170962314669943), (Int.ofNat 13211587534314668231951024638175), (Int.negOfNat 5469031417910289836963494017728), (Int.negOfNat 260299516230270144097483492064), (Int.ofNat 85058155083906347158046730872), (Int.ofNat 3400186787463689224562509823), (Int.negOfNat 831731812568837093060443426), (Int.negOfNat 30171914110979447347962204), (Int.ofNat 5490865582522527536669501), (Int.ofNat 184972293771760073610650), (Int.negOfNat 26018552663875302921335), (Int.negOfNat 813308297949308733717), (Int.ofNat 93108416878289252915), (Int.ofNat 2583835851881121147), (Int.negOfNat 260152098044601842), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-645617021131834479343856577477651/562949953421312000000000000000000), (-244608299243324069547101283314619/2251799813685248000000000000000000), (201470279871674325170962314669943/2251799813685248000000000000000000), (528463501372586729278040985527/90071992547409920000000000000000), (-85453615904848278702554594027/35184372088832000000000000000000), (-8134359882195942003046359127/70368744177664000000000000000000), (10632269385488293394755841359/281474976710656000000000000000000), (3400186787463689224562509823/2251799813685248000000000000000000), (-415865906284418546530221713/1125899906842624000000000000000000), (-7542978527744861836990551/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial128.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial128.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial128.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial128.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial128 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial128 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial128 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 3308784182495209460076546186774381), (Int.ofNat 226791713059844858273683140297045), (Int.ofNat 232264285711132099604657087009986), (Int.negOfNat 27608040681993573312329872816409), (Int.negOfNat 6125909748668834560236843633161), (Int.ofNat 680345200905828459019031544233), (Int.ofNat 94408463716346727148693684811), (Int.negOfNat 8642598337465319257062528503), (Int.negOfNat 912991318681923608878105626), (Int.ofNat 67622256744320131384891444), (Int.ofNat 5945759910769679231096861), (Int.negOfNat 359246776831777827563730), (Int.negOfNat 27772042260456111627575), (Int.ofNat 1384054799781946029797), (Int.ofNat 98006230544177100515), (Int.negOfNat 4053179951647475427), (Int.negOfNat 260152098044601842), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-3308784182495209460076546186774381/2251799813685248000000000000000000), (45358342611968971654736628059409/450359962737049600000000000000000), (116132142855566049802328543504993/1125899906842624000000000000000000), (-27608040681993573312329872816409/2251799813685248000000000000000000), (-6125909748668834560236843633161/2251799813685248000000000000000000), (680345200905828459019031544233/2251799813685248000000000000000000), (94408463716346727148693684811/2251799813685248000000000000000000), (-8642598337465319257062528503/2251799813685248000000000000000000), (-456495659340961804439052813/1125899906842624000000000000000000), (16905564186080032846222861/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial128.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial128.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial128.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 2218509410868201563984262353844103), (Int.ofNat 696452108392374278390250362967546), (Int.negOfNat 10395692725140914715502457108457), (Int.negOfNat 40335061034992942204792308124341), (Int.ofNat 3234036207629120087020215844637), (Int.ofNat 849625538176672780790975808766), (Int.negOfNat 70009568259929430369263302381), (Int.negOfNat 10218661956381052368188856081), (Int.ofNat 751999395868398614265454075), (Int.ofNat 79101990505414790011469013), (Int.negOfNat 5055098046346634775891086), (Int.negOfNat 425968824737003235753579), (Int.ofNat 23618674462114879904497), (Int.ofNat 1691851246744744848381), (Int.negOfNat 81849389306185104108), (Int.negOfNat 5176058043292893501), (Int.ofNat 226374249902533136), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-2218509410868201563984262353844103/2251799813685248000000000000000000), (348226054196187139195125181483773/1125899906842624000000000000000000), (-10395692725140914715502457108457/2251799813685248000000000000000000), (-40335061034992942204792308124341/2251799813685248000000000000000000), (3234036207629120087020215844637/2251799813685248000000000000000000), (424812769088336390395487904383/1125899906842624000000000000000000), (-70009568259929430369263302381/2251799813685248000000000000000000), (-10218661956381052368188856081/2251799813685248000000000000000000), (30079975834735944570618163/90071992547409920000000000000000), (79101990505414790011469013/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial128.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial128.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial128.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 1116497385451615754234655489866526), (Int.ofNat 325210287274222374657064343368397), (Int.negOfNat 128844697192351334031116389282006), (Int.ofNat 4278550914124744219813393099639), (Int.ofNat 5747253092430130368580572489170), (Int.negOfNat 402996645932688851817583529848), (Int.negOfNat 97278772488291671072161057876), (Int.ofNat 6843437820269227365953397747), (Int.ofNat 941244293438685776825246512), (Int.negOfNat 61302627100046729551324791), (Int.negOfNat 5990257908583940539935692), (Int.ofNat 355791743041653882609005), (Int.ofNat 27183491062390045383520), (Int.negOfNat 1472124382685140795522), (Int.negOfNat 92981466580984353809), (Int.ofNat 4518237562366284151), (Int.ofNat 220526966367102799), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-558248692725807877117327744933263/1125899906842624000000000000000000), (325210287274222374657064343368397/2251799813685248000000000000000000), (-64422348596175667015558194641003/1125899906842624000000000000000000), (4278550914124744219813393099639/2251799813685248000000000000000000), (574725309243013036858057248917/225179981368524800000000000000000), (-50374580741586106477197941231/281474976710656000000000000000000), (-24319693122072917768040264469/562949953421312000000000000000000), (6843437820269227365953397747/2251799813685248000000000000000000), (58827768339917861051577907/140737488355328000000000000000000), (-61302627100046729551324791/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial128.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial128.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial128.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 873312652791360893044395539920295), (Int.negOfNat 1968676738417454118049714857806), (Int.negOfNat 14880354015161329471672339785722), (Int.ofNat 23687167604084250628072073520202), (Int.negOfNat 1458911197417908544473876864429), (Int.negOfNat 732995708292988727326817552438), (Int.ofNat 49112312213084382153540032337), (Int.ofNat 9698902153933599971054180150), (Int.negOfNat 629558782736764646073263884), (Int.negOfNat 76030594942527580719216620), (Int.ofNat 4693342293500887966937873), (Int.ofNat 402875044722974861040299), (Int.negOfNat 23628480319377162086774), (Int.negOfNat 1557389380561569382900), (Int.ofNat 86949497613252341408), (Int.ofNat 4484061019726762494), (Int.negOfNat 256904474710960319), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-174662530558272178608879107984059/450359962737049600000000000000000), (-984338369208727059024857428903/1125899906842624000000000000000000), (-7440177007580664735836169892861/1125899906842624000000000000000000), (11843583802042125314036036760101/1125899906842624000000000000000000), (-1458911197417908544473876864429/2251799813685248000000000000000000), (-366497854146494363663408776219/1125899906842624000000000000000000), (49112312213084382153540032337/2251799813685248000000000000000000), (193978043078671999421083603/45035996273704960000000000000000), (-157389695684191161518315971/562949953421312000000000000000000), (-3801529747126379035960831/112589990684262400000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial128.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial128.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial128.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 789882447485566141739486040048221), (Int.ofNat 130413848148816000092591061229202), (Int.ofNat 50478827530502504358175032882927), (Int.negOfNat 5465443140786220281348096962836), (Int.negOfNat 4061466400640817623628304887680), (Int.ofNat 282691623872093292331792984477), (Int.ofNat 83356650373892849912120070786), (Int.negOfNat 5415318161911976375364813428), (Int.negOfNat 853181871672871819697552088), (Int.ofNat 53706584258701425900797308), (Int.ofNat 5446293026184364351007633), (Int.negOfNat 336383773749129139978263), (Int.negOfNat 24211769668840600154103), (Int.ofNat 1477431226957230572473), (Int.ofNat 80126648354363953496), (Int.negOfNat 4890220515965953323), (Int.negOfNat 170725093086794695), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-789882447485566141739486040048221/2251799813685248000000000000000000), (65206924074408000046295530614601/1125899906842624000000000000000000), (50478827530502504358175032882927/2251799813685248000000000000000000), (-1366360785196555070337024240709/562949953421312000000000000000000), (-6346041251001277536919226387/3518437208883200000000000000000), (282691623872093292331792984477/2251799813685248000000000000000000), (41678325186946424956060035393/1125899906842624000000000000000000), (-1353829540477994093841203357/562949953421312000000000000000000), (-106647733959108977462194011/281474976710656000000000000000000), (13426646064675356475199327/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial128.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial128.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial128.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 422344766365854540001283114624213), (Int.ofNat 172244329266083578425713260642956), (Int.negOfNat 42036720980348259980702014032292), (Int.negOfNat 17517997282328122650084920922083), (Int.ofNat 1568070359224917343373463517825), (Int.ofNat 586202387771321403759133307185), (Int.negOfNat 39656352545399185161824189791), (Int.negOfNat 8305233425245248409266046276), (Int.ofNat 529831180176596926078940587), (Int.ofNat 66281778210927713058235320), (Int.negOfNat 4219361115518898122766365), (Int.negOfNat 346842414027256038228187), (Int.ofNat 22492750689172427283536), (Int.ofNat 1299457194625787972386), (Int.negOfNat 86687960352691818453), (Int.negOfNat 3718588370780506451), (Int.ofNat 287434699519387502), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-422344766365854540001283114624213/2251799813685248000000000000000000), (43061082316520894606428315160739/562949953421312000000000000000000), (-10509180245087064995175503508073/562949953421312000000000000000000), (-17517997282328122650084920922083/2251799813685248000000000000000000), (62722814368996693734938540713/90071992547409920000000000000000), (117240477554264280751826661437/450359962737049600000000000000000), (-39656352545399185161824189791/2251799813685248000000000000000000), (-2076308356311312102316511569/562949953421312000000000000000000), (529831180176596926078940587/2251799813685248000000000000000000), (1657044455273192826455883/56294995342131200000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial128.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial128.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial128.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 345735800952557394760066949340818), (Int.negOfNat 119708482133711048502831490838779), (Int.negOfNat 76515263929196549248047954313504), (Int.ofNat 8707886192424722079398420010600), (Int.ofNat 3517776805675982887074707150052), (Int.negOfNat 257994762140045513689429648554), (Int.negOfNat 69810226887373927995871841393), (Int.ofNat 4504954955469261087001435868), (Int.ofNat 718460721372214719139145469), (Int.negOfNat 46284510205357544051102898), (Int.negOfNat 4537705865695952925228220), (Int.ofNat 304903958280970985671810), (Int.ofNat 19576965356570964905449), (Int.negOfNat 1399372148668732361415), (Int.negOfNat 61602463634069743841), (Int.ofNat 4746577042295022093), (Int.ofNat 120923219806486591), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-172867900476278697380033474670409/1125899906842624000000000000000000), (-119708482133711048502831490838779/2251799813685248000000000000000000), (-2391101997787392164001498572297/70368744177664000000000000000000), (43539430962123610396992100053/11258999068426240000000000000000), (879444201418995721768676787513/562949953421312000000000000000000), (-128997381070022756844714824277/1125899906842624000000000000000000), (-69810226887373927995871841393/2251799813685248000000000000000000), (1126238738867315271750358967/562949953421312000000000000000000), (718460721372214719139145469/2251799813685248000000000000000000), (-23142255102678772025551449/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial128.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial128.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial128.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 777257081198414186413814401678918), (Int.negOfNat 240121304066513350146300307752535), (Int.ofNat 26823586022773963460992358228497), (Int.ofNat 18867043352973858113055609811383), (Int.negOfNat 1417528478040217599860936037584), (Int.negOfNat 514841227841600668405153452760), (Int.ofNat 32700470557050173082224779925), (Int.ofNat 6912829158871872845234830463), (Int.negOfNat 439186826643937644340265119), (Int.negOfNat 53811798235218821701951141), (Int.ofNat 3647684574000089723651609), (Int.ofNat 272437744706309835610285), (Int.negOfNat 20272486977805316897888), (Int.negOfNat 969190915080745821827), (Int.ofNat 80597098918203047524), (Int.ofNat 2445713448928841636), (Int.negOfNat 301364299901045317), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-388628540599207093206907200839459/1125899906842624000000000000000000), (-48024260813302670029260061550507/450359962737049600000000000000000), (26823586022773963460992358228497/2251799813685248000000000000000000), (18867043352973858113055609811383/2251799813685248000000000000000000), (-88595529877513599991308502349/140737488355328000000000000000000), (-12871030696040016710128836319/56294995342131200000000000000000), (1308018822282006923288991197/90071992547409920000000000000000), (6912829158871872845234830463/2251799813685248000000000000000000), (-439186826643937644340265119/2251799813685248000000000000000000), (-53811798235218821701951141/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial128.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial128.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial128.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 1035582480980949417585312104467623), (Int.ofNat 15852283667597728109118918115867), (Int.ofNat 76324611066590022172144408026046), (Int.negOfNat 4974856303760676954683190683077), (Int.negOfNat 3319481802345021304255917077651), (Int.ofNat 188186077959335155179050133995), (Int.ofNat 59068419075897224287464245145), (Int.negOfNat 3504830024969702363216675271), (Int.negOfNat 575280688806385725114584439), (Int.ofNat 37930918335211972962208685), (Int.ofNat 3480209510658196917996385), (Int.negOfNat 261162951264458664231109), (Int.negOfNat 14177452876626541800508), (Int.ofNat 1239460046469670501795), (Int.ofNat 40945629533035099004), (Int.negOfNat 4373808411889584764), (Int.negOfNat 67368487747329733), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-1035582480980949417585312104467623/2251799813685248000000000000000000), (15852283667597728109118918115867/2251799813685248000000000000000000), (38162305533295011086072204013023/1125899906842624000000000000000000), (-4974856303760676954683190683077/2251799813685248000000000000000000), (-3319481802345021304255917077651/2251799813685248000000000000000000), (37637215591867031035810026799/450359962737049600000000000000000), (11813683815179444857492849029/450359962737049600000000000000000), (-3504830024969702363216675271/2251799813685248000000000000000000), (-575280688806385725114584439/2251799813685248000000000000000000), (7586183667042394592441737/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial128.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial128.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial128.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 782261183318941885525054366589264), (Int.ofNat 179567796989762857130855688244355), (Int.negOfNat 7140157346105763378858100742585), (Int.negOfNat 17300798931795785012322667689600), (Int.ofNat 668184045428380305011168444794), (Int.ofNat 440686132364067242416232769372), (Int.negOfNat 21654672627128967550276143053), (Int.negOfNat 5497757976287715114729327896), (Int.ofNat 332129906835034769594383665), (Int.ofNat 40498131082071611873189158), (Int.negOfNat 2945428040818602811845772), (Int.negOfNat 192434026283040772960850), (Int.ofNat 17028921710465461794961), (Int.ofNat 621110299480812117863), (Int.negOfNat 69567391009070136017), (Int.negOfNat 1372478610083059181), (Int.ofNat 288516534253124703), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-48891323957433867845315897911829/140737488355328000000000000000000), (35913559397952571426171137648871/450359962737049600000000000000000), (-1428031469221152675771620148517/450359962737049600000000000000000), (-5406499666186182816350833653/703687441776640000000000000000), (334092022714190152505584222397/1125899906842624000000000000000000), (110171533091016810604058192343/562949953421312000000000000000000), (-21654672627128967550276143053/2251799813685248000000000000000000), (-687219747035964389341165987/281474976710656000000000000000000), (66425981367006953918876733/450359962737049600000000000000000), (20249065541035805936594579/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial128.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial128.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial128.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 567286897543880711925282696897403), (Int.negOfNat 6169728348910223101952445178138), (Int.negOfNat 67801592790406064675216494586185), (Int.negOfNat 109802317630223351155353985112), (Int.ofNat 2726263351491865296163760529283), (Int.negOfNat 78127796277634122957485108187), (Int.negOfNat 45863473283898511294228763815), (Int.ofNat 2272555968324864093013703404), (Int.ofNat 423533264245790334427942579), (Int.negOfNat 28262286082449130951431328), (Int.negOfNat 2401819914089776817164641), (Int.ofNat 206446502732842214484763), (Int.ofNat 8823632015603996542804), (Int.negOfNat 1009738786447455027762), (Int.negOfNat 20755950975486117093), (Int.ofNat 3475743967188375123), (Int.ofNat 20237638512133182), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-567286897543880711925282696897403/2251799813685248000000000000000000), (-3084864174455111550976222589069/1125899906842624000000000000000000), (-13560318558081212935043298917237/450359962737049600000000000000000), (-13725289703777918894419248139/281474976710656000000000000000000), (2726263351491865296163760529283/2251799813685248000000000000000000), (-78127796277634122957485108187/2251799813685248000000000000000000), (-9172694656779702258845752763/450359962737049600000000000000000), (568138992081216023253425851/562949953421312000000000000000000), (423533264245790334427942579/2251799813685248000000000000000000), (-883196440076535342232229/70368744177664000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial128.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial128.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial128.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 813143449722813183136897798509212), (Int.negOfNat 205132434182624926915097509959216), (Int.negOfNat 18153072131056026710143149003799), (Int.ofNat 13089219282909160957252095942822), (Int.ofNat 167073089979123694169425876043), (Int.negOfNat 317541498370341475106594361746), (Int.ofNat 9670724606303509955872168238), (Int.ofNat 3872954568941478250569798480), (Int.negOfNat 217833584561262593613456828), (Int.negOfNat 27121967408631388555632424), (Int.ofNat 2157248861580515574608409), (Int.ofNat 116717574489481931193139), (Int.negOfNat 13030446370642479570179), (Int.negOfNat 304674871575336902209), (Int.ofNat 54156070845032418100), (Int.ofNat 374421431660816771), (Int.negOfNat 238714660972816599), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-203285862430703295784224449627303/562949953421312000000000000000000), (-12820777136414057932193594372451/140737488355328000000000000000000), (-18153072131056026710143149003799/2251799813685248000000000000000000), (6544609641454580478626047971411/1125899906842624000000000000000000), (167073089979123694169425876043/2251799813685248000000000000000000), (-158770749185170737553297180873/1125899906842624000000000000000000), (4835362303151754977936084119/1125899906842624000000000000000000), (48411932111768478132122481/28147497671065600000000000000000), (-54458396140315648403364207/562949953421312000000000000000000), (-3390245926078923569454053/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial128.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial128.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial128.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 1197747605058934626490244679490473), (Int.negOfNat 137412730534530771065206584174546), (Int.ofNat 43424170632269173767017513067099), (Int.ofNat 4940698052237769067310864297834), (Int.negOfNat 1664784187349214394395224924703), (Int.negOfNat 8950778690809612954718907526), (Int.ofNat 29446557889697800865166694962), (Int.negOfNat 1170904397439448988589039938), (Int.negOfNat 269196127248894918561539848), (Int.ofNat 18644423041860865614118288), (Int.ofNat 1412014965350067225910737), (Int.negOfNat 146546590918342970321439), (Int.negOfNat 4209869102146311779674), (Int.ofNat 735894414002272877716), (Int.ofNat 4571597189477077996), (Int.negOfNat 2514751675750616894), (Int.ofNat 10292586296294001), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-1197747605058934626490244679490473/2251799813685248000000000000000000), (-68706365267265385532603292087273/1125899906842624000000000000000000), (43424170632269173767017513067099/2251799813685248000000000000000000), (2470349026118884533655432148917/1125899906842624000000000000000000), (-1664784187349214394395224924703/2251799813685248000000000000000000), (-4475389345404806477359453763/1125899906842624000000000000000000), (14723278944848900432583347481/1125899906842624000000000000000000), (-585452198719724494294519969/1125899906842624000000000000000000), (-33649515906111864820192481/281474976710656000000000000000000), (1165276440116304100882393/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial128.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial128.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial128.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 1284597300869373897285278071783126), (Int.ofNat 46485160611483327641284861613292), (Int.ofNat 38293288493874754892078153285778), (Int.negOfNat 5046792508022609500447257373616), (Int.negOfNat 529156296621810923290014849484), (Int.ofNat 169905168782597881563803577817), (Int.negOfNat 2079462865260256350566331804), (Int.negOfNat 2239459377972587814566826675), (Int.ofNat 122937577418238104160415696), (Int.ofNat 15170205440255140092806095), (Int.negOfNat 1393947791105436895939400), (Int.negOfNat 54557152936360040568357), (Int.ofNat 8758193353281851813564), (Int.ofNat 62097531372406010282), (Int.negOfNat 36764311209455340561), (Int.ofNat 475237196961251321), (Int.ofNat 188912787692508495), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-642298650434686948642639035891563/1125899906842624000000000000000000), (11621290152870831910321215403323/562949953421312000000000000000000), (19146644246937377446039076642889/1125899906842624000000000000000000), (-315424531751413093777953585851/140737488355328000000000000000000), (-132289074155452730822503712371/562949953421312000000000000000000), (169905168782597881563803577817/2251799813685248000000000000000000), (-519865716315064087641582951/562949953421312000000000000000000), (-89578375118903512582673067/90071992547409920000000000000000), (7683598588639881510025981/140737488355328000000000000000000), (3034041088051028018561219/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial128.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial128.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial128.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1082239701672656836385400509791056), (Int.ofNat 134506985012742736296698913311935), (Int.ofNat 7174410582389395408124398967847), (Int.negOfNat 3791525243246831228604483899084), (Int.ofNat 596993014983148788936449858527), (Int.ofNat 30515080268590749723813461700), (Int.negOfNat 14453569531263883999817980529), (Int.ofNat 499688798149982482812867861), (Int.ofNat 138587250104906303621931767), (Int.negOfNat 10672283399515301759256025), (Int.negOfNat 642301068310758107778358), (Int.ofNat 89295955338558109643163), (Int.ofNat 928204531891979116745), (Int.negOfNat 451934875460029420021), (Int.ofNat 6109587290584205380), (Int.ofNat 1546686256639811101), (Int.negOfNat 40822811104721184), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-67639981354541052274087531861941/140737488355328000000000000000000), (26901397002548547259339782662387/450359962737049600000000000000000), (7174410582389395408124398967847/2251799813685248000000000000000000), (-947881310811707807151120974771/562949953421312000000000000000000), (596993014983148788936449858527/2251799813685248000000000000000000), (305150802685907497238134617/22517998136852480000000000000000), (-14453569531263883999817980529/2251799813685248000000000000000000), (499688798149982482812867861/2251799813685248000000000000000000), (138587250104906303621931767/2251799813685248000000000000000000), (-426891335980612070370241/90071992547409920000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial128.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial128.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial128.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 805163449200349077494465319492278), (Int.ofNat 136815124028406161615129558404332), (Int.negOfNat 1744488066244130942460692387622), (Int.ofNat 357136483349615901983079149913), (Int.ofNat 282131454154738422962722905170), (Int.negOfNat 62965445197346812226949542888), (Int.ofNat 18046447049817581975006767), (Int.ofNat 1014014355004352208471160767), (Int.negOfNat 60227604677731437850000810), (Int.negOfNat 6597787476279003412866972), (Int.ofNat 751768954810316905774141), (Int.ofNat 14044616640673997582514), (Int.negOfNat 4758678358746811694555), (Int.ofNat 76268268997361146075), (Int.ofNat 19071393368790758667), (Int.negOfNat 753945505631684245), (Int.negOfNat 128934172809391330), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-402581724600174538747232659746139/1125899906842624000000000000000000), (34203781007101540403782389601083/562949953421312000000000000000000), (-872244033122065471230346193811/1125899906842624000000000000000000), (357136483349615901983079149913/2251799813685248000000000000000000), (28213145415473842296272290517/225179981368524800000000000000000), (-7870680649668351528368692861/281474976710656000000000000000000), (18046447049817581975006767/2251799813685248000000000000000000), (1014014355004352208471160767/2251799813685248000000000000000000), (-6022760467773143785000081/225179981368524800000000000000000), (-1649446869069750853216743/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial128.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial128.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial128.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 533041920050028404873646393391558), (Int.ofNat 138498545824415202950365289445296), (Int.ofNat 2688421319446333997953248120283), (Int.ofNat 534547671088634636886708795049), (Int.negOfNat 146434183101485039110562632241), (Int.negOfNat 11817521377800985117801727529), (Int.ofNat 5516481435448870733284861305), (Int.negOfNat 209109586699584158277372601), (Int.negOfNat 56729792962388687575499110), (Int.ofNat 4961147152227700658198228), (Int.ofNat 196613466749834674573411), (Int.negOfNat 41350904567537620888630), (Int.ofNat 646745416582307244147), (Int.ofNat 195292399877143842579), (Int.negOfNat 9888131497003657755), (Int.negOfNat 448358187737616461), (Int.ofNat 27975045456800570), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-266520960025014202436823196695779/1125899906842624000000000000000000), (8656159114025950184397830590331/140737488355328000000000000000000), (2688421319446333997953248120283/2251799813685248000000000000000000), (534547671088634636886708795049/2251799813685248000000000000000000), (-146434183101485039110562632241/2251799813685248000000000000000000), (-11817521377800985117801727529/2251799813685248000000000000000000), (1103296287089774146656972261/450359962737049600000000000000000), (-209109586699584158277372601/2251799813685248000000000000000000), (-5672979296238868757549911/225179981368524800000000000000000), (1240286788056925164549557/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial128.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial128.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial128.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.negOfNat 243421442586019580189907607940583), (Int.ofNat 150954896035008908580950477306589), (Int.ofNat 2541691711001946813853706153541), (Int.negOfNat 417684452859588445145036248579), (Int.negOfNat 34667249061181524357449105354), (Int.ofNat 21883124971193841600286195164), (Int.negOfNat 309079710401794317026016703), (Int.negOfNat 399093726169509672765315435), (Int.ofNat 24347468520169200636203049), (Int.ofNat 2428918563888102377756055), (Int.negOfNat 282234677175837396531202), (Int.ofNat 1012139524737603118539), (Int.ofNat 1526266866402927382055), (Int.negOfNat 98070513881180088957), (Int.negOfNat 4327377535748463212), (Int.ofNat 808183379769693469), (Int.ofNat 75379440750234472), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-243421442586019580189907607940583/2251799813685248000000000000000000), (150954896035008908580950477306589/2251799813685248000000000000000000), (2541691711001946813853706153541/2251799813685248000000000000000000), (-417684452859588445145036248579/2251799813685248000000000000000000), (-17333624530590762178724552677/1125899906842624000000000000000000), (5470781242798460400071548791/562949953421312000000000000000000), (-309079710401794317026016703/2251799813685248000000000000000000), (-79818745233901934553063087/450359962737049600000000000000000), (24347468520169200636203049/2251799813685248000000000000000000), (485783712777620475551211/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial128.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial128.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial128.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 65395554638925116444443633286989), (Int.ofNat 156541736505710828828882027840765), (Int.ofNat 663537557627563878804448241631), (Int.negOfNat 40105430740298448480292941884), (Int.ofNat 87339852579023787268382879057), (Int.negOfNat 1671447823116595259084025092), (Int.negOfNat 2403575735365009000176157700), (Int.ofNat 101689010969601879061769517), (Int.ofNat 26345468166274682126711904), (Int.negOfNat 1502038564147274540572801), (Int.negOfNat 90232784790608609252080), (Int.ofNat 7847163588013114817635), (Int.negOfNat 479114367407384457132), (Int.negOfNat 1726724535418227334), (Int.ofNat 6458217597118879249), (Int.negOfNat 179959878510787183), (Int.ofNat 11650086220698473), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(65395554638925116444443633286989/2251799813685248000000000000000000), (31308347301142165765776405568153/450359962737049600000000000000000), (663537557627563878804448241631/2251799813685248000000000000000000), (-10026357685074612120073235471/562949953421312000000000000000000), (87339852579023787268382879057/2251799813685248000000000000000000), (-417861955779148814771006273/562949953421312000000000000000000), (-24035757353650090001761577/22517998136852480000000000000000), (101689010969601879061769517/2251799813685248000000000000000000), (823295880196083816459747/70368744177664000000000000000000), (-1502038564147274540572801/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial128.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial128.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial128.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 382021370282703968675949426135281), (Int.ofNat 160982983437760203176581222750783), (Int.ofNat 1916263173809086136799373210919), (Int.ofNat 302160699936518150291127362362), (Int.negOfNat 22602232543314974853785150435), (Int.negOfNat 13736744778297988469438901060), (Int.ofNat 749793509728531384067524155), (Int.ofNat 251782245887367223949296206), (Int.negOfNat 9436549625371632776171200), (Int.negOfNat 2126339687425650729319848), (Int.ofNat 24731202576283326130895), (Int.ofNat 7190111429796305526721), (Int.ofNat 498208419858333771122), (Int.ofNat 13774698886722283836), (Int.negOfNat 5631407709762999508), (Int.negOfNat 279446811733157382), (Int.negOfNat 44849215941807289), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(382021370282703968675949426135281/2251799813685248000000000000000000), (160982983437760203176581222750783/2251799813685248000000000000000000), (1916263173809086136799373210919/2251799813685248000000000000000000), (151080349968259075145563681181/1125899906842624000000000000000000), (-4520446508662994970757030087/450359962737049600000000000000000), (-686837238914899423471945053/112589990684262400000000000000000), (149958701945706276813504831/450359962737049600000000000000000), (125891122943683611974648103/1125899906842624000000000000000000), (-5897843515857270485107/1407374883553280000000000000000), (-265792460928206341164981/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial128.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial128.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial128.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 713345216472992252038456036207460), (Int.ofNat 170694170087822881136206383568852), (Int.ofNat 2410794825109885519301685235305), (Int.negOfNat 194764260539907179293449725492), (Int.negOfNat 62927398931402166759745078120), (Int.ofNat 8356970705577906150055555844), (Int.ofNat 2006083509714632494757277170), (Int.negOfNat 132271773531788108810430176), (Int.negOfNat 30446726074131265515787508), (Int.ofNat 588325207323457583389304), (Int.ofNat 247944329053194664773559), (Int.ofNat 6149306173568324893243), (Int.negOfNat 1129709231936415221965), (Int.negOfNat 97515249067331574537), (Int.ofNat 2612757245387549444), (Int.ofNat 715203287640051275), (Int.negOfNat 61451959501006577), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(35667260823649612601922801810373/112589990684262400000000000000000), (42673542521955720284051595892213/562949953421312000000000000000000), (482158965021977103860337047061/450359962737049600000000000000000), (-48691065134976794823362431373/562949953421312000000000000000000), (-1573184973285054168993626953/56294995342131200000000000000000), (2089242676394476537513888961/562949953421312000000000000000000), (200608350971463249475727717/225179981368524800000000000000000), (-4133492922868378400325943/70368744177664000000000000000000), (-7611681518532816378946877/562949953421312000000000000000000), (73540650915432197923663/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial128.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial128.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial128.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 1062183433087313107292050243045737), (Int.ofNat 176952453714807608063400719251534), (Int.ofNat 744172263959173190826115267904), (Int.negOfNat 164485731276103512044488630316), (Int.ofNat 75660626579214139459194223738), (Int.ofNat 10904179372279760748185939680), (Int.negOfNat 2021087338576642472450990473), (Int.negOfNat 301423491611661640361892660), (Int.ofNat 20912062224350846011578557), (Int.ofNat 4148597706444346559602448), (Int.negOfNat 42149056080058304482543), (Int.negOfNat 31992777444020472932933), (Int.negOfNat 901187135640321009244), (Int.ofNat 150197961395871221158), (Int.ofNat 9392878197237902573), (Int.negOfNat 322765381683503741), (Int.ofNat 14318991133380106), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(1062183433087313107292050243045737/2251799813685248000000000000000000), (88476226857403804031700359625767/1125899906842624000000000000000000), (11627691624362081106658051061/35184372088832000000000000000000), (-41121432819025878011122157579/562949953421312000000000000000000), (37830313289607069729597111869/1125899906842624000000000000000000), (68151121076748504676162123/14073748835532800000000000000000), (-2021087338576642472450990473/2251799813685248000000000000000000), (-15071174580583082018094633/112589990684262400000000000000000), (20912062224350846011578557/2251799813685248000000000000000000), (259287356652771659975153/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial128.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial128.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial128.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 1419148082253962429976984857630528), (Int.ofNat 180756084842472806186992148117821), (Int.ofNat 1813000495700541825123201381680), (Int.ofNat 442522225378396716653034617668), (Int.ofNat 17218177597283582524547798850), (Int.negOfNat 22256194963641789774156705519), (Int.negOfNat 1740249457878624093131286923), (Int.ofNat 417938861246469905622719576), (Int.ofNat 46096516240292473515263007), (Int.negOfNat 3210025718515091210626354), (Int.negOfNat 555479636909589392120572), (Int.ofNat 5013778111611831378710), (Int.ofNat 3688904801550665802239), (Int.ofNat 78181913955616418239), (Int.negOfNat 15673056077903444879), (Int.negOfNat 734820269498714965), (Int.ofNat 111253832781314681), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(22174188785218162968390388400477/35184372088832000000000000000000), (180756084842472806186992148117821/2251799813685248000000000000000000), (22662506196256772814040017271/28147497671065600000000000000000), (110630556344599179163258654417/562949953421312000000000000000000), (344363551945671650490955977/45035996273704960000000000000000), (-22256194963641789774156705519/2251799813685248000000000000000000), (-1740249457878624093131286923/2251799813685248000000000000000000), (52242357655808738202839947/281474976710656000000000000000000), (46096516240292473515263007/2251799813685248000000000000000000), (-1605012859257545605313177/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial128.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial128.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial128.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 1790967458646697275957256643704563), (Int.ofNat 191979060592083348258606525190986), (Int.ofNat 3025880334223274907153327342836), (Int.negOfNat 296920974729261156814052620916), (Int.negOfNat 160825746537323982746536442271), (Int.ofNat 2198591571893683282668172658), (Int.ofNat 5546377507039119402777457511), (Int.ofNat 280912574450511175980644353), (Int.negOfNat 75977648584213841926572905), (Int.negOfNat 6960071568020323962156627), (Int.ofNat 422881658426224930284479), (Int.ofNat 66082898591968175965875), (Int.negOfNat 642774184489084383604), (Int.negOfNat 361970110934382011157), (Int.negOfNat 5183864062762845124), (Int.ofNat 1269119392475978716), (Int.negOfNat 389390751722291), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(1790967458646697275957256643704563/2251799813685248000000000000000000), (95989530296041674129303262595493/1125899906842624000000000000000000), (756470083555818726788331835709/562949953421312000000000000000000), (-74230243682315289203513155229/562949953421312000000000000000000), (-160825746537323982746536442271/2251799813685248000000000000000000), (1099295785946841641334086329/1125899906842624000000000000000000), (5546377507039119402777457511/2251799813685248000000000000000000), (280912574450511175980644353/2251799813685248000000000000000000), (-15195529716842768385314581/450359962737049600000000000000000), (-6960071568020323962156627/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial128.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial128.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial128.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 2182519350220060472143431617613344), (Int.ofNat 196648784042445110090046942122923), (Int.negOfNat 1081265749082100683561639031853), (Int.negOfNat 615314052623277230841949580234), (Int.ofNat 167699823314050651883970011206), (Int.ofNat 49460897761710464530025630499), (Int.negOfNat 1427556768944080759960187869), (Int.negOfNat 1238080748105352322020347033), (Int.negOfNat 57728863796403347336204897), (Int.ofNat 10891700219509711751819667), (Int.ofNat 934409137663591392209567), (Int.negOfNat 45877639150822599372211), (Int.negOfNat 6743360536312533707960), (Int.ofNat 70672936684115585981), (Int.ofNat 30232526844010169356), (Int.ofNat 362051639093277636), (Int.negOfNat 164808564840471539), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(68203729694376889754482238050417/70368744177664000000000000000000), (196648784042445110090046942122923/2251799813685248000000000000000000), (-1081265749082100683561639031853/2251799813685248000000000000000000), (-307657026311638615420974790117/1125899906842624000000000000000000), (83849911657025325941985005603/1125899906842624000000000000000000), (49460897761710464530025630499/2251799813685248000000000000000000), (-1427556768944080759960187869/2251799813685248000000000000000000), (-1238080748105352322020347033/2251799813685248000000000000000000), (-57728863796403347336204897/2251799813685248000000000000000000), (10891700219509711751819667/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial128.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial128.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial128.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 2570577085118822413548627319563844), (Int.ofNat 193404556584628964158114369909023), (Int.ofNat 1989691879684205382086794538912), (Int.ofNat 1749788336807417443896301423368), (Int.ofNat 219074968623039219001392976888), (Int.negOfNat 70024043022946953724333813023), (Int.negOfNat 15805714838261929426078563111), (Int.negOfNat 88454615693828203521541740), (Int.ofNat 201198026222186632248581699), (Int.ofNat 10314017464308977766610830), (Int.negOfNat 1232447868047072582751356), (Int.negOfNat 105424223466402261886710), (Int.ofNat 4201405361982942265951), (Int.ofNat 591018261711334396921), (Int.negOfNat 6364280657684190863), (Int.negOfNat 2342354231321761171), (Int.ofNat 13237156399642905), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(642644271279705603387156829890961/562949953421312000000000000000000), (193404556584628964158114369909023/2251799813685248000000000000000000), (62177871240131418190212329341/70368744177664000000000000000000), (218723542100927180487037677921/281474976710656000000000000000000), (27384371077879902375174122111/281474976710656000000000000000000), (-70024043022946953724333813023/2251799813685248000000000000000000), (-15805714838261929426078563111/2251799813685248000000000000000000), (-4422730784691410176077087/112589990684262400000000000000000), (201198026222186632248581699/2251799813685248000000000000000000), (1031401746430897776661083/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial128.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial128.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial128.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 2979640146085976019716946639420977), (Int.ofNat 220917360834191396671817805097982), (Int.ofNat 8682765901038353881276234964207), (Int.negOfNat 1483773890293805634174091816741), (Int.negOfNat 1207629253354573417452697129873), (Int.negOfNat 168641690391856763674972923845), (Int.ofNat 7088984703536302941269975719), (Int.ofNat 3040982378667402632104853900), (Int.ofNat 80388111325260143896170157), (Int.negOfNat 24490434183308087347559344), (Int.negOfNat 1400953280306523012470851), (Int.ofNat 115313147102575458286757), (Int.ofNat 9989983744561841503544), (Int.negOfNat 337429092890084690934), (Int.negOfNat 45160116332624132827), (Int.ofNat 536012805607932005), (Int.ofNat 211939414075668090), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(2979640146085976019716946639420977/2251799813685248000000000000000000), (110458680417095698335908902548991/1125899906842624000000000000000000), (8682765901038353881276234964207/2251799813685248000000000000000000), (-1483773890293805634174091816741/2251799813685248000000000000000000), (-1207629253354573417452697129873/2251799813685248000000000000000000), (-33728338078371352734994584769/450359962737049600000000000000000), (7088984703536302941269975719/2251799813685248000000000000000000), (30409823786674026321048539/22517998136852480000000000000000), (80388111325260143896170157/2251799813685248000000000000000000), (-1530652136456755459222459/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial128.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial128.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial128.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 3420466958140852427437645433756142), (Int.ofNat 188451351657444112565084268992514), (Int.negOfNat 38930501205653935278105965739651), (Int.negOfNat 15056546159039491877965250381832), (Int.negOfNat 1638801880022242929480426338523), (Int.ofNat 151480473320030393799180114435), (Int.ofNat 39690820524461679956253837667), (Int.ofNat 262581417465336248540080396), (Int.negOfNat 402915973372816164923396096), (Int.negOfNat 15924137291438461875324684), (Int.ofNat 2403245434211216700943999), (Int.ofNat 149551506885415504618001), (Int.negOfNat 9351716727194088241113), (Int.negOfNat 810142158560741109135), (Int.ofNat 24511891838281400240), (Int.ofNat 3013890498684813741), (Int.negOfNat 63039029679951009), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(1710233479070426213718822716878071/1125899906842624000000000000000000), (94225675828722056282542134496257/1125899906842624000000000000000000), (-38930501205653935278105965739651/2251799813685248000000000000000000), (-1882068269879936484745656297729/281474976710656000000000000000000), (-1638801880022242929480426338523/2251799813685248000000000000000000), (30296094664006078759836022887/450359962737049600000000000000000), (39690820524461679956253837667/2251799813685248000000000000000000), (65645354366334062135020099/562949953421312000000000000000000), (-98368157561722696514501/549755813888000000000000000000), (-3981034322859615468831171/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial128.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial128.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial128.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 3502287078472704711256641403239707), (Int.negOfNat 180969710810716123352736098061635), (Int.negOfNat 147544590716452928033203675446507), (Int.negOfNat 16375835119541031443665882420440), (Int.ofNat 1852670994686583072359137201459), (Int.ofNat 459838324623899842415574726440), (Int.negOfNat 2879695186999037732825109406), (Int.negOfNat 5691031460703846320377681306), (Int.negOfNat 160016930562854053835667268), (Int.ofNat 41746942507438090665164324), (Int.ofNat 2014260354883687036240735), (Int.negOfNat 201957206346983972942301), (Int.negOfNat 13170516334895727537114), (Int.ofNat 681903689727930199140), (Int.ofNat 57291811637326587384), (Int.negOfNat 1660265552575285154), (Int.negOfNat 242469638884095273), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(3502287078472704711256641403239707/2251799813685248000000000000000000), (-36193942162143224670547219612327/450359962737049600000000000000000), (-147544590716452928033203675446507/2251799813685248000000000000000000), (-409395877988525786091647060511/56294995342131200000000000000000), (1852670994686583072359137201459/2251799813685248000000000000000000), (11495958115597496060389368161/56294995342131200000000000000000), (-1439847593499518866412554703/1125899906842624000000000000000000), (-2845515730351923160188840653/1125899906842624000000000000000000), (-40004232640713513458916817/562949953421312000000000000000000), (10436735626859522666291081/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial128.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial128.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial128.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 2462589434422377287911955712421807), (Int.negOfNat 874747956377443208174057576729574), (Int.negOfNat 169141556390225085738087647995520), (Int.ofNat 13150181673022598445763104191340), (Int.ofNat 4691063033833736950517729077659), (Int.negOfNat 31077146303141685732514469674), (Int.negOfNat 69230464950126615804032417660), (Int.negOfNat 1609774554972655472167454181), (Int.ofNat 620311140506724926791029768), (Int.ofNat 25132093745442906025171833), (Int.negOfNat 3666767230873181986333748), (Int.negOfNat 195819117543638400671363), (Int.ofNat 15161871921663466481608), (Int.ofNat 992681400163401494142), (Int.negOfNat 45600138310834713959), (Int.negOfNat 3700288671777286913), (Int.ofNat 112840902960259113), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(2462589434422377287911955712421807/2251799813685248000000000000000000), (-437373978188721604087028788364787/1125899906842624000000000000000000), (-264283681859726696465761949993/3518437208883200000000000000000), (657509083651129922288155209567/112589990684262400000000000000000), (4691063033833736950517729077659/2251799813685248000000000000000000), (-15538573151570842866257234837/1125899906842624000000000000000000), (-3461523247506330790201620883/112589990684262400000000000000000), (-1609774554972655472167454181/2251799813685248000000000000000000), (77538892563340615848878721/281474976710656000000000000000000), (25132093745442906025171833/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial128.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial128.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial128.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 211322069302709883435305878041610), (Int.negOfNat 1259225041948845629578614475338856), (Int.ofNat 3342608862161055241842810689215), (Int.ofNat 38641325015656119042074917429094), (Int.ofNat 516483819102328509677926991604), (Int.negOfNat 702049603428842656415380545831), (Int.negOfNat 19547706983167273873450160987), (Int.ofNat 7848227909822062577388503183), (Int.ofNat 303839167049833534454698109), (Int.negOfNat 57123721560401355272267507), (Int.negOfNat 2706008818211113674829754), (Int.ofNat 286856552497192817780637), (Int.ofNat 15812380442963255412463), (Int.negOfNat 1044235291498385049115), (Int.negOfNat 65763640595275223740), (Int.ofNat 2791591427215685867), (Int.ofNat 272999863692522456), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(21132206930270988343530587804161/225179981368524800000000000000000), (-157403130243605703697326809417357/281474976710656000000000000000000), (668521772432211048368562137843/450359962737049600000000000000000), (19320662507828059521037458714547/1125899906842624000000000000000000), (129120954775582127419481747901/562949953421312000000000000000000), (-702049603428842656415380545831/2251799813685248000000000000000000), (-19547706983167273873450160987/2251799813685248000000000000000000), (7848227909822062577388503183/2251799813685248000000000000000000), (303839167049833534454698109/2251799813685248000000000000000000), (-57123721560401355272267507/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial128.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial128.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial128.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 1999028898045154220498980891192612), (Int.negOfNat 821863125099652295051748437818413), (Int.ofNat 192263800359744581635777099338513), (Int.ofNat 16167953633604709752925206158665), (Int.negOfNat 5392082228608388499145980222120), (Int.negOfNat 268549857197429228811293053768), (Int.ofNat 81783052205810878567989225896), (Int.ofNat 3663637480433882304574687649), (Int.negOfNat 760282337549927152201434694), (Int.negOfNat 35293008960773232626053396), (Int.ofNat 4697906484815068421777907), (Int.ofNat 233853498594174985189446), (Int.negOfNat 20559695792789903638977), (Int.negOfNat 1104619436930981673139), (Int.ofNat 67134028917868148373), (Int.ofNat 3815736524918124917), (Int.negOfNat 172819517843376278), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-499757224511288555124745222798153/562949953421312000000000000000000), (-821863125099652295051748437818413/2251799813685248000000000000000000), (192263800359744581635777099338513/2251799813685248000000000000000000), (3233590726720941950585041231733/450359962737049600000000000000000), (-134802055715209712478649505553/56294995342131200000000000000000), (-33568732149678653601411631721/281474976710656000000000000000000), (10222881525726359820998653237/281474976710656000000000000000000), (3663637480433882304574687649/2251799813685248000000000000000000), (-380141168774963576100717347/1125899906842624000000000000000000), (-8823252240193308156513349/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial128.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial128.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial128.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial128.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial128.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial128.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial128.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial128.reflect := by
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

end Bin128
end
end ErdosOverlap.OuterNumerics
