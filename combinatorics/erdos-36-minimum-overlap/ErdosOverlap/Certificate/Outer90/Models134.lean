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

/-! # Exact integer weighted outer models for source bin 134

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin134

def weightDenominator : ℤ := (Int.ofNat 100000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 35471242944938464000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 31969060100849850000)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 22906658811883227000)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 13183250650150535000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 6984778737010287000)⟩, ⟨(19494472361809/1000000000000), (Int.negOfNat 5006942707273226000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 8075577964593902000)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 3302415687364884000)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 730066949844778500)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial134.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial134.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 98849318430202540000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 16376485770507365000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 16959967617243340000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 5730669508402146000)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 966950526665005000)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 1461876319287956500)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 1057467728438801600)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 85814812730343150)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 34415749661679493)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial134.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial134.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 98849318430202540000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 16376485770507365000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 16959967617243340000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 5730669508402146000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 966950526665005000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 1461876319287956500)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 1057467728438801600)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 85814812730343150)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 34415749661679493)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial134.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial134.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial134.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 108767097996195256797714190721544589), (Int.ofNat 45553889342882644796600296850073431), (Int.ofNat 9534009635568833956753277601631940), (Int.negOfNat 1350174415823336336599097051771537), (Int.negOfNat 240259369841353204121037741983921), (Int.ofNat 25107092749066708067356672920937), (Int.ofNat 3314571548961903559906646282867), (Int.negOfNat 287026739147123525825068823067), (Int.negOfNat 28828851400329141585942609872), (Int.ofNat 2181315262753100871533048566), (Int.ofNat 172588939966753399321279057), (Int.negOfNat 11798235112168662726210602), (Int.negOfNat 758182790808280300531751), (Int.ofNat 47783570957838465912071), (Int.ofNat 2552055955795486442155), (Int.negOfNat 147100209978933556105), (Int.negOfNat 6660441125888356392), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-108767097996195256797714190721544589/112589990684262400000000000000000000), (45553889342882644796600296850073431/112589990684262400000000000000000000), (476700481778441697837663880081597/5629499534213120000000000000000000), (-1350174415823336336599097051771537/112589990684262400000000000000000000), (-240259369841353204121037741983921/112589990684262400000000000000000000), (25107092749066708067356672920937/112589990684262400000000000000000000), (3314571548961903559906646282867/112589990684262400000000000000000000), (-287026739147123525825068823067/112589990684262400000000000000000000), (-1801803212520571349121413117/7036874417766400000000000000000000), (1090657631376550435766524283/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial134.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial134.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial134.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial134 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 6803880650603043684186890186241303), (Int.ofNat 62292152170078643149453202310905662), (Int.negOfNat 1762075721454286405891261944677847), (Int.negOfNat 1936220938323357823886819549292103), (Int.ofNat 107569928352911487978062147447225), (Int.ofNat 33237811666056911578339561802610), (Int.negOfNat 2094119602357171086855544648023), (Int.negOfNat 343910777169333177285090048621), (Int.ofNat 22241046475976073748527221371), (Int.ofNat 2358138951309889548999968671), (Int.negOfNat 153709346360598499916872132), (Int.negOfNat 11532965088191082392567205), (Int.ofNat 755538249928518727416775), (Int.ofNat 42498272424286850976507), (Int.negOfNat 2793630349540512348468), (Int.negOfNat 118648559246854347033), (Int.ofNat 8636362147655394622), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(6803880650603043684186890186241303/112589990684262400000000000000000000), (31146076085039321574726601155452831/56294995342131200000000000000000000), (-1762075721454286405891261944677847/112589990684262400000000000000000000), (-1936220938323357823886819549292103/112589990684262400000000000000000000), (4302797134116459519122485897889/4503599627370496000000000000000000), (3323781166605691157833956180261/11258999068426240000000000000000000), (-2094119602357171086855544648023/112589990684262400000000000000000000), (-343910777169333177285090048621/112589990684262400000000000000000000), (22241046475976073748527221371/112589990684262400000000000000000000), (2358138951309889548999968671/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial134.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial134.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial134.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial134 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 111463522642080758062982940806023102), (Int.ofNat 37581629242994471874397784057316145), (Int.negOfNat 8823711402581045519301657994856682), (Int.negOfNat 224017753585956135342270095739299), (Int.ofNat 249978994160976721948752243230240), (Int.negOfNat 7555215348049686719289659682918), (Int.negOfNat 3468544666344416297115022256974), (Int.ofNat 165502002880357353839441923807), (Int.ofNat 28922158556457932533666456948), (Int.negOfNat 1642427279484704597038817673), (Int.negOfNat 162623973134288730365199582), (Int.ofNat 10319016979351099101179613), (Int.ofNat 664212906491010988620960), (Int.negOfNat 45948278345943292895900), (Int.negOfNat 2070929463162342699795), (Int.ofNat 154635713547583058327), (Int.ofNat 4435824526692341399), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(55731761321040379031491470403011551/56294995342131200000000000000000000), (7516325848598894374879556811463229/22517998136852480000000000000000000), (-4411855701290522759650828997428341/56294995342131200000000000000000000), (-224017753585956135342270095739299/112589990684262400000000000000000000), (1562368713506104512179701520189/703687441776640000000000000000000), (-3777607674024843359644829841459/56294995342131200000000000000000000), (-1734272333172208148557511128487/56294995342131200000000000000000000), (165502002880357353839441923807/112589990684262400000000000000000000), (7230539639114483133416614237/28147497671065600000000000000000000), (-1642427279484704597038817673/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial134.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial134.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial134.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial134 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 153103307974032291415720481979700469), (Int.ofNat 6426794912300049968374239168795936), (Int.negOfNat 5451258389307179437523822093620334), (Int.ofNat 1052316471335451343336688541115212), (Int.ofNat 36741164400797426056922243395549), (Int.negOfNat 26585297285754221370167701030550), (Int.ofNat 618211465215832088689287503913), (Int.ofNat 301263931620144309107201688288), (Int.negOfNat 13184801093044819456940959448), (Int.negOfNat 2060092978016794859707305034), (Int.ofNat 117745511796366331188081119), (Int.ofNat 9620683346538820538343483), (Int.negOfNat 661695377262310945871852), (Int.negOfNat 32970790287488282045186), (Int.ofNat 2646527456048288864232), (Int.ofNat 80571507781251428038), (Int.negOfNat 8533114898670356143), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(153103307974032291415720481979700469/112589990684262400000000000000000000), (200837341009376561511694974024873/3518437208883200000000000000000000), (-2725629194653589718761911046810167/56294995342131200000000000000000000), (263079117833862835834172135278803/28147497671065600000000000000000000), (36741164400797426056922243395549/112589990684262400000000000000000000), (-531705945715084427403354020611/2251799813685248000000000000000000), (618211465215832088689287503913/112589990684262400000000000000000000), (9414497863129509659600052759/3518437208883200000000000000000000), (-1648100136630602432117619931/14073748835532800000000000000000000), (-1030046489008397429853652517/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial134.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial134.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial134.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial134 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 152381359709476201059687269824159769), (Int.negOfNat 3465438831558862724171208550281398), (Int.negOfNat 63116952785746137750766193812803), (Int.ofNat 517886162804707306387695557409276), (Int.negOfNat 128842642324947970600408787166984), (Int.negOfNat 2761602690656477018714419178595), (Int.ofNat 2468499020399338202890971868004), (Int.negOfNat 61648338340779707982420353582), (Int.negOfNat 22419240680169854452401320454), (Int.ofNat 1054538649701132210278905528), (Int.ofNat 125657825372401525325309911), (Int.negOfNat 8129032100273353488228985), (Int.negOfNat 485550044231289947720231), (Int.ofNat 40184769840200788725415), (Int.ofNat 1373281824744042176704), (Int.negOfNat 148420851349805715191), (Int.negOfNat 2245623677158005899), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(152381359709476201059687269824159769/112589990684262400000000000000000000), (-1732719415779431362085604275140699/56294995342131200000000000000000000), (-63116952785746137750766193812803/112589990684262400000000000000000000), (129471540701176826596923889352319/28147497671065600000000000000000000), (-16105330290618496325051098395873/14073748835532800000000000000000000), (-552320538131295403742883835719/22517998136852480000000000000000000), (617124755099834550722742967001/28147497671065600000000000000000000), (-30824169170389853991210176791/56294995342131200000000000000000000), (-11209620340084927226200660227/56294995342131200000000000000000000), (131817331212641526284863191/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial134.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial134.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial134.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial134 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 147336253905795229986466527561727123), (Int.negOfNat 1420817617752114331850519587178630), (Int.ofNat 247937160697733102071240016766614), (Int.negOfNat 295843833716100075877032012617657), (Int.negOfNat 45168268912181975897407452253223), (Int.ofNat 14501966968872956680736848564675), (Int.ofNat 85935255582450408362030926983), (Int.negOfNat 198326852202693672424359014956), (Int.ofNat 6401302229382436910262357735), (Int.ofNat 1424790677955244203465604318), (Int.negOfNat 81688938381769916367900735), (Int.negOfNat 6466737767737195894430101), (Int.ofNat 530519439113321268537616), (Int.ofNat 20085639910165788589498), (Int.negOfNat 2284452289736755922141), (Int.negOfNat 41722637409192541903), (Int.ofNat 8429867649685317664), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(147336253905795229986466527561727123/112589990684262400000000000000000000), (-142081761775211433185051958717863/11258999068426240000000000000000000), (123968580348866551035620008383307/56294995342131200000000000000000000), (-295843833716100075877032012617657/112589990684262400000000000000000000), (-45168268912181975897407452253223/112589990684262400000000000000000000), (580078678754918267229473942587/4503599627370496000000000000000000), (85935255582450408362030926983/112589990684262400000000000000000000), (-49581713050673418106089753739/28147497671065600000000000000000000), (1280260445876487382052471547/22517998136852480000000000000000000), (712395338977622101732802159/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial134.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial134.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial134.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial134 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 142843374935108027287201553701841404), (Int.negOfNat 4327412686426745353913139625398265), (Int.negOfNat 1546706522651783172945452887550184), (Int.negOfNat 156757900280688152154098889202322), (Int.ofNat 61091331230842553548571075032696), (Int.ofNat 3821938932106559157335755387630), (Int.negOfNat 1352336916682443548098771630261), (Int.ofNat 11317244453527292091273524948), (Int.ofNat 13385435899268695952349059543), (Int.negOfNat 617907699576003737602387760), (Int.negOfNat 75055212085941582122548260), (Int.ofNat 5915038722374117206765072), (Int.ofNat 264346722136303286079385), (Int.negOfNat 32144162925866932518557), (Int.negOfNat 582560184737763415891), (Int.ofNat 122666538947182935041), (Int.ofNat 55422827623670399), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(35710843733777006821800388425460351/28147497671065600000000000000000000), (-865482537285349070782627925079653/22517998136852480000000000000000000), (-193338315331472896618181610943773/14073748835532800000000000000000000), (-78378950140344076077049444601161/56294995342131200000000000000000000), (7636416403855319193571384379087/14073748835532800000000000000000000), (382193893210655915733575538763/11258999068426240000000000000000000), (-1352336916682443548098771630261/112589990684262400000000000000000000), (2829311113381823022818381237/28147497671065600000000000000000000), (13385435899268695952349059543/112589990684262400000000000000000000), (-7723846244700046720029847/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial134.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial134.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial134.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial134 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 127765369033670775920195891993970704), (Int.negOfNat 10377264310082534003476319492595007), (Int.negOfNat 1011808601847436621683659350758911), (Int.ofNat 294596039272804435855541352181881), (Int.ofNat 33102193058899626679803440487956), (Int.negOfNat 7118856664856810351520587303494), (Int.negOfNat 266271549031738675402985472899), (Int.ofNat 98791080010232834303088832399), (Int.negOfNat 2684850362082923167130956525), (Int.negOfNat 720354109243184678486799895), (Int.ofNat 52993599233991161432351671), (Int.ofNat 2983935889388122081994347), (Int.negOfNat 390467030623135257802754), (Int.negOfNat 6665937289437688285427), (Int.ofNat 1771056222188919541936), (Int.negOfNat 133094235157985372), (Int.negOfNat 7596553450855500685), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(7985335564604423495012243249623169/7036874417766400000000000000000000), (-10377264310082534003476319492595007/112589990684262400000000000000000000), (-1011808601847436621683659350758911/112589990684262400000000000000000000), (294596039272804435855541352181881/112589990684262400000000000000000000), (8275548264724906669950860121989/28147497671065600000000000000000000), (-3559428332428405175760293651747/56294995342131200000000000000000000), (-266271549031738675402985472899/112589990684262400000000000000000000), (98791080010232834303088832399/112589990684262400000000000000000000), (-107394014483316926685238261/4503599627370496000000000000000000), (-144070821848636935697359979/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial134.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial134.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial134.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial134 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 105616812483452639026045408313278257), (Int.negOfNat 10410564129217167322885093077251309), (Int.ofNat 975731237137222641125672764913468), (Int.ofNat 279590390207262005231822278739403), (Int.negOfNat 31524523073696638904357647592465), (Int.negOfNat 4195143397051940103126455358063), (Int.ofNat 530967325091286245271440043201), (Int.ofNat 8855807738676553433941278701), (Int.negOfNat 5215066146339988791886600125), (Int.ofNat 339223002631329594961901595), (Int.ofNat 26277339235566675541214871), (Int.negOfNat 3964602347721897742637347), (Int.negOfNat 53735583617932189956554), (Int.ofNat 23093505295949189704027), (Int.negOfNat 128055865610215962064), (Int.negOfNat 94422049387449732428), (Int.ofNat 1335879572742527615), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(105616812483452639026045408313278257/112589990684262400000000000000000000), (-10410564129217167322885093077251309/112589990684262400000000000000000000), (243932809284305660281418191228367/28147497671065600000000000000000000), (279590390207262005231822278739403/112589990684262400000000000000000000), (-6304904614739327780871529518493/22517998136852480000000000000000000), (-4195143397051940103126455358063/112589990684262400000000000000000000), (530967325091286245271440043201/112589990684262400000000000000000000), (8855807738676553433941278701/112589990684262400000000000000000000), (-41720529170719910335092801/900719925474099200000000000000000), (67844600526265918992380319/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial134.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial134.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial134.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial134 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 90330668167399711737117755863968736), (Int.negOfNat 4395506482111551952790153915625331), (Int.ofNat 1686865562326824499722139993891169), (Int.negOfNat 57782630142233767977348615767590), (Int.negOfNat 43424438363092065141733811774618), (Int.ofNat 1364323907139488141241089592920), (Int.ofNat 330082321192272640842463071839), (Int.negOfNat 20460581247542887456758199048), (Int.ofNat 822238494909377717711953943), (Int.ofNat 128767670979823951774638060), (Int.negOfNat 31672164911398590494343060), (Int.negOfNat 10765992419837825059072), (Int.ofNat 255636661376705181783585), (Int.negOfNat 4511648130732316481043), (Int.negOfNat 1200721027478779218891), (Int.ofNat 32677370486784298759), (Int.ofNat 6067588051842584699), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(2822833380231240991784929870749023/3518437208883200000000000000000000), (-4395506482111551952790153915625331/112589990684262400000000000000000000), (1686865562326824499722139993891169/112589990684262400000000000000000000), (-5778263014223376797734861576759/11258999068426240000000000000000000), (-21712219181546032570866905887309/56294995342131200000000000000000000), (34108097678487203531027239823/2814749767106560000000000000000000), (330082321192272640842463071839/112589990684262400000000000000000000), (-2557572655942860932094774881/14073748835532800000000000000000000), (822238494909377717711953943/112589990684262400000000000000000000), (6438383548991197588731903/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial134.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial134.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial134.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial134 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 87192475036252570736368979518490823), (Int.ofNat 433319840352338147087625398118310), (Int.ofNat 474317209477240693548935287210351), (Int.negOfNat 307544513564817945155489864912678), (Int.negOfNat 14661626539710802107717878426345), (Int.ofNat 4002184871813246138182985429325), (Int.ofNat 128991037700949749372175089883), (Int.negOfNat 13696975694811309597564847144), (Int.negOfNat 930317944324059326704384665), (Int.negOfNat 170867512989421916311911018), (Int.ofNat 10649819750283984664711065), (Int.ofNat 2324838875986971184314101), (Int.negOfNat 103297762885527530004584), (Int.negOfNat 13949320987665160302098), (Int.ofNat 646976794378407847859), (Int.ofNat 52960465716892833703), (Int.negOfNat 1962699273602267636), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(87192475036252570736368979518490823/112589990684262400000000000000000000), (43331984035233814708762539811831/11258999068426240000000000000000000), (474317209477240693548935287210351/112589990684262400000000000000000000), (-153772256782408972577744932456339/56294995342131200000000000000000000), (-2932325307942160421543575685269/22517998136852480000000000000000000), (160087394872529845527319417173/4503599627370496000000000000000000), (128991037700949749372175089883/112589990684262400000000000000000000), (-1712121961851413699695605893/14073748835532800000000000000000000), (-186063588864811865340876933/22517998136852480000000000000000000), (-85433756494710958155955509/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial134.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial134.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial134.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial134 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 87395703046923657458018439991731874), (Int.negOfNat 1491581516560666233679780038381718), (Int.negOfNat 1383175902247440924655788845657795), (Int.negOfNat 254120959448565514313029977178200), (Int.ofNat 27757559806637745057174144669673), (Int.ofNat 3778627752185274622607360794038), (Int.negOfNat 220198922641603268336559407596), (Int.negOfNat 34486117112355985257403713318), (Int.negOfNat 255679441173915973402764854), (Int.ofNat 265842208618581304611876172), (Int.ofNat 16393758960683262554604711), (Int.negOfNat 1922102451827905157058015), (Int.negOfNat 133728521614353344763431), (Int.ofNat 11422732204908480248185), (Int.ofNat 615914687490788856704), (Int.negOfNat 54990107923239129609), (Int.negOfNat 3877387202308249199), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(43697851523461828729009219995865937/56294995342131200000000000000000000), (-745790758280333116839890019190859/56294995342131200000000000000000000), (-276635180449488184931157769131559/22517998136852480000000000000000000), (-1270604797242827571565149885891/562949953421312000000000000000000), (27757559806637745057174144669673/112589990684262400000000000000000000), (1889313876092637311303680397019/56294995342131200000000000000000000), (-55049730660400817084139851899/28147497671065600000000000000000000), (-17243058556177992628701856659/56294995342131200000000000000000000), (-127839720586957986701382427/56294995342131200000000000000000000), (66460552154645326152969043/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial134.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial134.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial134.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial134 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 77393481882452620732612015825221977), (Int.negOfNat 8940522128515748916695522419831938), (Int.negOfNat 2014557890537514035091037820095357), (Int.ofNat 65670828317669022335463809417924), (Int.ofNat 43588165258391676433806423302621), (Int.negOfNat 1273160044418291961024574406350), (Int.negOfNat 531392668161642519238466967480), (Int.ofNat 3339155182541899555044756812), (Int.ofNat 4427254918168882492006193952), (Int.ofNat 87723610873820998012080734), (Int.negOfNat 30611699250149365608037681), (Int.negOfNat 1011099167717408053535483), (Int.ofNat 181766875998996183561348), (Int.ofNat 5504362675176323620786), (Int.negOfNat 861301462856881697768), (Int.negOfNat 15882373305094755838), (Int.ofNat 1859452024617229157), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(77393481882452620732612015825221977/112589990684262400000000000000000000), (-4470261064257874458347761209915969/56294995342131200000000000000000000), (-2014557890537514035091037820095357/112589990684262400000000000000000000), (16417707079417255583865952354481/28147497671065600000000000000000000), (43588165258391676433806423302621/112589990684262400000000000000000000), (-25463200888365839220491488127/2251799813685248000000000000000000), (-13284816704041062980961674187/2814749767106560000000000000000000), (834788795635474888761189203/28147497671065600000000000000000000), (138351716192777577875193561/3518437208883200000000000000000000), (43861805436910499006040367/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial134.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial134.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial134.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial134 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 52603806143167942664870794254491674), (Int.negOfNat 15013694556316500031062007748745864), (Int.negOfNat 793590504873156263753139536299058), (Int.ofNat 288210604207783019986813913543480), (Int.ofNat 4790193801227635478248064157754), (Int.negOfNat 5466550400158094746069429682525), (Int.negOfNat 36376540274330736605324227874), (Int.ofNat 56899363157903172829346255093), (Int.ofNat 656161456602202261292444348), (Int.negOfNat 420960344108984986823348027), (Int.negOfNat 6331317469375435049067382), (Int.ofNat 2576785807260519215509387), (Int.ofNat 31832073718272188599160), (Int.negOfNat 13120514567617256056700), (Int.negOfNat 85372402764800397795), (Int.ofNat 52618789448928579473), (Int.ofNat 1687186352773913699), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(26301903071583971332435397127245837/56294995342131200000000000000000000), (-1876711819539562503882750968593233/14073748835532800000000000000000000), (-396795252436578131876569768149529/56294995342131200000000000000000000), (7205265105194575499670347838587/2814749767106560000000000000000000), (2395096900613817739124032078877/56294995342131200000000000000000000), (-218662016006323789842777187301/4503599627370496000000000000000000), (-18188270137165368302662113937/56294995342131200000000000000000000), (56899363157903172829346255093/112589990684262400000000000000000000), (164040364150550565323111087/28147497671065600000000000000000000), (-420960344108984986823348027/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial134.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial134.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial134.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial134 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 21614359615513482663492199682344226), (Int.negOfNat 14995361824346830920703543930314517), (Int.ofNat 642055493456103382386833781857825), (Int.ofNat 132837667950705678581807468093066), (Int.negOfNat 37065449074426302359572267533397), (Int.negOfNat 1654103256218043260660025860110), (Int.ofNat 566711440000394575978832992877), (Int.ofNat 13721518821142738792860834521), (Int.negOfNat 4921451337929948584822320029), (Int.negOfNat 63920260337754589917885371), (Int.ofNat 32164279501226412176486668), (Int.ofNat 51190285236741928774205), (Int.negOfNat 174754054458778117467425), (Int.ofNat 1465513459467001446893), (Int.ofNat 779106926928181485532), (Int.negOfNat 19047270213780175167), (Int.negOfNat 1756204775632190678), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(10807179807756741331746099841172113/56294995342131200000000000000000000), (-14995361824346830920703543930314517/112589990684262400000000000000000000), (25682219738244135295473351274313/4503599627370496000000000000000000), (66418833975352839290903734046533/56294995342131200000000000000000000), (-37065449074426302359572267533397/112589990684262400000000000000000000), (-165410325621804326066002586011/11258999068426240000000000000000000), (566711440000394575978832992877/112589990684262400000000000000000000), (13721518821142738792860834521/112589990684262400000000000000000000), (-4921451337929948584822320029/112589990684262400000000000000000000), (-63920260337754589917885371/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial134.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial134.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial134.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial134 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 5354653587755341155024513590635032), (Int.negOfNat 12041580341155604883157015721217730), (Int.ofNat 553660957234147705456498136591956), (Int.negOfNat 140177551286152601898831462226265), (Int.negOfNat 21117932019244788129739980251192), (Int.ofNat 4209762495229241734778000697106), (Int.ofNat 264021249614499930884148040767), (Int.negOfNat 47037425641959672923066235833), (Int.negOfNat 1406379708518909664884552272), (Int.ofNat 342519683798461589058991134), (Int.ofNat 672055251881052786540857), (Int.negOfNat 1986798224068136998025398), (Int.ofNat 42227442406071968189049), (Int.ofNat 9689922770290526928529), (Int.negOfNat 322157016703821818845), (Int.negOfNat 39802101454526960695), (Int.ofNat 468598747098742308), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-669331698469417644378064198829379/14073748835532800000000000000000000), (-1204158034115560488315701572121773/11258999068426240000000000000000000), (138415239308536926364124534147989/28147497671065600000000000000000000), (-28035510257230520379766292445253/22517998136852480000000000000000000), (-2639741502405598516217497531399/14073748835532800000000000000000000), (2104881247614620867389000348553/56294995342131200000000000000000000), (264021249614499930884148040767/112589990684262400000000000000000000), (-47037425641959672923066235833/112589990684262400000000000000000000), (-87898731782431854055284517/7036874417766400000000000000000000), (171259841899230794529495567/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial134.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial134.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial134.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial134 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 28537076592642703706334936367529554), (Int.negOfNat 11819109038887380227752946201225682), (Int.negOfNat 426683631460110051149936184610317), (Int.negOfNat 125573234105248244125153723677561), (Int.ofNat 23389949710685486135764517188107), (Int.ofNat 3441033180117355035335120779663), (Int.negOfNat 344677048869908381799699156767), (Int.negOfNat 28128517466246855725778883833), (Int.ofNat 2900447310433779993396931272), (Int.ofNat 72901484635400440068506134), (Int.negOfNat 17807719230604430624477857), (Int.ofNat 511910989349699428257602), (Int.ofNat 92564244130747560114951), (Int.negOfNat 6168266937171435511471), (Int.negOfNat 414757574506556120155), (Int.ofNat 38676833975886287305), (Int.ofNat 227239376619274692), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-14268538296321351853167468183764777/56294995342131200000000000000000000), (-5909554519443690113876473100612841/56294995342131200000000000000000000), (-426683631460110051149936184610317/112589990684262400000000000000000000), (-125573234105248244125153723677561/112589990684262400000000000000000000), (23389949710685486135764517188107/112589990684262400000000000000000000), (3441033180117355035335120779663/112589990684262400000000000000000000), (-344677048869908381799699156767/112589990684262400000000000000000000), (-28128517466246855725778883833/112589990684262400000000000000000000), (362555913804222499174616409/14073748835532800000000000000000000), (36450742317700220034253067/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial134.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial134.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial134.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial134 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 54427159616995798421208106337658137), (Int.negOfNat 14084686376799658132486581517655757), (Int.negOfNat 439758495412427486445094274471881), (Int.ofNat 133633387438937720423687706411647), (Int.ofNat 32577548675823524390276511664396), (Int.negOfNat 1732943554111942858153307078560), (Int.negOfNat 413007599579055198972473667877), (Int.ofNat 15931478604564821975815289521), (Int.ofNat 2113225747053275101766213029), (Int.negOfNat 92761729647817652669224371), (Int.ofNat 789707644456507549802332), (Int.ofNat 435857920632116549944205), (Int.negOfNat 79912332339337862606575), (Int.negOfNat 2138609847199648676107), (Int.ofNat 576508048230271125468), (Int.ofNat 15717331258549039833), (Int.negOfNat 1859901147464940322), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-54427159616995798421208106337658137/112589990684262400000000000000000000), (-14084686376799658132486581517655757/112589990684262400000000000000000000), (-439758495412427486445094274471881/112589990684262400000000000000000000), (133633387438937720423687706411647/112589990684262400000000000000000000), (8144387168955881097569127916099/28147497671065600000000000000000000), (-10830897213199642863458169241/703687441776640000000000000000000), (-413007599579055198972473667877/112589990684262400000000000000000000), (15931478604564821975815289521/112589990684262400000000000000000000), (2113225747053275101766213029/112589990684262400000000000000000000), (-92761729647817652669224371/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial134.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial134.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial134.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial134 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 82844611066933377160451385376013787), (Int.negOfNat 13406476630332424090624634997105169), (Int.ofNat 920226944215970202491960177812513), (Int.ofNat 271086009368754038033373755919718), (Int.negOfNat 3060016804952330654888403979283), (Int.negOfNat 4580024239603662907544761169332), (Int.negOfNat 11271457300949219567953203126), (Int.ofNat 37439937810554942996176964093), (Int.ofNat 550963475562528604581901652), (Int.negOfNat 109631714345315751096487027), (Int.negOfNat 6664771135796829719393618), (Int.negOfNat 590294903362475905927613), (Int.ofNat 41200237084470240175840), (Int.ofNat 7848453295712633327300), (Int.negOfNat 156126726447673243205), (Int.negOfNat 46212337544535789527), (Int.ofNat 1997377222576740301), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-82844611066933377160451385376013787/112589990684262400000000000000000000), (-13406476630332424090624634997105169/112589990684262400000000000000000000), (920226944215970202491960177812513/112589990684262400000000000000000000), (135543004684377019016686877959859/56294995342131200000000000000000000), (-3060016804952330654888403979283/112589990684262400000000000000000000), (-1145006059900915726886190292333/28147497671065600000000000000000000), (-5635728650474609783976601563/56294995342131200000000000000000000), (37439937810554942996176964093/112589990684262400000000000000000000), (137740868890632151145475413/28147497671065600000000000000000000), (-109631714345315751096487027/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial134.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial134.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial134.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial134 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 103999341470912290676670374675675011), (Int.negOfNat 6921978021039220249451900536959677), (Int.ofNat 2129747833443404195345400563062411), (Int.ofNat 82845225468543107460507984524202), (Int.negOfNat 38985007679583707948580973401927), (Int.negOfNat 1609231853187372269870448068400), (Int.ofNat 473741499094887085227665099487), (Int.ofNat 22726677820279228526988243812), (Int.negOfNat 2813397489649390368099669952), (Int.negOfNat 232567087048638617939550266), (Int.ofNat 3165038744002912012104681), (Int.ofNat 1629539544948812691937517), (Int.ofNat 71429012400072042661652), (Int.negOfNat 7817510314016556021214), (Int.negOfNat 596257335537118614232), (Int.ofNat 22359720207053879162), (Int.ofNat 1756653898479901843), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-103999341470912290676670374675675011/112589990684262400000000000000000000), (-6921978021039220249451900536959677/112589990684262400000000000000000000), (2129747833443404195345400563062411/112589990684262400000000000000000000), (41422612734271553730253992262101/56294995342131200000000000000000000), (-38985007679583707948580973401927/112589990684262400000000000000000000), (-4023079632968430674676120171/281474976710656000000000000000000), (473741499094887085227665099487/112589990684262400000000000000000000), (5681669455069807131747060953/28147497671065600000000000000000000), (-43959335775771724501557343/1759218604441600000000000000000000), (-116283543524319308969775133/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial134.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial134.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial134.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial134 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 109304403952921516503115182681370014), (Int.ofNat 1312656229163555714610771227571464), (Int.ofNat 1685383197132152015029197836371011), (Int.negOfNat 211047599698695763872676388406702), (Int.negOfNat 24261040807340772877051895360616), (Int.ofNat 4333312832314705849630630845352), (Int.ofNat 357391285851573565015229605096), (Int.negOfNat 43387655525336267964441880318), (Int.negOfNat 4120334194835642221899701146), (Int.ofNat 199080560051028814419407172), (Int.ofNat 34090331210811196779282289), (Int.ofNat 35456755358046259351985), (Int.negOfNat 196563081521852276139569), (Int.negOfNat 5834733375096722712815), (Int.ofNat 802501012748224583296), (Int.ofNat 39997475346758446391), (Int.negOfNat 4187578072111075801), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-54652201976460758251557591340685007/56294995342131200000000000000000000), (164082028645444464326346403446433/14073748835532800000000000000000000), (1685383197132152015029197836371011/112589990684262400000000000000000000), (-105523799849347881936338194203351/56294995342131200000000000000000000), (-3032630100917596609631486920077/14073748835532800000000000000000000), (541664104039338231203828855669/14073748835532800000000000000000000), (44673910731446695626903700637/14073748835532800000000000000000000), (-21693827762668133982220940159/56294995342131200000000000000000000), (-2060167097417821110949850573/56294995342131200000000000000000000), (49770140012757203604851793/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial134.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial134.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial134.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial134 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 101859049457367284347421155406107273), (Int.ofNat 5137520359587640692414976414739400), (Int.ofNat 234028605108416812577800751214580), (Int.negOfNat 204729340894100409121155401604658), (Int.ofNat 24988479434912455508286597152944), (Int.ofNat 3787904418326567276612589347268), (Int.negOfNat 474874430097597798643228147883), (Int.negOfNat 52953535434774545543271884144), (Int.ofNat 4026008518521525154274639665), (Int.ofNat 535578172689302804480789982), (Int.negOfNat 15321489899528047954157065), (Int.negOfNat 3747923154930269239542899), (Int.negOfNat 7072655387115704646416), (Int.ofNat 18347784065379259453902), (Int.ofNat 374776360216372697141), (Int.negOfNat 61208590579112765297), (Int.negOfNat 1653406649494863364), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-101859049457367284347421155406107273/112589990684262400000000000000000000), (25687601797938203462074882073697/562949953421312000000000000000000), (11701430255420840628890037560729/5629499534213120000000000000000000), (-102364670447050204560577700802329/56294995342131200000000000000000000), (1561779964682028469267912322059/7036874417766400000000000000000000), (946976104581641819153147336817/28147497671065600000000000000000000), (-474874430097597798643228147883/112589990684262400000000000000000000), (-3309595964673409096454492759/7036874417766400000000000000000000), (805201703704305030854927933/22517998136852480000000000000000000), (267789086344651402240394991/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial134.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial134.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial134.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial134 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 91800588814185671170020426730503922), (Int.ofNat 4609884081383961531420137443763811), (Int.negOfNat 231743180634991790592987859342270), (Int.ofNat 50765732932431149222810679136484), (Int.ofNat 25858423048251079338965570717540), (Int.negOfNat 3704184735889856066101165776887), (Int.negOfNat 508573973480885479119723579839), (Int.ofNat 55971215789683829917604790952), (Int.ofNat 6674029115920646733833382057), (Int.negOfNat 396919363713219815193044940), (Int.negOfNat 58572555229830451837253940), (Int.ofNat 1327960617210111086674928), (Int.ofNat 346780832037494962967415), (Int.negOfNat 186445521076669587043), (Int.negOfNat 1452245748061677101109), (Int.negOfNat 19250105651408892241), (Int.ofNat 6377778921645411301), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-45900294407092835585010213365251961/56294995342131200000000000000000000), (4609884081383961531420137443763811/112589990684262400000000000000000000), (-23174318063499179059298785934227/11258999068426240000000000000000000), (12691433233107787305702669784121/28147497671065600000000000000000000), (1292921152412553966948278535877/5629499534213120000000000000000000), (-3704184735889856066101165776887/112589990684262400000000000000000000), (-508573973480885479119723579839/112589990684262400000000000000000000), (6996401973710478739700598869/14073748835532800000000000000000000), (6674029115920646733833382057/112589990684262400000000000000000000), (-19845968185660990759652247/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial134.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial134.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial134.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial134 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 82830401606913396923261158342578001), (Int.ofNat 4756306929445023940068619974515966), (Int.ofNat 322189850955395616551712074028790), (Int.ofNat 68458127476467428517579999935142), (Int.negOfNat 20840137175390609608671506917027), (Int.negOfNat 3315186248775278121958423122606), (Int.ofNat 597955176986453765046781677299), (Int.ofNat 64508974625798541535478006701), (Int.negOfNat 6800665829515417103535271875), (Int.negOfNat 760100236709479373351497405), (Int.ofNat 39134981972967836619238129), (Int.ofNat 5614978831366399172353653), (Int.negOfNat 118091092775980308373446), (Int.negOfNat 28012346291152528764973), (Int.ofNat 99998150023116197064), (Int.ofNat 103064322223463292572), (Int.ofNat 820092450665046385), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-82830401606913396923261158342578001/112589990684262400000000000000000000), (2378153464722511970034309987257983/56294995342131200000000000000000000), (32218985095539561655171207402879/11258999068426240000000000000000000), (34229063738233714258789999967571/56294995342131200000000000000000000), (-20840137175390609608671506917027/112589990684262400000000000000000000), (-1657593124387639060979211561303/56294995342131200000000000000000000), (597955176986453765046781677299/112589990684262400000000000000000000), (64508974625798541535478006701/112589990684262400000000000000000000), (-2176213065444933473131287/36028797018963968000000000000000), (-152020047341895874670299481/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial134.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial134.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial134.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial134 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 71876444475461566218807187977667260), (Int.ofNat 6069716095555921570231565175147025), (Int.ofNat 139326981729262946667435842681153), (Int.negOfNat 114528613178974139864050106114580), (Int.negOfNat 9995332956740208033172179153514), (Int.ofNat 5160786345455255035672790077413), (Int.ofNat 430320800071437523761427964899), (Int.negOfNat 92400572908616305292297783601), (Int.negOfNat 8014292393220220040606701475), (Int.ofNat 767605705927149573482703105), (Int.ofNat 78366072022908704617528329), (Int.negOfNat 3584037460769898965015653), (Int.negOfNat 476718091437384044520246), (Int.ofNat 9914688952243017844573), (Int.ofNat 2001207917168878341064), (Int.negOfNat 8994383908324310372), (Int.negOfNat 7769081322011609315), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-3593822223773078310940359398883363/5629499534213120000000000000000000), (242788643822236862809262607005881/4503599627370496000000000000000000), (139326981729262946667435842681153/112589990684262400000000000000000000), (-5726430658948706993202505305729/5629499534213120000000000000000000), (-4997666478370104016586089576757/56294995342131200000000000000000000), (5160786345455255035672790077413/112589990684262400000000000000000000), (430320800071437523761427964899/112589990684262400000000000000000000), (-92400572908616305292297783601/112589990684262400000000000000000000), (-320571695728808801624268059/4503599627370496000000000000000000), (153521141185429914696540621/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial134.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial134.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial134.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial134 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 60076587746487852906081932018738968), (Int.ofNat 5380830882581784203994292712779277), (Int.negOfNat 343738516228572504214142184873222), (Int.ofNat 19815185891764204136788156620802), (Int.ofNat 36525644594150758409255676076932), (Int.ofNat 1002952212265363683057195890173), (Int.negOfNat 1059286458633182661938952961739), (Int.negOfNat 63954610658120302888936567052), (Int.ofNat 12165301398140979102375306457), (Int.ofNat 936372351920630441946952240), (Int.negOfNat 75842351010959993857030740), (Int.negOfNat 7201043469275094650725928), (Int.ofNat 295897506471088238066615), (Int.ofNat 35985009080963706615443), (Int.negOfNat 753520835085421868109), (Int.negOfNat 135608598475089605959), (Int.ofNat 708872948347869601), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-7509573468310981613260241502342371/14073748835532800000000000000000000), (5380830882581784203994292712779277/112589990684262400000000000000000000), (-171869258114286252107071092436611/56294995342131200000000000000000000), (9907592945882102068394078310401/56294995342131200000000000000000000), (9131411148537689602313919019233/28147497671065600000000000000000000), (1002952212265363683057195890173/112589990684262400000000000000000000), (-1059286458633182661938952961739/112589990684262400000000000000000000), (-15988652664530075722234141763/28147497671065600000000000000000000), (12165301398140979102375306457/112589990684262400000000000000000000), (11704654399007880524336903/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial134.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial134.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial134.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial134 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 49987331478727852691402412942265873), (Int.ofNat 5274835501261037547450381998208810), (Int.ofNat 459861889943189499126964717440605), (Int.ofNat 172246129210082247108256900757213), (Int.negOfNat 18782674804733007943077101373783), (Int.negOfNat 10526713087971916923254798214075), (Int.negOfNat 299683582369774703882078316983), (Int.ofNat 165614304326578244238188860044), (Int.ofNat 9443572218195444177572030265), (Int.negOfNat 1318642694726937914361770682), (Int.negOfNat 96983393575961375887751265), (Int.ofNat 6520655732472005755215899), (Int.ofNat 584206434371067628949384), (Int.negOfNat 22049233615685872054502), (Int.negOfNat 2423526517437042236859), (Int.ofNat 55462910286154435097), (Int.ofNat 8395901022871349336), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-49987331478727852691402412942265873/112589990684262400000000000000000000), (527483550126103754745038199820881/11258999068426240000000000000000000), (91972377988637899825392943488121/22517998136852480000000000000000000), (172246129210082247108256900757213/112589990684262400000000000000000000), (-18782674804733007943077101373783/112589990684262400000000000000000000), (-421068523518876676930191928563/4503599627370496000000000000000000), (-299683582369774703882078316983/112589990684262400000000000000000000), (41403576081644561059547215011/28147497671065600000000000000000000), (1888714443639088835514406053/22517998136852480000000000000000000), (-659321347363468957180885341/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial134.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial134.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial134.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial134 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 36853943989235918439012015673738836), (Int.ofNat 7760931812286487096676953129880384), (Int.ofNat 249734240960078334855545378996487), (Int.negOfNat 345611858664959816701455203282226), (Int.negOfNat 91363132450009171613709743420373), (Int.ofNat 821450847854173884630796075269), (Int.ofNat 1989039696212599373742889665003), (Int.ofNat 79599513938158585165891188418), (Int.negOfNat 19822397208794747297547976546), (Int.negOfNat 1176112862478667895172384472), (Int.ofNat 119968053634527048494178089), (Int.ofNat 8674910356064715499320015), (Int.negOfNat 496636662963479913438769), (Int.negOfNat 41849609740725004132585), (Int.ofNat 1500172413165209977296), (Int.ofNat 152914393204271210809), (Int.negOfNat 2899073797882205101), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-9213485997308979609753003918434709/28147497671065600000000000000000000), (121264559566976360885577392654381/1759218604441600000000000000000000), (249734240960078334855545378996487/112589990684262400000000000000000000), (-172805929332479908350727601641113/56294995342131200000000000000000000), (-91363132450009171613709743420373/112589990684262400000000000000000000), (821450847854173884630796075269/112589990684262400000000000000000000), (1989039696212599373742889665003/112589990684262400000000000000000000), (39799756969079292582945594209/56294995342131200000000000000000000), (-9911198604397373648773988273/56294995342131200000000000000000000), (-147014107809833486896548059/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial134.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial134.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial134.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial134 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 24401613121903871236244795781467335), (Int.ofNat 2149868328828700954244582329559947), (Int.negOfNat 3459430142507822369451808416191113), (Int.negOfNat 720539014016199130737731829281410), (Int.ofNat 33440907365365297537547292195707), (Int.ofNat 21286543161374329268910468866700), (Int.ofNat 587249118227488832636440776580), (Int.negOfNat 262255757663741624934892079712), (Int.negOfNat 13210747770214095907701618552), (Int.ofNat 1914793449262275990727680966), (Int.ofNat 119458539641152512985826881), (Int.negOfNat 9478608039703360314036517), (Int.negOfNat 670557337154078237178148), (Int.ofNat 34269459563621436724814), (Int.ofNat 2664089824496899139768), (Int.negOfNat 92541002697952512962), (Int.negOfNat 8292653773886310857), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-4880322624380774247248959156293467/22517998136852480000000000000000000), (2149868328828700954244582329559947/112589990684262400000000000000000000), (-3459430142507822369451808416191113/112589990684262400000000000000000000), (-72053901401619913073773182928141/11258999068426240000000000000000000), (33440907365365297537547292195707/112589990684262400000000000000000000), (212865431613743292689104688667/1125899906842624000000000000000000), (29362455911374441631822038829/5629499534213120000000000000000000), (-8195492426991925779215377491/3518437208883200000000000000000000), (-1651343471276761988462702319/14073748835532800000000000000000000), (957396724631137995363840483/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial134.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial134.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial134.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial134 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 38485971130451296190486083768170839), (Int.negOfNat 17574652306875015804025058537160660), (Int.negOfNat 5326235072096200817466621602258866), (Int.ofNat 333537663254173282225953223037696), (Int.ofNat 202169214338733572464218173891839), (Int.ofNat 4874595079492212968469477969868), (Int.negOfNat 3046325412634819942703979421026), (Int.negOfNat 145522638794143078919202593193), (Int.ofNat 26757766518188302594931580052), (Int.ofNat 1560812738257662277410291327), (Int.negOfNat 157539962718482464706092418), (Int.negOfNat 10083142952638113250644387), (Int.ofNat 671568332054496956810040), (Int.ofNat 45253017856945314470100), (Int.negOfNat 2176315831589258687205), (Int.negOfNat 155550017437233886673), (Int.ofNat 5089274647416540601), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-38485971130451296190486083768170839/112589990684262400000000000000000000), (-878732615343750790201252926858033/5629499534213120000000000000000000), (-2663117536048100408733310801129433/56294995342131200000000000000000000), (1302881497086614383695129777491/439804651110400000000000000000000), (202169214338733572464218173891839/112589990684262400000000000000000000), (1218648769873053242117369492467/28147497671065600000000000000000000), (-1523162706317409971351989710513/56294995342131200000000000000000000), (-145522638794143078919202593193/112589990684262400000000000000000000), (6689441629547075648732895013/28147497671065600000000000000000000), (1560812738257662277410291327/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial134.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial134.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial134.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial134 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 89087341744437844784095267629830242), (Int.negOfNat 28637752278034552437203777885619728), (Int.ofNat 1141205372094174182203329773485903), (Int.ofNat 1630552578233638681425577828129828), (Int.ofNat 61207004680114149083544327319476), (Int.negOfNat 30259326340922238863337466863133), (Int.negOfNat 1668666463368765431258572813977), (Int.ofNat 323703306240460781117160398379), (Int.ofNat 19846649951499092476289672629), (Int.negOfNat 2286620728218803168879498329), (Int.negOfNat 144351962629010666580283868), (Int.ofNat 11524518084842998464666795), (Int.ofNat 725236605560317761335225), (Int.negOfNat 43714290923508680762493), (Int.negOfNat 2697837479724659040532), (Int.ofNat 127470646216827443967), (Int.ofNat 8189406524901272378), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-44543670872218922392047633814915121/56294995342131200000000000000000000), (-1789859517377159527325236117851233/7036874417766400000000000000000000), (1141205372094174182203329773485903/112589990684262400000000000000000000), (407638144558409670356394457032457/28147497671065600000000000000000000), (15301751170028537270886081829869/28147497671065600000000000000000000), (-30259326340922238863337466863133/112589990684262400000000000000000000), (-1668666463368765431258572813977/112589990684262400000000000000000000), (323703306240460781117160398379/112589990684262400000000000000000000), (19846649951499092476289672629/112589990684262400000000000000000000), (-2286620728218803168879498329/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial134.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial134.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial134.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial134 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 128804162833346839145841956538865068), (Int.negOfNat 5129326140390896172410825424743921), (Int.ofNat 9813522713545117536748376244524921), (Int.ofNat 845731805508597016909708697926867), (Int.negOfNat 239240472005533671399156204634094), (Int.negOfNat 19577255973866247379861354723456), (Int.ofNat 3266352029088997491100641453626), (Int.ofNat 246895147425210062146389511933), (Int.negOfNat 28530248438280506830953658128), (Int.negOfNat 1984061833361844210621157434), (Int.ofNat 172951781285424864903778943), (Int.ofNat 11053058177511494833256398), (Int.negOfNat 772402049769491096520249), (Int.negOfNat 45332380121447982803929), (Int.ofNat 2647501521902594519845), (Int.ofNat 142733329442832267895), (Int.negOfNat 7245059747289196608), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-32201040708336709786460489134716267/28147497671065600000000000000000000), (-5129326140390896172410825424743921/112589990684262400000000000000000000), (9813522713545117536748376244524921/112589990684262400000000000000000000), (845731805508597016909708697926867/112589990684262400000000000000000000), (-119620236002766835699578102317047/56294995342131200000000000000000000), (-152947312295830057655166833777/879609302220800000000000000000000), (1633176014544498745550320726813/56294995342131200000000000000000000), (246895147425210062146389511933/112589990684262400000000000000000000), (-1783140527392531676934603633/7036874417766400000000000000000000), (-992030916680922105310578717/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial134.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial134.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial134.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial134.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial134 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial134 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial134 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 155344447272825212417325237977772411), (Int.negOfNat 181190143068408803590742320442431), (Int.ofNat 10789192830785912961106669447670060), (Int.negOfNat 945453800524633204269489867445463), (Int.negOfNat 250464521782692428353496762492079), (Int.ofNat 23116176124079345883569553823063), (Int.ofNat 3339553194580642109565195178133), (Int.negOfNat 283501137723272554424267639933), (Int.negOfNat 28836069680234122614828899128), (Int.ofNat 2185272293205706604549342434), (Int.ofNat 173857169101243674180953943), (Int.negOfNat 11753200792686753956962398), (Int.negOfNat 774441385625689151086249), (Int.ofNat 47015509138052334702929), (Int.ofNat 2647501521902594519845), (Int.negOfNat 142733329442832267895), (Int.negOfNat 7245059747289196608), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-155344447272825212417325237977772411/112589990684262400000000000000000000), (-181190143068408803590742320442431/112589990684262400000000000000000000), (539459641539295648055333472383503/5629499534213120000000000000000000), (-945453800524633204269489867445463/112589990684262400000000000000000000), (-250464521782692428353496762492079/112589990684262400000000000000000000), (23116176124079345883569553823063/112589990684262400000000000000000000), (3339553194580642109565195178133/112589990684262400000000000000000000), (-283501137723272554424267639933/112589990684262400000000000000000000), (-3604508710029265326853612391/14073748835532800000000000000000000), (1092636146602853302274671217/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial134.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial134.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial134.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 123210070057520395842790879466496303), (Int.ofNat 25954998899768676404291011858204338), (Int.ofNat 1525618983276292633661034115588847), (Int.negOfNat 1686779060419444937057468564503897), (Int.ofNat 79966262463337194692737446837775), (Int.ofNat 31857335675753589766365756671390), (Int.negOfNat 2014049436188619043983584018977), (Int.negOfNat 338924502894676977190990507379), (Int.ofNat 22453300929979080640748639629), (Int.ofNat 2366986387307274414916175329), (Int.negOfNat 155737058585664167457715868), (Int.negOfNat 11798193455404733642194795), (Int.ofNat 758188515575049536510225), (Int.ofNat 44370200418161473368493), (Int.negOfNat 2767934677626484204532), (Int.negOfNat 127470646216827443967), (Int.ofNat 8189406524901272378), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-123210070057520395842790879466496303/112589990684262400000000000000000000), (12977499449884338202145505929102169/56294995342131200000000000000000000), (1525618983276292633661034115588847/112589990684262400000000000000000000), (-1686779060419444937057468564503897/112589990684262400000000000000000000), (3198650498533487787709497873511/4503599627370496000000000000000000), (3185733567575358976636575667139/11258999068426240000000000000000000), (-2014049436188619043983584018977/112589990684262400000000000000000000), (-338924502894676977190990507379/112589990684262400000000000000000000), (22453300929979080640748639629/112589990684262400000000000000000000), (2366986387307274414916175329/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial134.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial134.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial134.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 76558435642852174980858144403731102), (Int.ofNat 16412633791018633663347375887353855), (Int.negOfNat 4789333093229572393943073035400318), (Int.negOfNat 234634277121109924805879751393701), (Int.ofNat 215006900852176947100020064978760), (Int.negOfNat 7466384322754155246853787976082), (Int.negOfNat 3299117368702008816017813036026), (Int.ofNat 172081245049189906847051226193), (Int.ofNat 28674550934798567501973768052), (Int.negOfNat 1707480196493736856591614327), (Int.negOfNat 165900392984188256079517418), (Int.ofNat 10595680575690669096167387), (Int.ofNat 695700331162918295089040), (Int.negOfNat 46508428688706959256100), (Int.negOfNat 2226385258661990947205), (Int.ofNat 155550017437233886673), (Int.ofNat 5089274647416540601), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-38279217821426087490429072201865551/56294995342131200000000000000000000), (3282526758203726732669475177470771/22517998136852480000000000000000000), (-2394666546614786196971536517700159/56294995342131200000000000000000000), (-234634277121109924805879751393701/112589990684262400000000000000000000), (5375172521304423677500501624469/2814749767106560000000000000000000), (-3733192161377077623426893988041/56294995342131200000000000000000000), (-1649558684351004408008906518013/56294995342131200000000000000000000), (172081245049189906847051226193/112589990684262400000000000000000000), (7168637733699641875493442013/28147497671065600000000000000000000), (-1707480196493736856591614327/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial134.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial134.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial134.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 61749184937028990015903827012449469), (Int.ofNat 190975088513430843304775870887064), (Int.negOfNat 2268490624850229639598852662871666), (Int.ofNat 795440378077605778932677229481788), (Int.ofNat 14096874054060299955023924435451), (Int.negOfNat 24168144981184169402363967812450), (Int.ofNat 803005698517781032778355298087), (Int.ofNat 293500423364646158858185855712), (Int.negOfNat 14629845883375531872059776552), (Int.negOfNat 2090034629567056124791796966), (Int.ofNat 125348964976604773745725881), (Int.ofNat 10094067807629031730855517), (Int.negOfNat 687224413636747513613148), (Int.negOfNat 35767041222803865501814), (Int.ofNat 2699138423447811721768), (Int.ofNat 92541002697952512962), (Int.negOfNat 8292653773886310857), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-61749184937028990015903827012449469/112589990684262400000000000000000000), (23871886064178855413096983860883/14073748835532800000000000000000000), (-1134245312425114819799426331435833/56294995342131200000000000000000000), (198860094519401444733169307370447/28147497671065600000000000000000000), (14096874054060299955023924435451/112589990684262400000000000000000000), (-483362899623683388047279356249/2251799813685248000000000000000000), (803005698517781032778355298087/112589990684262400000000000000000000), (9171888230145192464318307991/3518437208883200000000000000000000), (-1828730735421941484007472069/14073748835532800000000000000000000), (-1045017314783528062395898483/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial134.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial134.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial134.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 64541213839715247249187007980660769), (Int.negOfNat 553448599248210524518890331749602), (Int.ofNat 1264808294776186987469440689060803), (Int.ofNat 199144015383285319282399895537724), (Int.negOfNat 120022700534548015622391157442016), (Int.ofNat 585092837957458648694264832595), (Int.ofNat 2393128772117711796802593441996), (Int.negOfNat 87958756412975584222785216418), (Int.negOfNat 22708320752995126170309615546), (Int.ofNat 1210560332666135639301554472), (Int.ofNat 132342395734636163423937089), (Int.negOfNat 8778291263632139937288015), (Int.negOfNat 532164974984030676557769), (Int.ofNat 42100998186599786612585), (Int.ofNat 1575276553774308367296), (Int.negOfNat 152914393204271210809), (Int.negOfNat 2899073797882205101), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-64541213839715247249187007980660769/112589990684262400000000000000000000), (-276724299624105262259445165874801/56294995342131200000000000000000000), (1264808294776186987469440689060803/112589990684262400000000000000000000), (49786003845821329820599973884431/28147497671065600000000000000000000), (-3750709391704625488199723670063/3518437208883200000000000000000000), (117018567591491729738852966519/22517998136852480000000000000000000), (598282193029427949200648360499/28147497671065600000000000000000000), (-43979378206487792111392608209/56294995342131200000000000000000000), (-11354160376497563085154807773/56294995342131200000000000000000000), (151320041583266954912694309/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial134.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial134.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial134.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 60760542249935455441640551686188123), (Int.ofNat 3501772806227213635582872655370630), (Int.ofNat 107311173883002020655585266970386), (Int.negOfNat 436560258152607926933572295682343), (Int.negOfNat 14407793331261114619830312105777), (Int.ofNat 14949977566656407602654099014325), (Int.negOfNat 274645803514208937475917026983), (Int.negOfNat 204698817093580760739590962044), (Int.ofNat 9010072377695672522755820265), (Int.ofNat 1522341475557592285320334682), (Int.negOfNat 94655133146008393843787265), (Int.negOfNat 7214747406390352743328899), (Int.ofNat 576906504318926247090384), (Int.ofNat 23710206806736648146502), (Int.negOfNat 2408505689315222558859), (Int.negOfNat 55462910286154435097), (Int.ofNat 8395901022871349336), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-60760542249935455441640551686188123/112589990684262400000000000000000000), (350177280622721363558287265537063/11258999068426240000000000000000000), (53655586941501010327792633485193/56294995342131200000000000000000000), (-436560258152607926933572295682343/112589990684262400000000000000000000), (-14407793331261114619830312105777/112589990684262400000000000000000000), (597999102666256304106163960573/4503599627370496000000000000000000), (-274645803514208937475917026983/112589990684262400000000000000000000), (-51174704273395190184897740511/28147497671065600000000000000000000), (1802014475539134504551164053/22517998136852480000000000000000000), (761170737778796142660167341/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial134.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial134.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial134.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 56613161367139862343117708219609404), (Int.negOfNat 705010799050966664490104592453735), (Int.negOfNat 1843402555460246993123161157895816), (Int.negOfNat 89756601072767815869786673795678), (Int.ofNat 76029230207012909683099989992304), (Int.ofNat 652180491616602541196853378370), (Int.negOfNat 1495599799931398517832628170739), (Int.ofNat 45836220096420194980143340052), (Int.ofNat 14912366273296289219616293457), (Int.negOfNat 832608775055925906764763240), (Int.negOfNat 86944573041395512735961740), (Int.ofNat 6831383950196076494743928), (Int.ofNat 326888373323541917369615), (Int.negOfNat 35078246661239518506443), (Int.negOfNat 818611090279973806109), (Int.ofNat 130601655767816379959), (Int.ofNat 708872948347869601), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-14153290341784965585779427054902351/28147497671065600000000000000000000), (-141002159810193332898020918490747/22517998136852480000000000000000000), (-230425319432530874140395144736977/14073748835532800000000000000000000), (-44878300536383907934893336897839/56294995342131200000000000000000000), (4751826887938306855193749374519/7036874417766400000000000000000000), (65218049161660254119685337837/11258999068426240000000000000000000), (-1495599799931398517832628170739/112589990684262400000000000000000000), (11459055024105048745035835013/28147497671065600000000000000000000), (14912366273296289219616293457/112589990684262400000000000000000000), (-20815219376398147669119081/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial134.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial134.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial134.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 64964042615822325887995927611343704), (Int.negOfNat 6924221134855002184620945380836993), (Int.negOfNat 811114847623966734065689518668089), (Int.ofNat 352162893354733604892850089228119), (Int.ofNat 18142079796286191304375991364044), (Int.negOfNat 8920572682326459171765101585506), (Int.ofNat 76961932145612230569429651899), (Int.ofNat 121422476621982446105216046601), (Int.negOfNat 5616166062637859005352173475), (Int.negOfNat 906705580238824330798634105), (Int.ofNat 68274352741835007777191329), (Int.ofNat 4036615986288902450851653), (Int.negOfNat 447909232831100672322246), (Int.negOfNat 10964309343298726161573), (Int.ofNat 1941124604681599629064), (Int.ofNat 14001326615597536372), (Int.negOfNat 7769081322011609315), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-8120505326977790735999490951417963/14073748835532800000000000000000000), (-6924221134855002184620945380836993/112589990684262400000000000000000000), (-811114847623966734065689518668089/112589990684262400000000000000000000), (352162893354733604892850089228119/112589990684262400000000000000000000), (4535519949071547826093997841011/28147497671065600000000000000000000), (-4460286341163229585882550792753/56294995342131200000000000000000000), (76961932145612230569429651899/112589990684262400000000000000000000), (121422476621982446105216046601/112589990684262400000000000000000000), (-224646642505514360214086939/4503599627370496000000000000000000), (-181341116047764866159726821/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial134.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial134.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial134.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 79216184221959383628190617280171257), (Int.negOfNat 6014107444214000747336212642079691), (Int.ofNat 1110320007580489699719603616882532), (Int.ofNat 207015491240819238354564411198597), (Int.negOfNat 41364245128635701909961125145535), (Int.negOfNat 1518612755250653810573408166937), (Int.ofNat 800231173679964642529228519799), (Int.negOfNat 23854699152982851736075597701), (Int.negOfNat 7950522221119679506859721875), (Int.ofNat 554231684141091849930520405), (Int.ofNat 43451522263457036497446129), (Int.negOfNat 4922871620250897097236653), (Int.negOfNat 129556583487036456776446), (Int.ofNat 26376407813638118802973), (Int.ofNat 125032863559482327064), (Int.negOfNat 103064322223463292572), (Int.ofNat 820092450665046385), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-79216184221959383628190617280171257/112589990684262400000000000000000000), (-6014107444214000747336212642079691/112589990684262400000000000000000000), (277580001895122424929900904220633/28147497671065600000000000000000000), (207015491240819238354564411198597/112589990684262400000000000000000000), (-8272849025727140381992225029107/22517998136852480000000000000000000), (-1518612755250653810573408166937/112589990684262400000000000000000000), (800231173679964642529228519799/112589990684262400000000000000000000), (-23854699152982851736075597701/112589990684262400000000000000000000), (-2544167110758297442195111/36028797018963968000000000000000), (110846336828218369986104081/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial134.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial134.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial134.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 85810974757287143932465874221072736), (Int.negOfNat 397528057175321068167496708669669), (Int.ofNat 1402871092653520614530001498336831), (Int.negOfNat 80779892822630088523061590539410), (Int.negOfNat 21516596684840343653838217261382), (Int.ofNat 3836088553179649106696427615080), (Int.ofNat 19454008958871359638544329161), (Int.negOfNat 56018793163919390150809773952), (Int.ofNat 3356958542497864703083773057), (Int.ofNat 392911970101370891531516940), (Int.negOfNat 45213014725456794424934940), (Int.negOfNat 1303523490380233136905928), (Int.ofNat 309607878579586399389415), (Int.ofNat 110835590759836994043), (Int.negOfNat 1377141607452578711109), (Int.ofNat 19250105651408892241), (Int.ofNat 6377778921645411301), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-2681592961165223247889558569408523/3518437208883200000000000000000000), (-397528057175321068167496708669669/112589990684262400000000000000000000), (1402871092653520614530001498336831/112589990684262400000000000000000000), (-8077989282263008852306159053941/11258999068426240000000000000000000), (-10758298342420171826919108630691/56294995342131200000000000000000000), (95902213829491227667410690377/2814749767106560000000000000000000), (19454008958871359638544329161/112589990684262400000000000000000000), (-437646821593120235553201359/879609302220800000000000000000000), (3356958542497864703083773057/112589990684262400000000000000000000), (19645598505068544576575847/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial134.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial134.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial134.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 81867208873930984275746764604693823), (Int.ofNat 3845696424662523242522054092614690), (Int.ofNat 682993931316599605009598197084649), (Int.negOfNat 120314643945488064798152773632322), (Int.ofNat 7045500334266132499798310696345), (Int.ofNat 1286948522510604273157386102675), (Int.negOfNat 278626101289758255982171911883), (Int.ofNat 11291966085636337697915834144), (Int.ofNat 2790401830050448223929674665), (Int.negOfNat 328618537654028256066451982), (Int.negOfNat 10250653238695595024163065), (Int.ofNat 3063385574222947641388899), (Int.negOfNat 21467261069811178841416), (Int.negOfNat 16739223668580618967902), (Int.ofNat 404818016460012053141), (Int.ofNat 61208590579112765297), (Int.negOfNat 1653406649494863364), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-81867208873930984275746764604693823/112589990684262400000000000000000000), (384569642466252324252205409261469/11258999068426240000000000000000000), (682993931316599605009598197084649/112589990684262400000000000000000000), (-60157321972744032399076386816161/56294995342131200000000000000000000), (1409100066853226499959662139269/22517998136852480000000000000000000), (51477940900424170926295444107/4503599627370496000000000000000000), (-278626101289758255982171911883/112589990684262400000000000000000000), (352873940176135553059869817/3518437208883200000000000000000000), (558080366010089644785934933/22517998136852480000000000000000000), (-164309268827014128033225991/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial134.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial134.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial134.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 72268292140959364057917221808660874), (Int.ofNat 5415951802417026571366396215052718), (Int.ofNat 177322270639696804995567357914795), (Int.negOfNat 47530598767997864158129117424800), (Int.ofNat 8142776264673514979605059167327), (Int.negOfNat 519629567427592093427706090038), (Int.negOfNat 22497963615254350970909677404), (Int.ofNat 12832389164780571211988825318), (Int.negOfNat 1665934661008096711907481146), (Int.negOfNat 47265217054899797852798172), (Int.ofNat 24175146683019011160864289), (Int.negOfNat 541628962927634535886985), (Int.negOfNat 169134174952497694348569), (Int.ofNat 7028223316899419643815), (Int.ofNat 752431585675492323296), (Int.negOfNat 45004418054031672391), (Int.negOfNat 4187578072111075801), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-36134146070479682028958610904330437/56294995342131200000000000000000000), (2707975901208513285683198107526359/56294995342131200000000000000000000), (35464454127939360999113471582959/22517998136852480000000000000000000), (-59413248459997330197661396781/140737488355328000000000000000000), (8142776264673514979605059167327/112589990684262400000000000000000000), (-259814783713796046713853045019/56294995342131200000000000000000000), (-5624490903813587742727419351/28147497671065600000000000000000000), (6416194582390285605994412659/56294995342131200000000000000000000), (-832967330504048355953740573/56294995342131200000000000000000000), (-11816304263724949463199543/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial134.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial134.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial134.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 60993912950802792088880463090146977), (Int.ofNat 5773600628773673696985655416804938), (Int.ofNat 46268823600961048351325698773357), (Int.negOfNat 2494624152304923315837688902924), (Int.ofNat 3417072257755166402430401485379), (Int.negOfNat 388575846211422073067938716650), (Int.ofNat 4031823968635464573691641480), (Int.negOfNat 3541337118461981093245666812), (Int.ofNat 175490430264546493208578048), (Int.ofNat 132667164988214578813271266), (Int.negOfNat 8934637955244374158721319), (Int.negOfNat 1296198473239127814383517), (Int.ofNat 105136881209233479595652), (Int.ofNat 7026919155975120516214), (Int.negOfNat 661347590731670552232), (Int.negOfNat 22359720207053879162), (Int.ofNat 1756653898479901843), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-60993912950802792088880463090146977/112589990684262400000000000000000000), (2886800314386836848492827708402469/56294995342131200000000000000000000), (46268823600961048351325698773357/112589990684262400000000000000000000), (-623656038076230828959422225731/28147497671065600000000000000000000), (3417072257755166402430401485379/112589990684262400000000000000000000), (-7771516924228441461358774333/2251799813685248000000000000000000), (100795599215886614342291037/2814749767106560000000000000000000), (-885334279615495273311416703/28147497671065600000000000000000000), (85688686652610592387001/54975581388800000000000000000000), (66333582494107289406635633/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial134.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial134.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial134.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 49239448393393076830609350010933674), (Int.ofNat 6006616167219979965586571148837864), (Int.ofNat 81606948058734281615954919084058), (Int.ofNat 8809941012140526587612523750520), (Int.negOfNat 646560250106628175134688992754), (Int.negOfNat 389728168881111912204345734475), (Int.ofNat 21282998341790253764751564874), (Int.ofNat 6067617646499731484378478907), (Int.ofNat 226798526910914798513622652), (Int.negOfNat 112346997857146873825461973), (Int.negOfNat 5236630029055020017693618), (Int.ofNat 1332182985515258725385613), (Int.ofNat 37232070223511044056840), (Int.negOfNat 9597208088314924141300), (Int.negOfNat 146112841033126791205), (Int.ofNat 46212337544535789527), (Int.ofNat 1997377222576740301), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-24619724196696538415304675005466837/56294995342131200000000000000000000), (750827020902497495698321393604733/14073748835532800000000000000000000), (40803474029367140807977459542029/56294995342131200000000000000000000), (220248525303513164690313093763/2814749767106560000000000000000000), (-323280125053314087567344496377/56294995342131200000000000000000000), (-15589126755244476488173829379/4503599627370496000000000000000000), (10641499170895126882375782437/56294995342131200000000000000000000), (6067617646499731484378478907/112589990684262400000000000000000000), (56699631727728699628405663/28147497671065600000000000000000000), (-112346997857146873825461973/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial134.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial134.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial134.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 36849988259127368382155124170283226), (Int.ofNat 6393661686540672215692777960666517), (Int.ofNat 96823141224457400864512130164175), (Int.negOfNat 5368873937398709252849180665066), (Int.negOfNat 1779815970029650543253750317603), (Int.ofNat 248234038443341513970817804110), (Int.ofNat 58336913888625749074357736123), (Int.negOfNat 4572098175129758494522398521), (Int.negOfNat 1069878121371357562609938971), (Int.ofNat 36970166341796631410475371), (Int.ofNat 13887333408522435525449332), (Int.negOfNat 250645679744300980370205), (Int.negOfNat 116484327367926302693575), (Int.ofNat 1703005831666878014107), (Int.ofNat 651612188839369515468), (Int.negOfNat 15717331258549039833), (Int.negOfNat 1859901147464940322), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-18424994129563684191077562085141613/56294995342131200000000000000000000), (6393661686540672215692777960666517/112589990684262400000000000000000000), (3872925648978296034580485206567/4503599627370496000000000000000000), (-2684436968699354626424590332533/56294995342131200000000000000000000), (-1779815970029650543253750317603/112589990684262400000000000000000000), (24823403844334151397081780411/11258999068426240000000000000000000), (58336913888625749074357736123/112589990684262400000000000000000000), (-4572098175129758494522398521/112589990684262400000000000000000000), (-1069878121371357562609938971/112589990684262400000000000000000000), (36970166341796631410475371/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial134.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial134.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial134.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 23735950250701690178147402604305968), (Int.ofNat 6687639967041767128233967884501730), (Int.ofNat 51080138004171108066347900395044), (Int.negOfNat 4432420226822885282468907902735), (Int.ofNat 2035898252995518298998898506192), (Int.ofNat 253394769136150371574124772894), (Int.negOfNat 63755269998785870497829715767), (Int.negOfNat 6865898986229273932123985167), (Int.ofNat 1021951109874524647507983272), (Int.ofNat 109447994476970157726889866), (Int.negOfNat 10092625863011798110047857), (Int.negOfNat 1124864080875801315707602), (Int.ofNat 71000574303059992842951), (Int.ofNat 7629788417987483300471), (Int.negOfNat 356511839490946551155), (Int.negOfNat 38676833975886287305), (Int.ofNat 227239376619274692), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1483496890668855636134212662769123/7036874417766400000000000000000000), (668763996704176712823396788450173/11258999068426240000000000000000000), (12770034501042777016586975098761/28147497671065600000000000000000000), (-886484045364577056493781580547/22517998136852480000000000000000000), (127243640812219893687431156637/7036874417766400000000000000000000), (126697384568075185787062386447/56294995342131200000000000000000000), (-63755269998785870497829715767/112589990684262400000000000000000000), (-6865898986229273932123985167/112589990684262400000000000000000000), (127743888734315580938497909/14073748835532800000000000000000000), (54723997238485078863444933/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial134.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial134.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial134.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 10155779929660942554420877168404446), (Int.ofNat 6910111269313500778242378690026682), (Int.ofNat 75897187771538755240769848964317), (Int.ofNat 10171896953963311950207219171561), (Int.ofNat 236119438435074566242799452893), (Int.negOfNat 515334545973724190538014868663), (Int.negOfNat 16900529256622580417721400233), (Int.ofNat 12043009189483543265163366833), (Int.ofNat 472116492040345681004395728), (Int.negOfNat 160170204686090991263595134), (Int.negOfNat 7043038115711579727889143), (Int.ofNat 1373845132542035110575398), (Int.ofNat 63791112233759535461049), (Int.negOfNat 8228401289474479139529), (Int.negOfNat 380402751719431387845), (Int.ofNat 39802101454526960695), (Int.ofNat 468598747098742308), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-5077889964830471277210438584202223/56294995342131200000000000000000000), (3455055634656750389121189345013341/56294995342131200000000000000000000), (75897187771538755240769848964317/112589990684262400000000000000000000), (10171896953963311950207219171561/112589990684262400000000000000000000), (236119438435074566242799452893/112589990684262400000000000000000000), (-515334545973724190538014868663/112589990684262400000000000000000000), (-16900529256622580417721400233/112589990684262400000000000000000000), (12043009189483543265163366833/112589990684262400000000000000000000), (29507280752521605062774733/7036874417766400000000000000000000), (-80085102343045495631797567/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial134.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial134.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial134.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 4037188257692419112919206632563137), (Int.ofNat 7304337134095475341589357723255757), (Int.ofNat 105473856819687323833496736045881), (Int.negOfNat 4573154449377938278908047783647), (Int.negOfNat 2708084428562806777709801889396), (Int.ofNat 169393740554308974947529415560), (Int.ofNat 95366926532713627932001588877), (Int.negOfNat 2362138391707675311567943521), (Int.negOfNat 1738347469505315920446168029), (Int.ofNat 8128697031733568659136371), (Int.ofNat 19066653737160484200839668), (Int.ofNat 134021955651073640799795), (Int.negOfNat 138182059430189677380425), (Int.negOfNat 1901117474999772108893), (Int.ofNat 704002786319083095532), (Int.ofNat 19047270213780175167), (Int.negOfNat 1756204775632190678), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(4037188257692419112919206632563137/112589990684262400000000000000000000), (7304337134095475341589357723255757/112589990684262400000000000000000000), (105473856819687323833496736045881/112589990684262400000000000000000000), (-4573154449377938278908047783647/112589990684262400000000000000000000), (-677021107140701694427450472349/28147497671065600000000000000000000), (4234843513857724373688235389/2814749767106560000000000000000000), (95366926532713627932001588877/112589990684262400000000000000000000), (-2362138391707675311567943521/112589990684262400000000000000000000), (-1738347469505315920446168029/112589990684262400000000000000000000), (8128697031733568659136371/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial134.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial134.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial134.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 18998643469690795080430656977467787), (Int.ofNat 7613834093211548488494036437029169), (Int.ofNat 45029491283566707585496292765487), (Int.negOfNat 8314653826955332609100523544718), (Int.ofNat 2376737246405476750752223326283), (Int.ofNat 496797991673594354071920792332), (Int.negOfNat 68930995917070209938028995874), (Int.negOfNat 13391807700848498348790812093), (Int.ofNat 980326405253816067360723348), (Int.ofNat 198981631906522361901399027), (Int.negOfNat 7759458576117244750767382), (Int.negOfNat 1834897725107736396051387), (Int.ofNat 35800240579231384718160), (Int.ofNat 11371759775014965242700), (Int.negOfNat 95386288179346849795), (Int.negOfNat 52618789448928579473), (Int.ofNat 1687186352773913699), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(18998643469690795080430656977467787/112589990684262400000000000000000000), (7613834093211548488494036437029169/112589990684262400000000000000000000), (45029491283566707585496292765487/112589990684262400000000000000000000), (-4157326913477666304550261772359/56294995342131200000000000000000000), (2376737246405476750752223326283/112589990684262400000000000000000000), (124199497918398588517980198083/28147497671065600000000000000000000), (-34465497958535104969014497937/56294995342131200000000000000000000), (-13391807700848498348790812093/112589990684262400000000000000000000), (245081601313454016840180837/28147497671065600000000000000000000), (198981631906522361901399027/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial134.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial134.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial134.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 34388053362418492430052234982963011), (Int.ofNat 7792144736255091851706707688816677), (Int.ofNat 68921119304264628378102959529589), (Int.ofNat 14679772998608367541500759430798), (Int.ofNat 1186085321057528667249881942927), (Int.negOfNat 724647654982445687745229295600), (Int.negOfNat 61682993035322067085170150487), (Int.ofNat 15846185519275347878697820188), (Int.ofNat 1438366998254945630697945952), (Int.negOfNat 187623532934245037138359734), (Int.negOfNat 18512022550902079437211681), (Int.ofNat 1344440239427092931089483), (Int.ofNat 148059007189834746627348), (Int.negOfNat 6294953833217759125786), (Int.negOfNat 796211207662329759768), (Int.ofNat 15882373305094755838), (Int.ofNat 1859452024617229157), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(34388053362418492430052234982963011/112589990684262400000000000000000000), (7792144736255091851706707688816677/112589990684262400000000000000000000), (68921119304264628378102959529589/112589990684262400000000000000000000), (7339886499304183770750379715399/56294995342131200000000000000000000), (1186085321057528667249881942927/112589990684262400000000000000000000), (-1811619137456114219363073239/281474976710656000000000000000000), (-61682993035322067085170150487/112589990684262400000000000000000000), (3961546379818836969674455047/28147497671065600000000000000000000), (44948968695467050959310811/3518437208883200000000000000000000), (-93811766467122518569179867/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial134.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial134.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial134.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 50359591235044268166240968192523014), (Int.ofNat 8220189548143788149082672879048536), (Int.ofNat 124885024244550127949109847699989), (Int.negOfNat 4457239018150439399641377704298), (Int.negOfNat 4646257265408348812121618956384), (Int.ofNat 35055512701633537343289306648), (Int.ofNat 159690326825224647649579874904), (Int.ofNat 3930850751800288504950658318), (Int.negOfNat 2710078975001461483394984854), (Int.negOfNat 114026865622452288045267172), (Int.ofNat 26308943488475448173022711), (Int.ofNat 1415930244258316880523015), (Int.negOfNat 161157428183707926554431), (Int.negOfNat 10229242263105783317185), (Int.ofNat 665984114563521116704), (Int.ofNat 49983165215965903609), (Int.negOfNat 3877387202308249199), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(25179795617522134083120484096261507/56294995342131200000000000000000000), (1027523693517973518635334109881067/14073748835532800000000000000000000), (124885024244550127949109847699989/112589990684262400000000000000000000), (-2228619509075219699820688852149/56294995342131200000000000000000000), (-145195539544010900378800592387/3518437208883200000000000000000000), (4381939087704192167911163331/14073748835532800000000000000000000), (19961290853153080956197484363/14073748835532800000000000000000000), (1965425375900144252475329159/56294995342131200000000000000000000), (-1355039487500730741697492427/56294995342131200000000000000000000), (-28506716405613072011316793/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial134.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial134.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial134.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 67200634452901702496498405837743273), (Int.ofNat 8549896943897258000259242651778600), (Int.ofNat 25351883267860727366152725282420), (Int.negOfNat 17499471274963331147067600874342), (Int.ofNat 3281352560955376861041529101056), (Int.ofNat 1072668069027914821375961181732), (Int.negOfNat 67257291106889793288881146117), (Int.negOfNat 27964593654326898247791202856), (Int.ofNat 305288744147017603640580335), (Int.ofNat 377827148024696464726249018), (Int.ofNat 5578983089451531734717065), (Int.negOfNat 3009376456694292782468101), (Int.negOfNat 88903157202832055809584), (Int.ofNat 15557881384463800788098), (Int.ofNat 616935138134768491859), (Int.negOfNat 52960465716892833703), (Int.negOfNat 1962699273602267636), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(67200634452901702496498405837743273/112589990684262400000000000000000000), (42749484719486290001296213258893/562949953421312000000000000000000), (1267594163393036368307636264121/5629499534213120000000000000000000), (-8749735637481665573533800437171/56294995342131200000000000000000000), (12817783441231940863443473051/439804651110400000000000000000000), (268167017256978705343990295433/28147497671065600000000000000000000), (-67257291106889793288881146117/112589990684262400000000000000000000), (-3495574206790862280973900357/14073748835532800000000000000000000), (61057748829403520728116067/22517998136852480000000000000000000), (188913574012348232363124509/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial134.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial134.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial134.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 84341054110578966722368784202600922), (Int.ofNat 8607862506312715695726309177272189), (Int.ofNat 52251289036162917310906155356270), (Int.ofNat 27768470251945620498012223053516), (Int.ofNat 3950581370013648524916859107460), (Int.negOfNat 1232420089846496920255653828113), (Int.negOfNat 197945661247484197915804837161), (Int.ofNat 20413003873307327223553216048), (Int.ofNat 4139309068332159748461562943), (Int.negOfNat 132775064591672875436166060), (Int.negOfNat 45031705415772247906662060), (Int.ofNat 35203119249715774828072), (Int.ofNat 292809614834613745361585), (Int.ofNat 4436038200415483888043), (Int.negOfNat 1275825168087877608891), (Int.negOfNat 32677370486784298759), (Int.ofNat 6067588051842584699), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(42170527055289483361184392101300461/56294995342131200000000000000000000), (8607862506312715695726309177272189/112589990684262400000000000000000000), (5225128903616291731090615535627/11258999068426240000000000000000000), (6942117562986405124503055763379/28147497671065600000000000000000000), (197529068500682426245842955373/5629499534213120000000000000000000), (-1232420089846496920255653828113/112589990684262400000000000000000000), (-197945661247484197915804837161/112589990684262400000000000000000000), (1275812742081707951472076003/7036874417766400000000000000000000), (4139309068332159748461562943/112589990684262400000000000000000000), (-6638753229583643771808303/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial134.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial134.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial134.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 102002595098552768050730319026264001), (Int.ofNat 9152763614432339040387225649243034), (Int.ofNat 187601080510330866404727328497210), (Int.negOfNat 4116771489810192460921806709142), (Int.negOfNat 11000415120431877807416405895973), (Int.negOfNat 638655606975866303737469489394), (Int.ofNat 328691328397775367788993200701), (Int.ofNat 31798467734139136365461130299), (Int.negOfNat 4065209754735726388562150125), (Int.negOfNat 545091555199717118382878595), (Int.ofNat 21960798945077475663006871), (Int.ofNat 4656709558837399817754347), (Int.negOfNat 42270092906876041553554), (Int.negOfNat 24729443773463599666027), (Int.negOfNat 153090579146582092064), (Int.ofNat 94422049387449732428), (Int.ofNat 1335879572742527615), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(102002595098552768050730319026264001/112589990684262400000000000000000000), (4576381807216169520193612824621517/56294995342131200000000000000000000), (18760108051033086640472732849721/11258999068426240000000000000000000), (-2058385744905096230460903354571/56294995342131200000000000000000000), (-11000415120431877807416405895973/112589990684262400000000000000000000), (-319327803487933151868734744697/56294995342131200000000000000000000), (328691328397775367788993200701/112589990684262400000000000000000000), (31798467734139136365461130299/112589990684262400000000000000000000), (-32521678037885811108497201/900719925474099200000000000000000), (-109018311039943423676575719/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial134.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial134.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial134.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 120852967174048298078213895869731260), (Int.ofNat 9522759270762760614570084563352975), (Int.negOfNat 61366772494648148716494202022153), (Int.negOfNat 56961759096805782386357323321420), (Int.ofNat 4964780305882556352446162026514), (Int.ofNat 3359070327983216852219800178587), (Int.ofNat 87087318894086617789012840101), (Int.negOfNat 69769176296866693490170569399), (Int.negOfNat 5082976692665284202385484525), (Int.ofNat 581254234931509921170868895), (Int.ofNat 63085318515064858272688671), (Int.negOfNat 2531357363869118596158347), (Int.negOfNat 419275889229418630000754), (Int.ofNat 5616316898381979968427), (Int.ofNat 1831139534676198253936), (Int.ofNat 5140036942431211372), (Int.negOfNat 7596553450855500685), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(6042648358702414903910694793486563/5629499534213120000000000000000000), (380910370830510424582803382534119/4503599627370496000000000000000000), (-61366772494648148716494202022153/112589990684262400000000000000000000), (-2848087954840289119317866166071/5629499534213120000000000000000000), (2482390152941278176223081013257/56294995342131200000000000000000000), (3359070327983216852219800178587/112589990684262400000000000000000000), (87087318894086617789012840101/112589990684262400000000000000000000), (-69769176296866693490170569399/112589990684262400000000000000000000), (-203319067706611368095419381/4503599627370496000000000000000000), (116250846986301984234173779/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial134.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial134.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial134.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 139379948555735600433132291987434968), (Int.ofNat 9003232769938190468031592179178723), (Int.negOfNat 47042483419013860254165497222778), (Int.ofNat 86816485099798206682244132312198), (Int.ofNat 21587745617957346391969894721068), (Int.negOfNat 2166806228225642211388188474173), (Int.negOfNat 916023575384227692205096421261), (Int.negOfNat 29435635015227400000066751948), (Int.ofNat 10638371024113385835108072543), (Int.ofNat 721671276440708272784576760), (Int.negOfNat 63952990055506063243617260), (Int.negOfNat 6284698241453135362747072), (Int.ofNat 233355855283849606776385), (Int.ofNat 33050925345591120627557), (Int.negOfNat 517469929543211477891), (Int.negOfNat 127673481654456161041), (Int.ofNat 55422827623670399), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(17422493569466950054141536498429371/14073748835532800000000000000000000), (9003232769938190468031592179178723/112589990684262400000000000000000000), (-23521241709506930127082748611389/56294995342131200000000000000000000), (43408242549899103341122066156099/56294995342131200000000000000000000), (5396936404489336597992473680267/28147497671065600000000000000000000), (-2166806228225642211388188474173/112589990684262400000000000000000000), (-916023575384227692205096421261/112589990684262400000000000000000000), (-7358908753806850000016687987/28147497671065600000000000000000000), (10638371024113385835108072543/112589990684262400000000000000000000), (18041781911017706819614419/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial134.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial134.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial134.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 158109464676944587666516727879695873), (Int.ofNat 10197425925226146522042037425906190), (Int.ofNat 600487876759379426945403729139395), (Int.ofNat 31529704773531530364885771053787), (Int.negOfNat 49543150385692310926057556179217), (Int.negOfNat 10078702490186179436255209474925), (Int.ofNat 60897476726884641955869636983), (Int.ofNat 159242339435691155922956912956), (Int.ofNat 6834802069882208565078567735), (Int.negOfNat 1221091897124589832507040318), (Int.negOfNat 84017198811722898411864735), (Int.ofNat 5772646093818848906317101), (Int.ofNat 537819369165462650396616), (Int.negOfNat 18424666719115012497498), (Int.negOfNat 2299473117858575600141), (Int.ofNat 41722637409192541903), (Int.ofNat 8429867649685317664), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(158109464676944587666516727879695873/112589990684262400000000000000000000), (1019742592522614652204203742590619/11258999068426240000000000000000000), (120097575351875885389080745827879/22517998136852480000000000000000000), (31529704773531530364885771053787/112589990684262400000000000000000000), (-49543150385692310926057556179217/112589990684262400000000000000000000), (-403148099607447177450208378997/4503599627370496000000000000000000), (60897476726884641955869636983/112589990684262400000000000000000000), (39810584858922788980739228239/28147497671065600000000000000000000), (1366960413976441713015713547/22517998136852480000000000000000000), (-610545948562294916253520159/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial134.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial134.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial134.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 180068629559874655958052114293549836), (Int.ofNat 10672922044588478474850399525439616), (Int.negOfNat 1078191006600505222727793648932487), (Int.negOfNat 664354006086421783865588391230774), (Int.negOfNat 100183074240389425154667350208627), (Int.ofNat 4168146376468418844663587490731), (Int.ofNat 2064409944494294611330591449997), (Int.ofNat 53289095865962708925526325582), (Int.negOfNat 19533317135969475579639681454), (Int.negOfNat 1020091179513664466149735528), (Int.ofNat 113283483272292410395550911), (Int.ofNat 8025651192705929050260985), (Int.negOfNat 450021732210739184601231), (Int.negOfNat 39933381394326006245415), (Int.ofNat 1298177684134943786704), (Int.ofNat 148420851349805715191), (Int.negOfNat 2245623677158005899), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(45017157389968663989513028573387459/28147497671065600000000000000000000), (83382203473347488084768746292497/879609302220800000000000000000000), (-1078191006600505222727793648932487/112589990684262400000000000000000000), (-332177003043210891932794195615387/56294995342131200000000000000000000), (-100183074240389425154667350208627/112589990684262400000000000000000000), (4168146376468418844663587490731/112589990684262400000000000000000000), (2064409944494294611330591449997/112589990684262400000000000000000000), (26644547932981354462763162791/56294995342131200000000000000000000), (-9766658567984737789819840727/56294995342131200000000000000000000), (-127511397439208058268716941/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial134.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial134.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial134.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 190450879789063828475626508073277335), (Int.negOfNat 4085951494962044894193287024874947), (Int.negOfNat 6642197906963571986235599120594887), (Int.negOfNat 977415107274061376634450220571590), (Int.ofNat 56085197712097924677522532742293), (Int.ofNat 23703695465942094671631863795300), (Int.ofNat 402454884925471057048049623420), (Int.negOfNat 270019265919239775183907912288), (Int.negOfNat 11765702979883383492582801448), (Int.ofNat 1884851797712014725643189034), (Int.ofNat 111855086460914070428182119), (Int.negOfNat 9005223578613149121524483), (Int.negOfNat 645028300779641669436852), (Int.ofNat 31473208628305853268186), (Int.ofNat 2611478857097376282232), (Int.negOfNat 80571507781251428038), (Int.negOfNat 8533114898670356143), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(38090175957812765695125301614655467/22517998136852480000000000000000000), (-4085951494962044894193287024874947/112589990684262400000000000000000000), (-6642197906963571986235599120594887/112589990684262400000000000000000000), (-97741510727406137663445022057159/11258999068426240000000000000000000), (56085197712097924677522532742293/112589990684262400000000000000000000), (237036954659420946716318637953/1125899906842624000000000000000000), (20122744246273552852402481171/5629499534213120000000000000000000), (-8438102059976242974497122259/3518437208883200000000000000000000), (-1470712872485422936572850181/14073748835532800000000000000000000), (942425898856007362821594517/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial134.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial134.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial134.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 149535987154384085364465680832950839), (Int.negOfNat 38743647758850588068530376279007340), (Int.negOfNat 9360613381446729283143478946705134), (Int.ofNat 322921139718926206015962264383304), (Int.ofNat 237141307647521504620252525886161), (Int.ofNat 4963426104787263518655781586132), (Int.negOfNat 3215752710277227423801188641974), (Int.negOfNat 138943396625310525911593290807), (Int.ofNat 27005374139847667626624268948), (Int.ofNat 1495759821248630017857494673), (Int.negOfNat 154263542868582938991774582), (Int.negOfNat 9806479356298543255656613), (Int.ofNat 640080907382589650341960), (Int.ofNat 44692867514181648109900), (Int.negOfNat 2020860036089610439795), (Int.negOfNat 154635713547583058327), (Int.ofNat 4435824526692341399), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(149535987154384085364465680832950839/112589990684262400000000000000000000), (-1937182387942529403426518813950367/5629499534213120000000000000000000), (-4680306690723364641571739473352567/56294995342131200000000000000000000), (40365142464865775751995283047913/14073748835532800000000000000000000), (237141307647521504620252525886161/112589990684262400000000000000000000), (1240856526196815879663945396533/28147497671065600000000000000000000), (-1607876355138613711900594320987/56294995342131200000000000000000000), (-138943396625310525911593290807/112589990684262400000000000000000000), (6751343534961916906656067237/28147497671065600000000000000000000), (1495759821248630017857494673/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial134.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial134.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial134.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 40926608963591538717428454908639242), (Int.negOfNat 64974905548341780364791742864356272), (Int.negOfNat 2146489332636003910141863396866903), (Int.ofNat 1879994456137380867142682493944172), (Int.ofNat 88810670569692341231572488031524), (Int.negOfNat 31639802331223205278729610345867), (Int.negOfNat 1748736629537317474130533443023), (Int.ofNat 328689580515116981211259939621), (Int.ofNat 19634395497496085584068254371), (Int.negOfNat 2277773292221418302963291671), (Int.negOfNat 142324250403944999039440132), (Int.ofNat 11259289717629347215039205), (Int.ofNat 722586339913786952241775), (Int.negOfNat 41842362929634058370507), (Int.negOfNat 2723533151638687184468), (Int.ofNat 118648559246854347033), (Int.ofNat 8636362147655394622), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(20463304481795769358714227454319621/56294995342131200000000000000000000), (-4060931596771361272799483929022267/7036874417766400000000000000000000), (-2146489332636003910141863396866903/112589990684262400000000000000000000), (469998614034345216785670623486043/28147497671065600000000000000000000), (22202667642423085307893122007881/28147497671065600000000000000000000), (-31639802331223205278729610345867/112589990684262400000000000000000000), (-1748736629537317474130533443023/112589990684262400000000000000000000), (328689580515116981211259939621/112589990684262400000000000000000000), (19634395497496085584068254371/112589990684262400000000000000000000), (-2277773292221418302963291671/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial134.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial134.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial134.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 82226813556806182543301951884866932), (Int.negOfNat 50864405626340469981470370664240079), (Int.ofNat 8558339518327335266659159786803079), (Int.ofNat 1250452420807205361418650215973133), (Int.negOfNat 229035320064183601299650429757906), (Int.negOfNat 21568172598851082537441351486544), (Int.ofNat 3241370383470190109942769199374), (Int.ofNat 250420748849061033547190695067), (Int.negOfNat 28523030158375525802067368872), (Int.negOfNat 1980104802909238477604863566), (Int.ofNat 171683552150934590044104057), (Int.ofNat 11098092496993403602504602), (Int.negOfNat 756143454952082245965751), (Int.negOfNat 46100441941234114013071), (Int.ofNat 2552055955795486442155), (Int.ofNat 147100209978933556105), (Int.negOfNat 6660441125888356392), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-20556703389201545635825487971216733/28147497671065600000000000000000000), (-50864405626340469981470370664240079/112589990684262400000000000000000000), (8558339518327335266659159786803079/112589990684262400000000000000000000), (1250452420807205361418650215973133/112589990684262400000000000000000000), (-114517660032091800649825214878953/56294995342131200000000000000000000), (-1348010787428192658590084467909/7036874417766400000000000000000000), (1620685191735095054971384599687/56294995342131200000000000000000000), (250420748849061033547190695067/112589990684262400000000000000000000), (-3565378769796940725258421109/14073748835532800000000000000000000), (-990052401454619238802431783/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial134.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial134.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial134.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial134.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial134.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial134.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial134.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial134.reflect := by
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

end Bin134
end
end ErdosOverlap.OuterNumerics
