/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.IntegerOuterBindings
public import ErdosOverlap.Numerics.OuterTruncation
public import ErdosOverlap.Certificate.OuterData12
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

/-! # Exact integer weighted outer models for source bin 145

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin145

def weightDenominator : ℤ := (Int.ofNat 25000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 6319222272652261250)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 6237144087449235250)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 5520634187725954250)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 3779892009210175750)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 2442013726234781250)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 1385891631817452375)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 819661953398071600)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 1259084671781481375)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 429853457387742500)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial145.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial145.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 24507019749392357500)⟩, ⟨(314159265359/50000000000), (Int.ofNat 5711411425091134000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 3743343975003260000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 2355329260849546250)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 744383849413445075)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 123701714363885175)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 284640428167311225)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 278822094393216650)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 3067322477627393)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial145.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial145.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 24507019749392357500)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 5711411425091134000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 3743343975003260000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 2355329260849546250)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 744383849413445075)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 123701714363885175)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 284640428167311225)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 278822094393216650)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 3067322477627393)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial145.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial145.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial145.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 22062522509347446872204875736819989), (Int.ofNat 12388396893037584505895794373254831), (Int.ofNat 2377315215285167658433720435570140), (Int.negOfNat 407434985512095794105487672125262), (Int.negOfNat 69694214293938576436773247488371), (Int.ofNat 8268070805294176387418201955737), (Int.ofNat 1096399602560604873760868698092), (Int.negOfNat 102419460049592331713235475492), (Int.negOfNat 10750875834949389920286620797), (Int.ofNat 836618202702346531976943316), (Int.ofNat 71524554609143009243860932), (Int.negOfNat 4817199720247384784861477), (Int.negOfNat 343250150192844334858551), (Int.ofNat 20578104789666500082796), (Int.ofNat 1243141109160524620380), (Int.negOfNat 67269395150697597605), (Int.negOfNat 3668770118247646167), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-22062522509347446872204875736819989/28147497671065600000000000000000000), (12388396893037584505895794373254831/28147497671065600000000000000000000), (118865760764258382921686021778507/1407374883553280000000000000000000), (-203717492756047897052743836062631/14073748835532800000000000000000000), (-69694214293938576436773247488371/28147497671065600000000000000000000), (8268070805294176387418201955737/28147497671065600000000000000000000), (274099900640151218440217174523/7036874417766400000000000000000000), (-25604865012398082928308868873/7036874417766400000000000000000000), (-10750875834949389920286620797/28147497671065600000000000000000000), (209154550675586632994235829/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial145.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial145.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial145.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial145 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 8168321254929864690136090638592878), (Int.ofNat 15595516941404505124949104337650512), (Int.negOfNat 898941782622023865140657559344297), (Int.negOfNat 530101449741021393405416849559978), (Int.ofNat 42148196777810607223570234250600), (Int.ofNat 10099223796207619984807761232335), (Int.negOfNat 825277739945430400225446286273), (Int.negOfNat 116752670719188221804965439946), (Int.ofNat 9127150645415529183167875421), (Int.ofNat 892729346892352544545041721), (Int.negOfNat 65869310322475528275135857), (Int.negOfNat 4819967169119028887169330), (Int.ofNat 337077254372287156671025), (Int.ofNat 19329756966522527406657), (Int.negOfNat 1292980195640282612993), (Int.negOfNat 59293608933660690033), (Int.ofNat 4001506069012971797), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(4084160627464932345068045319296439/14073748835532800000000000000000000), (974719808837781570309319021103157/1759218604441600000000000000000000), (-898941782622023865140657559344297/28147497671065600000000000000000000), (-265050724870510696702708424779989/14073748835532800000000000000000000), (210740983889053036117851171253/140737488355328000000000000000000), (2019844759241523996961552246467/5629499534213120000000000000000000), (-825277739945430400225446286273/28147497671065600000000000000000000), (-58376335359594110902482719973/14073748835532800000000000000000000), (9127150645415529183167875421/28147497671065600000000000000000000), (892729346892352544545041721/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial145.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial145.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial145.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial145 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 32455278424747821141542531391056052), (Int.ofNat 7595474752497721594351576576260845), (Int.negOfNat 2516979956482104446971250747523607), (Int.ofNat 33609535991359610353779063214226), (Int.ofNat 73714368430775857208023875801115), (Int.negOfNat 4357244067401521683083995795268), (Int.negOfNat 1107171574091575599580595511149), (Int.ofNat 79175612896760340598649210907), (Int.ofNat 10159782441515199019514262998), (Int.negOfNat 766256807669299409267417273), (Int.negOfNat 62902252841806882921989207), (Int.ofNat 4845996284448367158094888), (Int.ofNat 280725017921459055023160), (Int.negOfNat 21954057530380616437850), (Int.negOfNat 946919329905601672970), (Int.ofNat 75134059640974015677), (Int.ofNat 2376142423606791274), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(8113819606186955285385632847764013/7036874417766400000000000000000000), (1519094950499544318870315315252169/5629499534213120000000000000000000), (-2516979956482104446971250747523607/28147497671065600000000000000000000), (16804767995679805176889531607113/14073748835532800000000000000000000), (14742873686155171441604775160223/5629499534213120000000000000000000), (-1089311016850380420770998948817/7036874417766400000000000000000000), (-1107171574091575599580595511149/28147497671065600000000000000000000), (79175612896760340598649210907/28147497671065600000000000000000000), (5079891220757599509757131499/14073748835532800000000000000000000), (-766256807669299409267417273/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial145.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial145.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial145.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial145 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 38828613024792645598462489129316319), (Int.negOfNat 227580316451678450804551051093539), (Int.negOfNat 1093170160325991756339771231431559), (Int.ofNat 329575696324775591464992449918262), (Int.negOfNat 6443707419802007529434632047101), (Int.negOfNat 8329197426303833684612374510075), (Int.ofNat 495807881944062194836838821313), (Int.ofNat 101013478724648998293644422638), (Int.negOfNat 7353947870809803937466099048), (Int.negOfNat 749555215796010192202906684), (Int.ofNat 60384465057378724108901569), (Int.ofNat 3794606896056860141695358), (Int.negOfNat 331547617014818149881277), (Int.negOfNat 14010408571685447132211), (Int.ofNat 1325154156022165909357), (Int.ofNat 38039566655276465363), (Int.negOfNat 3992304101580089618), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(38828613024792645598462489129316319/28147497671065600000000000000000000), (-227580316451678450804551051093539/28147497671065600000000000000000000), (-1093170160325991756339771231431559/28147497671065600000000000000000000), (164787848162387795732496224959131/14073748835532800000000000000000000), (-6443707419802007529434632047101/28147497671065600000000000000000000), (-333167897052153347384494980403/1125899906842624000000000000000000), (495807881944062194836838821313/28147497671065600000000000000000000), (50506739362324499146822211319/14073748835532800000000000000000000), (-919243483851225492183262381/3518437208883200000000000000000000), (-187388803949002548050726671/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial145.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial145.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial145.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial145 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 36310206886633116587694262558017219), (Int.negOfNat 1386352122987065182079014461046098), (Int.ofNat 234320329796146516085036743933147), (Int.ofNat 64594449869749450491972392268326), (Int.negOfNat 42035915487756989967259774703159), (Int.ofNat 1862312958272502290558587434680), (Int.ofNat 820046971107522889814364668229), (Int.negOfNat 55899626227599001818273169257), (Int.negOfNat 7897321684232454696217622979), (Int.ofNat 640510841989502825973133653), (Int.ofNat 47128139610324259163590136), (Int.negOfNat 4405849092983813090569735), (Int.negOfNat 193016402872492865630856), (Int.ofNat 20941832546505399025790), (Int.ofNat 574801326068149190454), (Int.negOfNat 74918272573860579766), (Int.negOfNat 1086582051443563774), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(36310206886633116587694262558017219/28147497671065600000000000000000000), (-693176061493532591039507230523049/14073748835532800000000000000000000), (234320329796146516085036743933147/28147497671065600000000000000000000), (32297224934874725245986196134163/14073748835532800000000000000000000), (-42035915487756989967259774703159/28147497671065600000000000000000000), (46557823956812557263964685867/703687441776640000000000000000000), (820046971107522889814364668229/28147497671065600000000000000000000), (-55899626227599001818273169257/28147497671065600000000000000000000), (-7897321684232454696217622979/28147497671065600000000000000000000), (640510841989502825973133653/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial145.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial145.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial145.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial145 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 34422231630781507550930292727247923), (Int.negOfNat 744118711436658728197416952498855), (Int.negOfNat 89534411355069151087946530963311), (Int.negOfNat 107482781246733008606236826341382), (Int.ofNat 4306559875857578333086033720877), (Int.ofNat 4998035108660413352672736308250), (Int.negOfNat 329977194191581206880081121817), (Int.negOfNat 70507578216808893443253009106), (Int.ofNat 5680953313890025005366745385), (Int.ofNat 526210257580296565912666443), (Int.negOfNat 50884984889317734802699860), (Int.negOfNat 2462973003046315641092601), (Int.ofNat 294131228672768434255366), (Int.ofNat 7777452228404220236098), (Int.negOfNat 1213392319346686239766), (Int.negOfNat 16806825865067375153), (Int.ofNat 3983102134147207439), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(34422231630781507550930292727247923/28147497671065600000000000000000000), (-148823742287331745639483390499771/5629499534213120000000000000000000), (-89534411355069151087946530963311/28147497671065600000000000000000000), (-53741390623366504303118413170691/14073748835532800000000000000000000), (4306559875857578333086033720877/28147497671065600000000000000000000), (19992140434641653410690945233/112589990684262400000000000000000), (-329977194191581206880081121817/28147497671065600000000000000000000), (-35253789108404446721626504553/14073748835532800000000000000000000), (1136190662778005001073349077/5629499534213120000000000000000000), (526210257580296565912666443/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial145.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial145.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial145.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial145 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 31916360725177821431222763126487704), (Int.negOfNat 1942591111363294271734982724438990), (Int.negOfNat 345836317496963545183077840661384), (Int.ofNat 46768543198912195926664559805678), (Int.ofNat 22481432214516922659130907564396), (Int.negOfNat 1730463353217925995572377886070), (Int.negOfNat 516431933320045592404443485661), (Int.ofNat 42077961847547737685274221748), (Int.ofNat 5157505131203925413436053293), (Int.negOfNat 504341865762651647139290660), (Int.negOfNat 28775474445511358933948660), (Int.ofNat 3633134497216836651685547), (Int.ofNat 97706878105242803640210), (Int.negOfNat 17819569229655979071032), (Int.negOfNat 187722729675290266091), (Int.ofNat 65291889050549477041), (Int.negOfNat 202978320719663726), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(3989545090647227678902845390810963/3518437208883200000000000000000000), (-194259111136329427173498272443899/2814749767106560000000000000000000), (-43229539687120443147884730082673/3518437208883200000000000000000000), (23384271599456097963332279902839/14073748835532800000000000000000000), (5620358053629230664782726891099/7036874417766400000000000000000000), (-173046335321792599557237788607/2814749767106560000000000000000000), (-516431933320045592404443485661/28147497671065600000000000000000000), (10519490461886934421318555437/7036874417766400000000000000000000), (5157505131203925413436053293/28147497671065600000000000000000000), (-25217093288132582356964533/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial145.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial145.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial145.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial145 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 27299684327615984402236371164268004), (Int.negOfNat 2260034783667910246899706680508157), (Int.ofNat 246917770960798611052933659967264), (Int.ofNat 104584158948138217877421724486431), (Int.negOfNat 10511827786328000570122636564244), (Int.negOfNat 3219876850739950117466079246994), (Int.ofNat 270287411841519452003204007526), (Int.ofNat 44069697123195845086657318324), (Int.negOfNat 4250153890065768177968230125), (Int.negOfNat 305045231417444543945052595), (Int.ofNat 38912915653035631457496496), (Int.ofNat 1144547620555371963457222), (Int.negOfNat 231201367759658551115579), (Int.negOfNat 1804837760777816961577), (Int.ofNat 968776761129422098036), (Int.negOfNat 4810663269876307772), (Int.negOfNat 3544046709326582760), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(6824921081903996100559092791067001/7036874417766400000000000000000000), (-2260034783667910246899706680508157/28147497671065600000000000000000000), (7716180342524956595404176873977/879609302220800000000000000000000), (104584158948138217877421724486431/28147497671065600000000000000000000), (-2627956946582000142530659141061/7036874417766400000000000000000000), (-1609938425369975058733039623497/14073748835532800000000000000000000), (135143705920759726001602003763/14073748835532800000000000000000000), (11017424280798961271664329581/7036874417766400000000000000000000), (-34001231120526145423745841/225179981368524800000000000000000), (-61009046283488908789010519/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial145.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial145.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial145.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial145 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 24354470149584647784241956217864257), (Int.negOfNat 544532547107415974394880919269709), (Int.ofNat 450475546804590641300871917556443), (Int.negOfNat 49016540302663538480258662883322), (Int.negOfNat 19601612225374225157135328206340), (Int.ofNat 1530946251578099369480861771312), (Int.ofNat 340567690266557716040037658726), (Int.negOfNat 30114268985798953687213576174), (Int.negOfNat 2957308406225796870527075575), (Int.ofNat 354276316399165490138300695), (Int.ofNat 12683865673439354481801596), (Int.negOfNat 2601629310616495252957422), (Int.negOfNat 14060033578096910723179), (Int.ofNat 12995165184395558738477), (Int.negOfNat 141626939351970665914), (Int.negOfNat 48060917264400673728), (Int.ofNat 1056550590539893940), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(24354470149584647784241956217864257/28147497671065600000000000000000000), (-544532547107415974394880919269709/28147497671065600000000000000000000), (450475546804590641300871917556443/28147497671065600000000000000000000), (-24508270151331769240129331441661/14073748835532800000000000000000000), (-980080611268711257856766410317/1407374883553280000000000000000000), (95684140723631210592553860707/1759218604441600000000000000000000), (170283845133278858020018829363/14073748835532800000000000000000000), (-15057134492899476843606788087/14073748835532800000000000000000000), (-118292336249031874821083023/1125899906842624000000000000000000), (70855263279833098027660139/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial145.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial145.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial145.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial145 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 24427913134116328637244164005043761), (Int.ofNat 214116994223934544820952060787494), (Int.negOfNat 133680331440638461393216981759531), (Int.negOfNat 110272688977676641948458402098690), (Int.ofNat 5889460463665770089606415238882), (Int.ofNat 2505443118322133435027252576295), (Int.negOfNat 168216880282594471973402742811), (Int.negOfNat 27036229435836344206521692998), (Int.ofNat 2631140722992463891332770543), (Int.ofNat 137493066615414683498763060), (Int.negOfNat 24553820636769391453113460), (Int.negOfNat 106735866335032659486347), (Int.ofNat 148858448716276050505060), (Int.negOfNat 2849990718539651021418), (Int.negOfNat 633271404515564961991), (Int.ofNat 20401171803126970809), (Int.ofNat 2678205149595842974), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(24427913134116328637244164005043761/28147497671065600000000000000000000), (107058497111967272410476030393747/14073748835532800000000000000000000), (-133680331440638461393216981759531/28147497671065600000000000000000000), (-11027268897767664194845840209869/2814749767106560000000000000000000), (2944730231832885044803207619441/14073748835532800000000000000000000), (501088623664426687005450515259/5629499534213120000000000000000000), (-168216880282594471973402742811/28147497671065600000000000000000000), (-13518114717918172103260846499/14073748835532800000000000000000000), (2631140722992463891332770543/28147497671065600000000000000000000), (6874653330770734174938153/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial145.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial145.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial145.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial145 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 23600142498046522973435321375141173), (Int.negOfNat 1296500692509040575108035736864490), (Int.negOfNat 507002265338073204633282662308249), (Int.ofNat 93748702240963578615316329997), (Int.ofNat 16464713281483736183979182384505), (Int.negOfNat 515843078860099504581376063850), (Int.negOfNat 235963767842138411397903761267), (Int.ofNat 13950468429539648120596467306), (Int.ofNat 1507389607167595812364952085), (Int.negOfNat 179435144759875225555235643), (Int.negOfNat 1538754813785340422918910), (Int.ofNat 1376151973592281495331401), (Int.negOfNat 43677041478269435910384), (Int.negOfNat 7018751058569904255298), (Int.ofNat 364306818646283235534), (Int.ofNat 24901119195842927103), (Int.negOfNat 1477202080494754261), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(23600142498046522973435321375141173/28147497671065600000000000000000000), (-129650069250904057510803573686449/2814749767106560000000000000000000), (-507002265338073204633282662308249/28147497671065600000000000000000000), (93748702240963578615316329997/28147497671065600000000000000000000), (3292942656296747236795836476901/5629499534213120000000000000000000), (-10316861577201990091627521277/562949953421312000000000000000000), (-235963767842138411397903761267/28147497671065600000000000000000000), (6975234214769824060298233653/14073748835532800000000000000000000), (301477921433519162472990417/5629499534213120000000000000000000), (-179435144759875225555235643/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial145.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial145.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial145.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial145 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 19213789487990154014273992203303774), (Int.negOfNat 2875700253482943948020681254999818), (Int.negOfNat 197919178351825726054205350572895), (Int.ofNat 83000218310085561497260363434700), (Int.ofNat 2049155253229865202625130575198), (Int.negOfNat 1840023865519480305312866163612), (Int.ofNat 18969948437475511404452127629), (Int.ofNat 16332025098884683997933171007), (Int.negOfNat 733095357188038256178191629), (Int.negOfNat 35872761169423454299704103), (Int.ofNat 8469902238920003475488086), (Int.negOfNat 506524619172185676036165), (Int.negOfNat 55476849110024422138106), (Int.ofNat 5472557110573095233860), (Int.ofNat 240673297249621961954), (Int.negOfNat 28901161125277262634), (Int.negOfNat 1388644777432615474), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(9606894743995077007136996101651887/14073748835532800000000000000000000), (-1437850126741471974010340627499909/14073748835532800000000000000000000), (-39583835670365145210841070114579/5629499534213120000000000000000000), (830002183100855614972603634347/281474976710656000000000000000000), (1024577626614932601312565287599/14073748835532800000000000000000000), (-460005966379870076328216540903/7036874417766400000000000000000000), (18969948437475511404452127629/28147497671065600000000000000000000), (16332025098884683997933171007/28147497671065600000000000000000000), (-733095357188038256178191629/28147497671065600000000000000000000), (-35872761169423454299704103/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial145.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial145.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial145.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial145 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 13311725727528512831074615420184527), (Int.negOfNat 2742841042496820286656946986146463), (Int.ofNat 216189347438854198434828209700418), (Int.ofNat 36571253506916006828080939103074), (Int.negOfNat 11518047598875361253475001985454), (Int.negOfNat 591581575003580363315620450350), (Int.ofNat 160405604013478254309536276070), (Int.ofNat 4144947196635039552610330062), (Int.negOfNat 715288174110515827130560948), (Int.negOfNat 7149539997064686112582516), (Int.negOfNat 3826537436039354435357631), (Int.negOfNat 79966614284035069577808), (Int.ofNat 68270508743821059646623), (Int.ofNat 637350846540480930961), (Int.negOfNat 443395258096719842243), (Int.negOfNat 1429100417726797313), (Int.ofNat 1468000113061872082), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(13311725727528512831074615420184527/28147497671065600000000000000000000), (-2742841042496820286656946986146463/28147497671065600000000000000000000), (108094673719427099217414104850209/14073748835532800000000000000000000), (18285626753458003414040469551537/14073748835532800000000000000000000), (-5759023799437680626737500992727/14073748835532800000000000000000000), (-11831631500071607266312409007/562949953421312000000000000000000), (16040560401347825430953627607/2814749767106560000000000000000000), (2072473598317519776305165031/14073748835532800000000000000000000), (-178822043527628956782640237/7036874417766400000000000000000000), (-1787384999266171528145629/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial145.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial145.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial145.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial145 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 8790757621354599547918305041273174), (Int.negOfNat 1823245606849128363334482347398264), (Int.ofNat 151783425519736197775623197819617), (Int.negOfNat 52625160880860619527830365513545), (Int.negOfNat 7525263508900308253247206265021), (Int.ofNat 1320060208478201167792452426225), (Int.ofNat 123322307885101211539924229901), (Int.negOfNat 10813586622970507087734437407), (Int.negOfNat 1152952289505563584261656952), (Int.negOfNat 489981928853809057140977), (Int.ofNat 7441811278966651055265693), (Int.ofNat 650666739043617635110162), (Int.negOfNat 37202393826264820790290), (Int.negOfNat 5771364916276564523400), (Int.ofNat 151184768181852805280), (Int.ofNat 29617608608115521273), (Int.ofNat 99084405269387974), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(4395378810677299773959152520636587/14073748835532800000000000000000000), (-227905700856141045416810293424783/3518437208883200000000000000000000), (151783425519736197775623197819617/28147497671065600000000000000000000), (-10525032176172123905566073102709/5629499534213120000000000000000000), (-7525263508900308253247206265021/28147497671065600000000000000000000), (52802408339128046711698097049/1125899906842624000000000000000000), (123322307885101211539924229901/28147497671065600000000000000000000), (-10813586622970507087734437407/28147497671065600000000000000000000), (-144119036188195448032707119/3518437208883200000000000000000000), (-489981928853809057140977/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial145.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial145.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial145.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial145 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 5258458371875857972223581333086326), (Int.negOfNat 1965121573031892438063895628706442), (Int.negOfNat 218606075862408041924856114929875), (Int.negOfNat 48281551415180507502302402468484), (Int.ofNat 8874496138807175999648926323478), (Int.ofNat 1447890209796473183229798579215), (Int.negOfNat 126187548722878660885457599023), (Int.negOfNat 20219077577180093405600490104), (Int.ofNat 554397205379317970609345521), (Int.ofNat 177638960550701320477757929), (Int.ofNat 3447840342446515144831043), (Int.negOfNat 1111568425181066645682970), (Int.negOfNat 58571390274598957129875), (Int.ofNat 5274358669074839474943), (Int.ofNat 378366951840259488607), (Int.negOfNat 20302203042663228017), (Int.negOfNat 1458798145628989903), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(2629229185937928986111790666543163/14073748835532800000000000000000000), (-982560786515946219031947814353221/14073748835532800000000000000000000), (-1748848606899264335398848919439/225179981368524800000000000000000), (-12070387853795126875575600617121/7036874417766400000000000000000000), (4437248069403587999824463161739/14073748835532800000000000000000000), (289578041959294636645959715843/5629499534213120000000000000000000), (-126187548722878660885457599023/28147497671065600000000000000000000), (-2527384697147511675700061263/3518437208883200000000000000000000), (554397205379317970609345521/28147497671065600000000000000000000), (177638960550701320477757929/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial145.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial145.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial145.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial145 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.ofNat 245432830652346114310178679326693), (Int.negOfNat 3051414561749797939586688594361255), (Int.negOfNat 221531028414373717075650162391519), (Int.ofNat 51066995575481650090099344777935), (Int.ofNat 11452188359247701893568668487833), (Int.negOfNat 1167219053049941963186297803094), (Int.negOfNat 234711638752576525186969598958), (Int.ofNat 10893916280218853732615423192), (Int.ofNat 2711233599948381012012406853), (Int.negOfNat 24455050295127733590550266), (Int.negOfNat 20811891002115779082284718), (Int.negOfNat 350388065917964391852523), (Int.ofNat 115794191407270036301549), (Int.ofNat 3830019009388735677354), (Int.negOfNat 485758018398880626220), (Int.negOfNat 21220369352833933895), (Int.ofNat 1187408644416212133), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(245432830652346114310178679326693/28147497671065600000000000000000000), (-610282912349959587917337718872251/5629499534213120000000000000000000), (-221531028414373717075650162391519/28147497671065600000000000000000000), (10213399115096330018019868955587/5629499534213120000000000000000000), (11452188359247701893568668487833/28147497671065600000000000000000000), (-583609526524970981593148901547/14073748835532800000000000000000000), (-117355819376288262593484799479/14073748835532800000000000000000000), (1361739535027356716576927899/3518437208883200000000000000000000), (2711233599948381012012406853/28147497671065600000000000000000000), (-12227525147563866795275133/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial145.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial145.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial145.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial145 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 6202067538528341053498857318260354), (Int.negOfNat 3089213940936284036173509315722657), (Int.ofNat 221840322470471794472873252532058), (Int.ofNat 68948829847918110158276288543264), (Int.negOfNat 8593407850160946246838036941693), (Int.negOfNat 2069074126859006109977653447962), (Int.ofNat 137194277212044998059573382258), (Int.ofNat 32039885452056933818086834942), (Int.negOfNat 967650465480750610308682703), (Int.negOfNat 305352689115227505920724216), (Int.ofNat 1970239764228073488112618), (Int.ofNat 2016893698488096249241127), (Int.ofNat 18563499505349955245751), (Int.negOfNat 9827159436983325015246), (Int.negOfNat 184811327976423577330), (Int.ofNat 37540316581069269605), (Int.ofNat 592956585898250117), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-3101033769264170526749428659130177/14073748835532800000000000000000000), (-3089213940936284036173509315722657/28147497671065600000000000000000000), (110920161235235897236436626266029/14073748835532800000000000000000000), (2154650932747440942446134016977/879609302220800000000000000000000), (-8593407850160946246838036941693/28147497671065600000000000000000000), (-1034537063429503054988826723981/14073748835532800000000000000000000), (68597138606022499029786691129/14073748835532800000000000000000000), (16019942726028466909043417471/14073748835532800000000000000000000), (-967650465480750610308682703/28147497671065600000000000000000000), (-38169086139403438240090527/3518437208883200000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial145.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial145.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial145.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial145 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 11132764767538663099817344474470562), (Int.negOfNat 1775948183957413461703318723699057), (Int.ofNat 315161059405015252293242026743119), (Int.negOfNat 45928980385955851637274529826978), (Int.negOfNat 14285928697373964629695770761979), (Int.ofNat 1293605729373773249480483625990), (Int.ofNat 307512548424334706026566587123), (Int.negOfNat 15499073177336581761262372804), (Int.negOfNat 3708472134641953238863838671), (Int.ofNat 98535882325874719342889979), (Int.ofNat 29494282800277258077353757), (Int.negOfNat 308385854881097085390420), (Int.negOfNat 167952924343571563374025), (Int.negOfNat 57771949913768621557), (Int.ofNat 716912198854894990493), (Int.ofNat 6801944602478066833), (Int.negOfNat 2040980914236442347), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-5566382383769331549908672237235281/14073748835532800000000000000000000), (-1775948183957413461703318723699057/28147497671065600000000000000000000), (315161059405015252293242026743119/28147497671065600000000000000000000), (-22964490192977925818637264913489/14073748835532800000000000000000000), (-14285928697373964629695770761979/28147497671065600000000000000000000), (129360572937377324948048362599/2814749767106560000000000000000000), (307512548424334706026566587123/28147497671065600000000000000000000), (-3874768294334145440315593201/7036874417766400000000000000000000), (-3708472134641953238863838671/28147497671065600000000000000000000), (98535882325874719342889979/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial145.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial145.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial145.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial145 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 13961801319571945732459058228979437), (Int.negOfNat 1371441106556268470043552508385769), (Int.negOfNat 142270550696863944407550770640037), (Int.negOfNat 73643903163647423970357382322107), (Int.ofNat 9367753235209270251706093000892), (Int.ofNat 2431494477626593014531932649268), (Int.negOfNat 173465601732152828000476647051), (Int.negOfNat 37912714393723446078570036157), (Int.ofNat 1768692768028103935561780202), (Int.ofNat 368422500515105211130332523), (Int.negOfNat 10993629361383842251056643), (Int.negOfNat 2483366667947858146942088), (Int.ofNat 43536676408588358061890), (Int.ofNat 12279265376065117515500), (Int.negOfNat 109263862011574656430), (Int.negOfNat 46224643024743759277), (Int.ofNat 699671108742604776), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-13961801319571945732459058228979437/28147497671065600000000000000000000), (-1371441106556268470043552508385769/28147497671065600000000000000000000), (-142270550696863944407550770640037/28147497671065600000000000000000000), (-73643903163647423970357382322107/28147497671065600000000000000000000), (2341938308802317562926523250223/7036874417766400000000000000000000), (607873619406648253632983162317/7036874417766400000000000000000000), (-173465601732152828000476647051/28147497671065600000000000000000000), (-37912714393723446078570036157/28147497671065600000000000000000000), (884346384014051967780890101/14073748835532800000000000000000000), (368422500515105211130332523/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial145.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial145.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial145.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial145 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 17650554361784197118386121493508611), (Int.negOfNat 2377675350142663419855452550134102), (Int.negOfNat 227221987625088239974935306426289), (Int.ofNat 54456998055883920891478549817577), (Int.ofNat 15882741157061743575819658920973), (Int.negOfNat 1453516528122435708701874834025), (Int.negOfNat 327148046921960077824179889413), (Int.ofNat 22105007504977774696306430062), (Int.ofNat 3937227175524649973925338598), (Int.negOfNat 201378975011901917759714516), (Int.negOfNat 31809900519378189601194719), (Int.ofNat 1191069812317673125321042), (Int.ofNat 184416611449944740662277), (Int.negOfNat 4870566068998935485789), (Int.negOfNat 795850628401682935807), (Int.ofNat 13632435722508086237), (Int.ofNat 2031778946803560168), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-17650554361784197118386121493508611/28147497671065600000000000000000000), (-1188837675071331709927726275067051/14073748835532800000000000000000000), (-227221987625088239974935306426289/28147497671065600000000000000000000), (54456998055883920891478549817577/28147497671065600000000000000000000), (15882741157061743575819658920973/28147497671065600000000000000000000), (-58140661124897428348074993361/1125899906842624000000000000000000), (-327148046921960077824179889413/28147497671065600000000000000000000), (11052503752488887348153215031/14073748835532800000000000000000000), (1968613587762324986962669299/14073748835532800000000000000000000), (-50344743752975479439928629/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial145.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial145.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial145.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial145 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 22688758339390747408434250861040989), (Int.negOfNat 2290599831435997854165567864934661), (Int.ofNat 306569553310740855324227523786911), (Int.ofNat 88966782112763883178437818681648), (Int.negOfNat 8850556227277443931072820200116), (Int.negOfNat 2369531745655435922438009084123), (Int.ofNat 207972680756819597412942989971), (Int.ofNat 35680300361658680634963758107), (Int.negOfNat 2714526096149689292669016521), (Int.negOfNat 349646564009388407249827553), (Int.ofNat 21751612887741630381717014), (Int.ofNat 2408292950349363842021885), (Int.negOfNat 116754029538895136779344), (Int.negOfNat 12167689072862617678740), (Int.ofNat 445869872161428237096), (Int.ofNat 46828517911028394966), (Int.negOfNat 1989231480905832276), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-22688758339390747408434250861040989/28147497671065600000000000000000000), (-2290599831435997854165567864934661/28147497671065600000000000000000000), (306569553310740855324227523786911/28147497671065600000000000000000000), (5560423882047742698652363667603/1759218604441600000000000000000000), (-2212639056819360982768205050029/7036874417766400000000000000000000), (-2369531745655435922438009084123/28147497671065600000000000000000000), (207972680756819597412942989971/28147497671065600000000000000000000), (35680300361658680634963758107/28147497671065600000000000000000000), (-2714526096149689292669016521/28147497671065600000000000000000000), (-349646564009388407249827553/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial145.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial145.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial145.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial145 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 25532349418635475949651896088738773), (Int.negOfNat 417035262985444500160779455291800), (Int.ofNat 506118125211385079991928278250280), (Int.negOfNat 29686942092945113520514122979133), (Int.negOfNat 14151678233878708221444043292631), (Int.ofNat 1433645414608511494224940837993), (Int.ofNat 268069214728005673196577868067), (Int.negOfNat 28536222872810070856601525294), (Int.negOfNat 3221273588476326483574467135), (Int.ofNat 311426188749885420412237107), (Int.ofNat 26746273162439853276085010), (Int.negOfNat 2143773399737949846021849), (Int.negOfNat 160531491068571936480366), (Int.ofNat 10149891252798912436652), (Int.ofNat 717976509934089513566), (Int.negOfNat 34045514559319104847), (Int.negOfNat 2022576979370677989), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-25532349418635475949651896088738773/28147497671065600000000000000000000), (-2085176314927222500803897276459/140737488355328000000000000000000), (12652953130284626999798206956257/703687441776640000000000000000000), (-29686942092945113520514122979133/28147497671065600000000000000000000), (-14151678233878708221444043292631/28147497671065600000000000000000000), (1433645414608511494224940837993/28147497671065600000000000000000000), (268069214728005673196577868067/28147497671065600000000000000000000), (-14268111436405035428300762647/14073748835532800000000000000000000), (-644254717695265296714893427/5629499534213120000000000000000000), (311426188749885420412237107/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial145.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial145.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial145.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial145 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 24747132147836868593620591168505222), (Int.ofNat 949245326464796166974168825157436), (Int.ofNat 144109379926810420165321796193530), (Int.negOfNat 62436439344160361970611095584116), (Int.ofNat 6179539112496586413392843327265), (Int.ofNat 1578108830404360870498436628863), (Int.negOfNat 231589334099691291532713825239), (Int.negOfNat 23583402355025166385793610748), (Int.ofNat 3617500574036170229783615457), (Int.ofNat 240037708674129689546452310), (Int.negOfNat 32444505420560108530897690), (Int.negOfNat 1758037883085836354942647), (Int.ofNat 189616271544632700670740), (Int.ofNat 9400210299759842524632), (Int.negOfNat 782580496479847695209), (Int.negOfNat 38021796341115363841), (Int.ofNat 3278791853069059776), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-12373566073918434296810295584252611/14073748835532800000000000000000000), (237311331616199041743542206289359/7036874417766400000000000000000000), (14410937992681042016532179619353/2814749767106560000000000000000000), (-15609109836040090492652773896029/7036874417766400000000000000000000), (1235907822499317282678568665453/5629499534213120000000000000000000), (1578108830404360870498436628863/28147497671065600000000000000000000), (-231589334099691291532713825239/28147497671065600000000000000000000), (-5895850588756291596448402687/7036874417766400000000000000000000), (3617500574036170229783615457/28147497671065600000000000000000000), (24003770867412968954645231/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial145.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial145.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial145.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial145 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 22639150778837262573146168024596926), (Int.ofNat 1049485527761550703277487026236441), (Int.negOfNat 20201711786241710472048268692260), (Int.ofNat 7087095085690990804800431058642), (Int.ofNat 5997616208034230154951569154723), (Int.negOfNat 1369600549476813064072219680731), (Int.negOfNat 117693531187729444714091861826), (Int.ofNat 33881312858548860020570011426), (Int.ofNat 1494246956440995462185563025), (Int.negOfNat 412422529650377092876118605), (Int.negOfNat 14244816190553677883140096), (Int.ofNat 3028408768620683467926578), (Int.ofNat 97494811813844275102179), (Int.negOfNat 15004574650304343527123), (Int.negOfNat 477338302417305075836), (Int.ofNat 54023679787466644572), (Int.ofNat 1583521554550053310), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-11319575389418631286573084012298463/14073748835532800000000000000000000), (1049485527761550703277487026236441/28147497671065600000000000000000000), (-1010085589312085523602413434613/1407374883553280000000000000000000), (3543547542845495402400215529321/14073748835532800000000000000000000), (5997616208034230154951569154723/28147497671065600000000000000000000), (-1369600549476813064072219680731/28147497671065600000000000000000000), (-58846765593864722357045930913/14073748835532800000000000000000000), (16940656429274430010285005713/14073748835532800000000000000000000), (59769878257639818487422521/1125899906842624000000000000000000), (-82484505930075418575223721/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial145.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial145.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial145.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial145 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 20515187493174753456683297154614510), (Int.ofNat 1129203788546202664885994357137100), (Int.ofNat 51919888585330442506647221786803), (Int.ofNat 802537066850098027903258572020), (Int.negOfNat 5319563038748422558037699062689), (Int.negOfNat 118612837928073233524277124712), (Int.ofNat 246012582075559303182789549274), (Int.ofNat 1424314536574647540037961524), (Int.negOfNat 4385405178655682126727838925), (Int.negOfNat 42923026466149263423861645), (Int.ofNat 41805664320497677542426304), (Int.ofNat 586678219103908968713822), (Int.negOfNat 252357394251202281705871), (Int.negOfNat 4293588819320886477927), (Int.ofNat 1063569879834703728514), (Int.ofNat 20790824554966560528), (Int.negOfNat 4132364122889289990), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-2051518749317475345668329715461451/2814749767106560000000000000000000), (11292037885462026648859943571371/281474976710656000000000000000000), (51919888585330442506647221786803/28147497671065600000000000000000000), (40126853342504901395162928601/1407374883553280000000000000000000), (-5319563038748422558037699062689/28147497671065600000000000000000000), (-14826604741009154190534640589/3518437208883200000000000000000000), (123006291037779651591394774637/14073748835532800000000000000000000), (356078634143661885009490381/7036874417766400000000000000000000), (-175416207146227285069113557/1125899906842624000000000000000000), (-8584605293229852684772329/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial145.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial145.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial145.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial145 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 18116763247835074357847092740411843), (Int.ofNat 1210296050823176778224414860562527), (Int.negOfNat 27998916218620160694686084963622), (Int.negOfNat 13790201616295310528001423385873), (Int.ofNat 4123374723188084522154619184207), (Int.ofNat 1230580420410824010234153534323), (Int.negOfNat 119939777472106493159109204739), (Int.negOfNat 38078061732131838416826210702), (Int.ofNat 1175945960770299829141913957), (Int.ofNat 498639883754211902336166940), (Int.negOfNat 4510023596741418779523890), (Int.negOfNat 3751482564351774133186153), (Int.negOfNat 3260276691888707237610), (Int.ofNat 18803642589470316703018), (Int.ofNat 119222084209409280291), (Int.negOfNat 69614188320717307609), (Int.negOfNat 717679994819313524), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-18116763247835074357847092740411843/28147497671065600000000000000000000), (1210296050823176778224414860562527/28147497671065600000000000000000000), (-13999458109310080347343042481811/14073748835532800000000000000000000), (-13790201616295310528001423385873/28147497671065600000000000000000000), (4123374723188084522154619184207/28147497671065600000000000000000000), (1230580420410824010234153534323/28147497671065600000000000000000000), (-119939777472106493159109204739/28147497671065600000000000000000000), (-19039030866065919208413105351/14073748835532800000000000000000000), (1175945960770299829141913957/28147497671065600000000000000000000), (24931994187710595116808347/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial145.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial145.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial145.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial145 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 15825141807818172711685895138509923), (Int.ofNat 1125413586831223110581099626327560), (Int.ofNat 36543494962313239264152290391005), (Int.ofNat 32471278576851963664298914915738), (Int.ofNat 1685830504829163959082860839317), (Int.negOfNat 2016692205270340987552261216800), (Int.negOfNat 253005104976179383198892725333), (Int.ofNat 30324788666260850279667659294), (Int.ofNat 5102636767304007683766271615), (Int.negOfNat 221687766805818246761438407), (Int.negOfNat 49433295945081722043347340), (Int.ofNat 945634727552487377669599), (Int.ofNat 298200776951679154510984), (Int.negOfNat 2394691897998525078852), (Int.negOfNat 1257750438362432180334), (Int.ofNat 2368973513591186097), (Int.ofNat 4553015612844150311), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-15825141807818172711685895138509923/28147497671065600000000000000000000), (28135339670780577764527490658189/703687441776640000000000000000000), (7308698992462647852830458078201/5629499534213120000000000000000000), (16235639288425981832149457457869/14073748835532800000000000000000000), (1685830504829163959082860839317/28147497671065600000000000000000000), (-2520865256587926234440326521/35184372088832000000000000000000), (-253005104976179383198892725333/28147497671065600000000000000000000), (15162394333130425139833829647/14073748835532800000000000000000000), (1020527353460801536753254323/5629499534213120000000000000000000), (-221687766805818246761438407/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial145.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial145.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial145.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial145 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 13217096772575783833228643551174561), (Int.ofNat 1523341578489746933050016036383259), (Int.ofNat 77751612023001348992217773954537), (Int.negOfNat 50943948639774590564123582918526), (Int.negOfNat 20938131578726929452558090001423), (Int.negOfNat 1008888253061080176215044611456), (Int.ofNat 458126604435445527008650992578), (Int.ofNat 44349503490778963594528828793), (Int.negOfNat 4501450682410130707389686271), (Int.negOfNat 579073378365888598571012797), (Int.ofNat 26649906849308298222880864), (Int.ofNat 4267933237421763184619365), (Int.negOfNat 107137950072529750383894), (Int.negOfNat 21087218337177376325410), (Int.ofNat 309484886827263437896), (Int.ofNat 76474853736071456234), (Int.negOfNat 571880377343913976), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-13217096772575783833228643551174561/28147497671065600000000000000000000), (1523341578489746933050016036383259/28147497671065600000000000000000000), (77751612023001348992217773954537/28147497671065600000000000000000000), (-25471974319887295282061791459263/14073748835532800000000000000000000), (-20938131578726929452558090001423/28147497671065600000000000000000000), (-7881939477039688876680036027/219902325555200000000000000000000), (229063302217722763504325496289/14073748835532800000000000000000000), (44349503490778963594528828793/28147497671065600000000000000000000), (-4501450682410130707389686271/28147497671065600000000000000000000), (-579073378365888598571012797/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial145.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial145.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial145.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial145 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 10600669877616776430674317497019335), (Int.ofNat 574355406707111693437145049312247), (Int.negOfNat 681703254354991346713832420117838), (Int.negOfNat 171276505756638928260752584274035), (Int.ofNat 2019673620188078093003212294132), (Int.ofNat 5353759667174684414169588834275), (Int.ofNat 327816823998046963268900243230), (Int.negOfNat 67718790286380569243004144412), (Int.negOfNat 6093370939495100203441930902), (Int.ofNat 505133562539007128152230866), (Int.ofNat 55465119660895074947754831), (Int.negOfNat 2564473158301537419421842), (Int.negOfNat 322710309765559576830973), (Int.ofNat 9559394177575658408339), (Int.ofNat 1333007097737360252093), (Int.negOfNat 26660654245105387487), (Int.negOfNat 4543813645411268132), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-2120133975523355286134863499403867/5629499534213120000000000000000000), (574355406707111693437145049312247/28147497671065600000000000000000000), (-340851627177495673356916210058919/14073748835532800000000000000000000), (-34255301151327785652150516854807/5629499534213120000000000000000000), (504918405047019523250803073533/7036874417766400000000000000000000), (214150386686987376566783553371/1125899906842624000000000000000000), (32781682399804696326890024323/2814749767106560000000000000000000), (-16929697571595142310751036103/7036874417766400000000000000000000), (-3046685469747550101720965451/14073748835532800000000000000000000), (252566781269503564076115433/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial145.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial145.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial145.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial145 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 13334287721991810165095438931396889), (Int.negOfNat 3687070505190101666402804925179710), (Int.negOfNat 1207465078060903935641057058991091), (Int.ofNat 66066711573228334604183757679896), (Int.ofNat 52078135783031065080089962046064), (Int.ofNat 2230828597765562082037497700418), (Int.negOfNat 830865450009503868293746282976), (Int.negOfNat 59378186807619606544372259743), (Int.ofNat 7656686558296594743067997702), (Int.ofNat 662825411595091539036899727), (Int.negOfNat 47423943835701967072393543), (Int.negOfNat 4536449428890846635760912), (Int.ofNat 213517076238329442697190), (Int.ofNat 21547188738056602931150), (Int.negOfNat 733591346559828309280), (Int.negOfNat 76371639265511643273), (Int.ofNat 1861440749507141476), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-13334287721991810165095438931396889/28147497671065600000000000000000000), (-368707050519010166640280492517971/2814749767106560000000000000000000), (-1207465078060903935641057058991091/28147497671065600000000000000000000), (8258338946653541825522969709987/3518437208883200000000000000000000), (3254883486439441567505622627879/1759218604441600000000000000000000), (1115414298882781041018748850209/14073748835532800000000000000000000), (-25964545312796995884179571343/879609302220800000000000000000000), (-59378186807619606544372259743/28147497671065600000000000000000000), (3828343279148297371533998851/14073748835532800000000000000000000), (662825411595091539036899727/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial145.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial145.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial145.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial145 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 24163651798775898761657193933666042), (Int.negOfNat 6056211259094893734871899984335228), (Int.ofNat 394085437936248864953701087844278), (Int.ofNat 422128448440791503819993797344828), (Int.ofNat 18361604203096244687526667833476), (Int.negOfNat 8449652337005799063089041858658), (Int.negOfNat 568982484408514560901629546627), (Int.ofNat 96441757373021067156674197204), (Int.ofNat 7446810636566162674667978279), (Int.negOfNat 728673682374133889556918629), (Int.negOfNat 59140725220520713485820543), (Int.ofNat 3932356344273474785643920), (Int.ofNat 321580102133135970510575), (Int.negOfNat 15933756243717888750843), (Int.negOfNat 1279822651745629999507), (Int.ofNat 49211619658893484417), (Int.ofNat 4534611677978385953), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-12081825899387949380828596966833021/14073748835532800000000000000000000), (-1514052814773723433717974996083807/7036874417766400000000000000000000), (197042718968124432476850543922139/14073748835532800000000000000000000), (105532112110197875954998449336207/7036874417766400000000000000000000), (4590401050774061171881666958369/7036874417766400000000000000000000), (-4224826168502899531544520929329/14073748835532800000000000000000000), (-568982484408514560901629546627/28147497671065600000000000000000000), (24110439343255266789168549301/7036874417766400000000000000000000), (7446810636566162674667978279/28147497671065600000000000000000000), (-728673682374133889556918629/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial145.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial145.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial145.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial145 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 31321896555751888744316991850280868), (Int.ofNat 436927377422344319547970418391054), (Int.ofNat 2629250659151782792560739108872346), (Int.ofNat 202721123749664002241592247273267), (Int.negOfNat 68462736415063811440965775498394), (Int.negOfNat 5643583525073659583724628002581), (Int.ofNat 999689718191792729248939280751), (Int.ofNat 80590144070732373603845334158), (Int.negOfNat 9426867508120947452602533853), (Int.negOfNat 723832317274848502004847484), (Int.ofNat 61739415252514559870651118), (Int.ofNat 4462846722429229182004523), (Int.negOfNat 296121780926030192883949), (Int.negOfNat 19989540255013770966454), (Int.ofNat 1081977890918112693420), (Int.ofNat 67154738056831984295), (Int.negOfNat 3147933799192741583), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-7830474138937972186079247962570217/7036874417766400000000000000000000), (218463688711172159773985209195527/14073748835532800000000000000000000), (1314625329575891396280369554436173/14073748835532800000000000000000000), (202721123749664002241592247273267/28147497671065600000000000000000000), (-34231368207531905720482887749197/14073748835532800000000000000000000), (-5643583525073659583724628002581/28147497671065600000000000000000000), (999689718191792729248939280751/28147497671065600000000000000000000), (40295072035366186801922667079/14073748835532800000000000000000000), (-9426867508120947452602533853/28147497671065600000000000000000000), (-180958079318712125501211871/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial145.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial145.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial145.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial145.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial145 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial145 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial145 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 35370080997336868917120804052845211), (Int.negOfNat 637709458391761232836203938918431), (Int.ofNat 2797593040861354341512105650727910), (Int.negOfNat 270567514288849995274661229033988), (Int.negOfNat 72212548290748104970782659228379), (Int.ofNat 7668024901715958741898728677913), (Int.ofNat 1051785865288694338021429563108), (Int.negOfNat 106293715172787603681747644558), (Int.negOfNat 9861319890030199004976288603), (Int.ofNat 909519090706579761138668684), (Int.ofNat 64101051088726487658922168), (Int.negOfNat 5332344663175459928443423), (Int.negOfNat 305076511638769564312149), (Int.ofNat 22849977645935203143354), (Int.ofNat 1106567749520054841420), (Int.negOfNat 74531695637414628695), (Int.negOfNat 3147933799192741583), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-35370080997336868917120804052845211/28147497671065600000000000000000000), (-637709458391761232836203938918431/28147497671065600000000000000000000), (279759304086135434151210565072791/2814749767106560000000000000000000), (-67641878572212498818665307258497/7036874417766400000000000000000000), (-72212548290748104970782659228379/28147497671065600000000000000000000), (7668024901715958741898728677913/28147497671065600000000000000000000), (262946466322173584505357390777/7036874417766400000000000000000000), (-53146857586393801840873822279/14073748835532800000000000000000000), (-9861319890030199004976288603/28147497671065600000000000000000000), (227379772676644940284667171/7036874417766400000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial145.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial145.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial145.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 28477988293090549278492297023345828), (Int.ofNat 5755075782966018634701673586768538), (Int.ofNat 222619258867290466724981617819997), (Int.negOfNat 444835200390252714639845955509472), (Int.ofNat 31042008105660529553842579884450), (Int.ofNat 9113230469090743699373196618915), (Int.negOfNat 805433426937233150777860676427), (Int.negOfNat 104595008507727538003857569504), (Int.ofNat 9677928864398303627462783829), (Int.ofNat 786614562543723554438337479), (Int.negOfNat 71996785127179751325977043), (Int.negOfNat 4201600441465310607270520), (Int.ofNat 371682504178855789310325), (Int.ofNat 16816532167527611864043), (Int.negOfNat 1421624169683496386307), (Int.negOfNat 51670605519087699217), (Int.ofNat 4534611677978385953), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-7119497073272637319623074255836457/7036874417766400000000000000000000), (2877537891483009317350836793384269/14073748835532800000000000000000000), (222619258867290466724981617819997/28147497671065600000000000000000000), (-13901100012195397332495186109671/879609302220800000000000000000000), (620840162113210591076851597689/562949953421312000000000000000000), (1822646093818148739874639323783/5629499534213120000000000000000000), (-805433426937233150777860676427/28147497671065600000000000000000000), (-3268594015866485562620549047/879609302220800000000000000000000), (9677928864398303627462783829/28147497671065600000000000000000000), (786614562543723554438337479/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial145.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial145.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial145.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 18909882088172490794937788377837102), (Int.ofNat 2839747794160742415229295826646955), (Int.negOfNat 1215870090671517476275614787440193), (Int.ofNat 921527689057876866507570109874), (Int.ofNat 57479189381092551657030004728385), (Int.negOfNat 4079596075458851574131698670432), (Int.negOfNat 936772127513748596621705588651), (Int.ofNat 82805831795842636316360006793), (Int.ofNat 8666513465347256890065811952), (Int.negOfNat 832243642511059344162649277), (Int.negOfNat 53266026912922638023885943), (Int.ofNat 5330233202252982523391812), (Int.ofNat 236322424069420711918690), (Int.negOfNat 24159268557098419413250), (Int.negOfNat 798344640878275965680), (Int.ofNat 82109272939298144473), (Int.ofNat 1861440749507141476), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-9454941044086245397468894188918551/14073748835532800000000000000000000), (567949558832148483045859165329391/5629499534213120000000000000000000), (-1215870090671517476275614787440193/28147497671065600000000000000000000), (460763844528938433253785054937/14073748835532800000000000000000000), (11495837876218510331406000945677/5629499534213120000000000000000000), (-127487377358089111691615583451/879609302220800000000000000000000), (-936772127513748596621705588651/28147497671065600000000000000000000), (82805831795842636316360006793/28147497671065600000000000000000000), (541657091584203555629113247/1759218604441600000000000000000000), (-832243642511059344162649277/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial145.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial145.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial145.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 17344979304597380099495160092093969), (Int.negOfNat 635722308631446681382244003852611), (Int.negOfNat 315144079563230688385131194213141), (Int.ofNat 204541268837850195311320226480838), (Int.negOfNat 10456796758715908540902176456199), (Int.negOfNat 6416863085639108758698845952975), (Int.ofNat 541997728128438516567393251187), (Int.ofNat 81764380376786270172713309762), (Int.negOfNat 8070534517267484970935637552), (Int.negOfNat 608438146713607754156623766), (Int.ofNat 66756040493029626892578231), (Int.ofNat 3052145857944106673436392), (Int.negOfNat 366532114613568925279423), (Int.negOfNat 11167706521462617362689), (Int.ofNat 1456776052700469063693), (Int.ofNat 29939302058697673887), (Int.negOfNat 4543813645411268132), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-17344979304597380099495160092093969/28147497671065600000000000000000000), (-635722308631446681382244003852611/28147497671065600000000000000000000), (-315144079563230688385131194213141/28147497671065600000000000000000000), (102270634418925097655660113240419/14073748835532800000000000000000000), (-10456796758715908540902176456199/28147497671065600000000000000000000), (-256674523425564350347953838119/1125899906842624000000000000000000), (541997728128438516567393251187/28147497671065600000000000000000000), (40882190188393135086356654881/14073748835532800000000000000000000), (-504408407329217810683477347/1759218604441600000000000000000000), (-304219073356803877078311883/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial145.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial145.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial145.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 18570469297373100898843360430774519), (Int.negOfNat 158375266305612877446360293383002), (Int.ofNat 316379385715229326638096058638353), (Int.negOfNat 19902437483781716613016760118326), (Int.negOfNat 29726622060680870029273858372141), (Int.ofNat 2702386331102700796186311165720), (Int.ofNat 620387426157293031103240268271), (Int.negOfNat 64628672102574832936745749443), (Int.negOfNat 6049387713549551690051050471), (Int.ofNat 722067386373380046633872547), (Int.ofNat 35621160727794836513502164), (Int.negOfNat 4930171794092762341248565), (Int.negOfNat 142194820128112404601144), (Int.ofNat 23254086124204097453560), (Int.ofNat 408663983188430101496), (Int.negOfNat 82212487409857957434), (Int.negOfNat 571880377343913976), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-18570469297373100898843360430774519/28147497671065600000000000000000000), (-79187633152806438723180146691501/14073748835532800000000000000000000), (316379385715229326638096058638353/28147497671065600000000000000000000), (-9951218741890858306508380059163/14073748835532800000000000000000000), (-29726622060680870029273858372141/28147497671065600000000000000000000), (67559658277567519904657779143/703687441776640000000000000000000), (620387426157293031103240268271/28147497671065600000000000000000000), (-64628672102574832936745749443/28147497671065600000000000000000000), (-6049387713549551690051050471/28147497671065600000000000000000000), (722067386373380046633872547/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial145.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial145.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial145.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 18139792005729542881769445506278123), (Int.ofNat 219006455484911759241675717740305), (Int.negOfNat 202068255325702848268887748059289), (Int.negOfNat 93178861587639729529540541897268), (Int.ofNat 12821701807117254791853078642473), (Int.ofNat 3598676514878032504843909213500), (Int.negOfNat 433113039107045592584894995133), (Int.negOfNat 50280894045645713637256551144), (Int.ofNat 6694919746128714518538776615), (Int.ofNat 365899040476903333975175357), (Int.negOfNat 58333741863904793343394640), (Int.negOfNat 1621150070613517280336349), (Int.ofNat 332399096966330402882484), (Int.ofNat 4615792965269461407752), (Int.negOfNat 1352831224956608485934), (Int.negOfNat 8106607187377687297), (Int.ofNat 4553015612844150311), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-18139792005729542881769445506278123/28147497671065600000000000000000000), (43801291096982351848335143548061/5629499534213120000000000000000000), (-202068255325702848268887748059289/28147497671065600000000000000000000), (-23294715396909932382385135474317/7036874417766400000000000000000000), (12821701807117254791853078642473/28147497671065600000000000000000000), (7197353029756065009687818427/56294995342131200000000000000000), (-433113039107045592584894995133/28147497671065600000000000000000000), (-6285111755705714204657068893/3518437208883200000000000000000000), (1338983949225742903707755323/5629499534213120000000000000000000), (365899040476903333975175357/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial145.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial145.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial145.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 18967493757240921273228405520025004), (Int.negOfNat 1107517910131011047740383647396760), (Int.negOfNat 290273948416139667228198762316916), (Int.ofNat 68924101346449499394697432700672), (Int.ofNat 16906599718391094347336395017154), (Int.negOfNat 2569792351677468611128720874180), (Int.negOfNat 341655182628951055689552285889), (Int.ofNat 53314819690577447348511026452), (Int.ofNat 3210525058692370291717984207), (Int.negOfNat 602965003781078404586600490), (Int.negOfNat 16089041253047619403532590), (Int.ofNat 4227726119711670135705253), (Int.ofNat 41608561002401502046990), (Int.negOfNat 20351028766165933408668), (Int.negOfNat 7005856613893746109), (Int.ofNat 72892836134309594009), (Int.negOfNat 717679994819313524), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-4741873439310230318307101380006251/7036874417766400000000000000000000), (-27687947753275276193509591184919/703687441776640000000000000000000), (-72568487104034916807049690579229/7036874417766400000000000000000000), (269234770884568357010536846487/109951162777600000000000000000000), (8453299859195547173668197508577/14073748835532800000000000000000000), (-128489617583873430556436043709/1407374883553280000000000000000000), (-341655182628951055689552285889/28147497671065600000000000000000000), (13328704922644361837127756613/7036874417766400000000000000000000), (3210525058692370291717984207/28147497671065600000000000000000000), (-60296500378107840458660049/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial145.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial145.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial145.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 21618496589534739569459235354607704), (Int.negOfNat 1145945894111325722566547566054143), (Int.ofNat 280184102559749691466873369783036), (Int.ofNat 79018696780304933208702182426769), (Int.negOfNat 13237502682664005634095251890306), (Int.negOfNat 1975492499877013864941187453306), (Int.ofNat 365741710543561196155443776174), (Int.ofNat 23661069963901627736236454526), (Int.negOfNat 5412966571392556037793264425), (Int.negOfNat 133471129057499564238073055), (Int.ofNat 47467310348855511748866354), (Int.ofNat 229022135309864216738178), (Int.negOfNat 273959108244947813717321), (Int.ofNat 1628366564628137816977), (Int.ofNat 1123405202432762955314), (Int.negOfNat 14233528927781987728), (Int.negOfNat 4132364122889289990), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-2702312073691842446182404419325963/3518437208883200000000000000000000), (-1145945894111325722566547566054143/28147497671065600000000000000000000), (70046025639937422866718342445759/7036874417766400000000000000000000), (79018696780304933208702182426769/28147497671065600000000000000000000), (-6618751341332002817047625945153/14073748835532800000000000000000000), (-987746249938506932470593726653/14073748835532800000000000000000000), (182870855271780598077721888087/14073748835532800000000000000000000), (11830534981950813868118227263/14073748835532800000000000000000000), (-216518662855702241511730577/1125899906842624000000000000000000), (-26694225811499912847614611/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial145.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial145.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial145.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 22407488181919027067986385152944657), (Int.ofNat 416586654188649156176510890335659), (Int.ofNat 372455415677268215145666551719007), (Int.negOfNat 43840541074124599805209237085828), (Int.negOfNat 10408898807519922412394793380360), (Int.ofNat 2070244727883482018554865885538), (Int.ofNat 148888062295960640507192739074), (Int.negOfNat 41699760296714292204940669776), (Int.negOfNat 877135921971904785268899075), (Int.ofNat 465872141465430857047491755), (Int.negOfNat 946085904730616931551346), (Int.negOfNat 3272357715124826812728678), (Int.ofNat 46317099964316183072779), (Int.ofNat 15799009909584912614623), (Int.negOfNat 334717122526040617436), (Int.negOfNat 56482665647660859372), (Int.ofNat 1583521554550053310), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-22407488181919027067986385152944657/28147497671065600000000000000000000), (416586654188649156176510890335659/28147497671065600000000000000000000), (372455415677268215145666551719007/28147497671065600000000000000000000), (-10960135268531149951302309271457/7036874417766400000000000000000000), (-260222470187998060309869834509/703687441776640000000000000000000), (1035122363941741009277432942769/14073748835532800000000000000000000), (74444031147980320253596369537/14073748835532800000000000000000000), (-2606235018544643262808791861/1759218604441600000000000000000000), (-35085436878876191410755963/1125899906842624000000000000000000), (93174428293086171409498351/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial145.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial145.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial145.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 20531314201296070896176911377661411), (Int.ofNat 1222897062475431150640696430872306), (Int.ofNat 33406419474521860094459036756981), (Int.negOfNat 43042274961806846675205634893810), (Int.ofNat 8307130801566305130509597442468), (Int.ofNat 805378810984103827881078867255), (Int.negOfNat 265815138232583840932272802639), (Int.negOfNat 4153639797034552089859457202), (Int.ofNat 3932289424044435728659416557), (Int.negOfNat 47138791847977347112756910), (Int.negOfNat 34242303706745128496422690), (Int.ofNat 870513180090871782835347), (Int.ofNat 196597786410801799145340), (Int.negOfNat 6506119533631194180182), (Int.negOfNat 802252383361401413609), (Int.ofNat 30644838760532719441), (Int.ofNat 3278791853069059776), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-20531314201296070896176911377661411/28147497671065600000000000000000000), (611448531237715575320348215436153/14073748835532800000000000000000000), (33406419474521860094459036756981/28147497671065600000000000000000000), (-4304227496180684667520563489381/2814749767106560000000000000000000), (2076782700391576282627399360617/7036874417766400000000000000000000), (161075762196820765576215773451/5629499534213120000000000000000000), (-265815138232583840932272802639/28147497671065600000000000000000000), (-2076819898517276044929728601/14073748835532800000000000000000000), (3932289424044435728659416557/28147497671065600000000000000000000), (-4713879184797734711275691/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial145.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial145.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial145.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 18154140228441080070161717432107323), (Int.ofNat 1121133537281130026062700427976040), (Int.negOfNat 21161197306089075462568303784551), (Int.ofNat 17097223927982546593190038878153), (Int.ofNat 3061454923296765057748508713495), (Int.negOfNat 1299989154109348090306361332450), (Int.negOfNat 7736585261837341018880173883), (Int.ofNat 27676233231540424946238170944), (Int.negOfNat 764246506923730004126387085), (Int.negOfNat 307717343294256710038788457), (Int.ofNat 12949728220110420549167310), (Int.ofNat 2131683984887492473134349), (Int.negOfNat 107406810897083539450666), (Int.negOfNat 10116921948225151865552), (Int.ofNat 569617696369038553966), (Int.ofNat 34045514559319104847), (Int.negOfNat 2022576979370677989), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-18154140228441080070161717432107323/28147497671065600000000000000000000), (28028338432028250651567510699401/703687441776640000000000000000000), (-21161197306089075462568303784551/28147497671065600000000000000000000), (17097223927982546593190038878153/28147497671065600000000000000000000), (612290984659353011549701742699/5629499534213120000000000000000000), (-25999783082186961806127226649/562949953421312000000000000000000), (-7736585261837341018880173883/28147497671065600000000000000000000), (432441144242819139784971421/439804651110400000000000000000000), (-152849301384746000825277417/5629499534213120000000000000000000), (-307717343294256710038788457/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial145.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial145.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial145.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 15849645194116134415587760805802124), (Int.ofNat 1245132027508682276916036016643268), (Int.ofNat 65052660504286161101723966036145), (Int.ofNat 1100683067271055090493755483750), (Int.negOfNat 4502523620930499461071780921048), (Int.ofNat 123138171244930389952433134162), (Int.ofNat 154308074317869515253711883171), (Int.negOfNat 8715974063352407219855135907), (Int.negOfNat 2295622691044653083328202421), (Int.ofNat 159531208357393418526701503), (Int.ofNat 19554722951079488552635114), (Int.negOfNat 1527932680856915356505535), (Int.negOfNat 108576373365027546018494), (Int.ofNat 9288535048332972330190), (Int.ofNat 423738999419680303896), (Int.negOfNat 39451560330445750566), (Int.negOfNat 1989231480905832276), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-3962411298529033603896940201450531/7036874417766400000000000000000000), (311283006877170569229009004160817/7036874417766400000000000000000000), (13010532100857232220344793207229/5629499534213120000000000000000000), (880546453816844072395004387/22517998136852480000000000000000), (-562815452616312432633972615131/3518437208883200000000000000000000), (61569085622465194976216567081/14073748835532800000000000000000000), (154308074317869515253711883171/28147497671065600000000000000000000), (-8715974063352407219855135907/28147497671065600000000000000000000), (-2295622691044653083328202421/28147497671065600000000000000000000), (159531208357393418526701503/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial145.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial145.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial145.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 13150194384541398844100538708417527), (Int.ofNat 1408141174719703896889718322601913), (Int.ofNat 1421925398384962612993292657182), (Int.negOfNat 13215198249370717821053804150524), (Int.ofNat 1807238638771044512046733191254), (Int.ofNat 640740893822230009783476690050), (Int.negOfNat 78666891372374106194778719370), (Int.negOfNat 13382855127900782819688469562), (Int.ofNat 1648307885725439095596094848), (Int.ofNat 143246594174911317129296866), (Int.negOfNat 18763963378877816839381169), (Int.negOfNat 929178166065992575380642), (Int.ofNat 133831545762892170503177), (Int.ofNat 4024810524412068069739), (Int.negOfNat 654049110463816549007), (Int.negOfNat 11173449862313871437), (Int.ofNat 2031778946803560168), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-13150194384541398844100538708417527/28147497671065600000000000000000000), (1408141174719703896889718322601913/28147497671065600000000000000000000), (710962699192481306496646328591/14073748835532800000000000000000000), (-3303799562342679455263451037631/7036874417766400000000000000000000), (903619319385522256023366595627/14073748835532800000000000000000000), (12814817876444600195669533801/562949953421312000000000000000000), (-7866689137237410619477871937/2814749767106560000000000000000000), (-6691427563950391409844234781/14073748835532800000000000000000000), (12877405357229992934344491/219902325555200000000000000000000), (71623297087455658564648433/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial145.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial145.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial145.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 10390799317237232963651165444216074), (Int.ofNat 1345152638895547956910355677180214), (Int.negOfNat 7728639387867095044183695136917), (Int.ofNat 10203395166829587713889339871245), (Int.ofNat 1897415937844348403686512991221), (Int.negOfNat 564777756211223634206712749125), (Int.negOfNat 53657318959426937205044672501), (Int.ofNat 14237048844680549158096104707), (Int.ofNat 719867928572604105380119202), (Int.negOfNat 197418690283319535546741873), (Int.negOfNat 5161474133045690287435243), (Int.ofNat 1682679983347759021154038), (Int.ofNat 21184341006001773392640), (Int.negOfNat 9645874346234951171800), (Int.negOfNat 46969553553321214830), (Int.ofNat 40487009350957258077), (Int.ofNat 699671108742604776), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-5195399658618616481825582722108037/14073748835532800000000000000000000), (672576319447773978455177838590107/14073748835532800000000000000000000), (-7728639387867095044183695136917/28147497671065600000000000000000000), (2040679033365917542777867974249/5629499534213120000000000000000000), (1897415937844348403686512991221/28147497671065600000000000000000000), (-4518222049689789073653701993/225179981368524800000000000000000), (-53657318959426937205044672501/28147497671065600000000000000000000), (14237048844680549158096104707/28147497671065600000000000000000000), (359933964286302052690059601/14073748835532800000000000000000000), (-197418690283319535546741873/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial145.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial145.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial145.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 7639026018096433609912709960715026), (Int.ofNat 1448564736126957260922738144081742), (Int.ofNat 50905163898211813504144923197075), (Int.ofNat 2399265989263254972162878719784), (Int.negOfNat 2972244964873079881823785818078), (Int.negOfNat 81074883144560666709974949215), (Int.ofNat 100353516776721504746089776823), (Int.ofNat 776920935649687107203018554), (Int.negOfNat 1748536190502056417891308571), (Int.ofNat 5562064273967794521195171), (Int.ofNat 18180031235074229181109757), (Int.negOfNat 174227166694527448223180), (Int.negOfNat 123822579290310094251875), (Int.ofNat 1635621210205056451557), (Int.ofNat 591503919984990035693), (Int.negOfNat 10080592416070353233), (Int.negOfNat 2040980914236442347), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-3819513009048216804956354980357513/14073748835532800000000000000000000), (724282368063478630461369072040871/14073748835532800000000000000000000), (2036206555928472540165796927883/1125899906842624000000000000000000), (299908248657906871520359839973/3518437208883200000000000000000000), (-1486122482436539940911892909039/14073748835532800000000000000000000), (-16214976628912133341994989843/5629499534213120000000000000000000), (100353516776721504746089776823/28147497671065600000000000000000000), (388460467824843553601509277/14073748835532800000000000000000000), (-1748536190502056417891308571/28147497671065600000000000000000000), (5562064273967794521195171/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial145.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial145.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial145.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 4563137009531118586436534776335343), (Int.ofNat 1597305231795299942948847049578055), (Int.ofNat 9176707853135913211542805856069), (Int.negOfNat 10974692417719767682563242114635), (Int.ofNat 742276502986093363505438714917), (Int.ofNat 546298171909569291167745247494), (Int.negOfNat 28905453047377130406282946642), (Int.negOfNat 12590175962784120290223569942), (Int.ofNat 580886592277604721324852247), (Int.ofNat 163956053050537837784220566), (Int.negOfNat 6909208460549605872451082), (Int.negOfNat 1352739641445421530170277), (Int.ofNat 53088285589924804960851), (Int.ofNat 7641805077904123654496), (Int.negOfNat 278571208421583921980), (Int.negOfNat 31802682907282768405), (Int.ofNat 592956585898250117), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-4563137009531118586436534776335343/28147497671065600000000000000000000), (319461046359059988589769409915611/5629499534213120000000000000000000), (9176707853135913211542805856069/28147497671065600000000000000000000), (-2194938483543953536512648422927/5629499534213120000000000000000000), (742276502986093363505438714917/28147497671065600000000000000000000), (273149085954784645583872623747/14073748835532800000000000000000000), (-14452726523688565203141473321/14073748835532800000000000000000000), (-6295087981392060145111784971/14073748835532800000000000000000000), (580886592277604721324852247/28147497671065600000000000000000000), (81978026525268918892110283/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial145.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial145.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial145.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 1393497698336879949273100968708796), (Int.ofNat 1559505852609297528179196607346107), (Int.negOfNat 8867413796794719226381515476708), (Int.ofNat 6907141854708147805203304996386), (Int.ofNat 2116504006104382910816259188993), (Int.negOfNat 355556901899500357646203331738), (Int.negOfNat 68611908493154396721113270058), (Int.ofNat 8555793209053959795247841808), (Int.ofNat 1162696542190025680378871903), (Int.negOfNat 116941585769561934545953384), (Int.negOfNat 11932442777338099721721018), (Int.ofNat 1014542122960639110923373), (Int.ofNat 81269405322695186586449), (Int.negOfNat 6015373368467937038104), (Int.negOfNat 391998137953720281570), (Int.ofNat 26958003026620435095), (Int.ofNat 1187408644416212133), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-348374424584219987318275242177199/7036874417766400000000000000000000), (1559505852609297528179196607346107/28147497671065600000000000000000000), (-2216853449198679806595378869177/7036874417766400000000000000000000), (3453570927354073902601652498193/14073748835532800000000000000000000), (2116504006104382910816259188993/28147497671065600000000000000000000), (-177778450949750178823101665869/14073748835532800000000000000000000), (-34305954246577198360556635029/14073748835532800000000000000000000), (534737075565872487202990113/1759218604441600000000000000000000), (1162696542190025680378871903/28147497671065600000000000000000000), (-14617698221195241818244173/3518437208883200000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial145.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial145.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial145.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 1764719622443360783355194094649862), (Int.ofNat 1637738125202622939003924106288257), (Int.ofNat 45649819644546732421330603836231), (Int.ofNat 4751837018480791870419602473828), (Int.negOfNat 2439187593690676728005904656671), (Int.negOfNat 235359363567024833698110321240), (Int.ofNat 80971482924734540395019211277), (Int.ofNat 5496925335493198751541135854), (Int.negOfNat 1405538738760578850363184579), (Int.negOfNat 73541013950858806613672779), (Int.ofNat 14762091907649544041075043), (Int.ofNat 628955403605442112069370), (Int.negOfNat 102701735327860426252025), (Int.negOfNat 3696509408783551644943), (Int.ofNat 503775230710164443407), (Int.ofNat 17023555229070941617), (Int.negOfNat 1458798145628989903), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(882359811221680391677597047324931/14073748835532800000000000000000000), (1637738125202622939003924106288257/28147497671065600000000000000000000), (45649819644546732421330603836231/28147497671065600000000000000000000), (1187959254620197967604900618457/7036874417766400000000000000000000), (-2439187593690676728005904656671/28147497671065600000000000000000000), (-5883984089175620842452758031/703687441776640000000000000000000), (80971482924734540395019211277/28147497671065600000000000000000000), (2748462667746599375770567927/14073748835532800000000000000000000), (-1405538738760578850363184579/28147497671065600000000000000000000), (-73541013950858806613672779/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial145.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial145.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial145.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 5219755619032597747404964165785337), (Int.ofNat 1796957139190180159413349339142119), (Int.ofNat 17241514210860674113167583630637), (Int.negOfNat 10815347115955873995304711047493), (Int.negOfNat 54926211534977924443238652642), (Int.ofNat 546656512936046789510239352532), (Int.ofNat 3514025112375320744492255351), (Int.negOfNat 12862078926072389832739494043), (Int.negOfNat 104127450050063754079995952), (Int.ofNat 171493792160639484640731627), (Int.ofNat 1609656050628499091644293), (Int.negOfNat 1451353423643716760898212), (Int.negOfNat 14850058423678236121040), (Int.ofNat 8404755946106730867100), (Int.ofNat 88890459723599363680), (Int.negOfNat 35355242281902022473), (Int.ofNat 99084405269387974), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(5219755619032597747404964165785337/28147497671065600000000000000000000), (1796957139190180159413349339142119/28147497671065600000000000000000000), (17241514210860674113167583630637/28147497671065600000000000000000000), (-10815347115955873995304711047493/28147497671065600000000000000000000), (-27463105767488962221619326321/14073748835532800000000000000000000), (136664128234011697377559838133/7036874417766400000000000000000000), (3514025112375320744492255351/28147497671065600000000000000000000), (-12862078926072389832739494043/28147497671065600000000000000000000), (-6507965628128984629999747/1759218604441600000000000000000000), (171493792160639484640731627/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial145.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial145.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial145.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 8811365750302319068041130737722911), (Int.ofNat 1773306867075985714666354184213102), (Int.negOfNat 12454565584596886781139366537861), (Int.ofNat 4670546299568765036395898868973), (Int.ofNat 2557454919411334023152993969427), (Int.negOfNat 221194059296613698935229504475), (Int.negOfNat 88075551536101582674909639187), (Int.ofNat 4577205180441952324007630438), (Int.ofNat 1573631115688695051198682802), (Int.negOfNat 50982840839925914517835134), (Int.negOfNat 16872474576539727197171181), (Int.ofNat 341858260535715619518208), (Int.ofNat 118855574430873629805723), (Int.negOfNat 1483106391127348347011), (Int.negOfNat 585196776034586229043), (Int.ofNat 3888086277921012113), (Int.ofNat 1468000113061872082), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(8811365750302319068041130737722911/28147497671065600000000000000000000), (886653433537992857333177092106551/14073748835532800000000000000000000), (-12454565584596886781139366537861/28147497671065600000000000000000000), (4670546299568765036395898868973/28147497671065600000000000000000000), (2557454919411334023152993969427/28147497671065600000000000000000000), (-8847762371864547957409180179/1125899906842624000000000000000000), (-88075551536101582674909639187/28147497671065600000000000000000000), (2288602590220976162003815219/14073748835532800000000000000000000), (786815557844347525599341401/14073748835532800000000000000000000), (-25491420419962957258917567/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial145.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial145.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial145.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 12374676342736178219789351280124389), (Int.ofNat 1830232449557342335218784217584161), (Int.ofNat 43597714454403724876399309152439), (Int.ofNat 7067246869898328878387133842102), (Int.negOfNat 2298877353121926464673446609584), (Int.negOfNat 406369708889897669505226410177), (Int.ofNat 72634554876425593563683234429), (Int.ofNat 10632301199421589417175451193), (Int.negOfNat 1151998762293074465519005729), (Int.negOfNat 154242594482571534423421947), (Int.ofNat 10666792175582145304569986), (Int.ofNat 1386884888664634161552515), (Int.negOfNat 63654505283892012898956), (Int.negOfNat 8351711135102740582410), (Int.ofNat 262804169991369895154), (Int.ofNat 36278118705859907034), (Int.negOfNat 1388644777432615474), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(12374676342736178219789351280124389/28147497671065600000000000000000000), (1830232449557342335218784217584161/28147497671065600000000000000000000), (43597714454403724876399309152439/28147497671065600000000000000000000), (3533623434949164439193566921051/14073748835532800000000000000000000), (-143679834570120404042090413099/1759218604441600000000000000000000), (-406369708889897669505226410177/28147497671065600000000000000000000), (72634554876425593563683234429/28147497671065600000000000000000000), (10632301199421589417175451193/28147497671065600000000000000000000), (-1151998762293074465519005729/28147497671065600000000000000000000), (-154242594482571534423421947/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial145.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial145.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial145.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 16221933307874901056635445162336523), (Int.ofNat 2000598966804908380074237793374950), (Int.ofNat 20277057178903529674450175921670), (Int.negOfNat 12683466867232945746076652743567), (Int.negOfNat 748419875678792315623112484569), (Int.ofNat 649499339358675856331117503007), (Int.ofNat 39842032147704602817554280683), (Int.negOfNat 14810458070809294030959821656), (Int.negOfNat 949637474385000667083127965), (Int.ofNat 183143990215503935928684293), (Int.ofNat 12257790128544092303998790), (Int.negOfNat 1388241388442738868218901), (Int.negOfNat 96801721649757832940084), (Int.ofNat 7051720363143664826398), (Int.ofNat 512665632211334195134), (Int.negOfNat 24901119195842927103), (Int.negOfNat 1477202080494754261), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(16221933307874901056635445162336523/28147497671065600000000000000000000), (40011979336098167601484755867499/562949953421312000000000000000000), (2027705717890352967445017592167/2814749767106560000000000000000000), (-12683466867232945746076652743567/28147497671065600000000000000000000), (-748419875678792315623112484569/28147497671065600000000000000000000), (649499339358675856331117503007/28147497671065600000000000000000000), (39842032147704602817554280683/28147497671065600000000000000000000), (-1851307258851161753869977707/3518437208883200000000000000000000), (-189927494877000133416625593/5629499534213120000000000000000000), (183143990215503935928684293/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial145.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial145.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial145.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 20212095187596527690478785930728472), (Int.ofNat 1958025394714418961797154076602014), (Int.negOfNat 22977370988820011971110900526380), (Int.ofNat 4793974671742691149835273149966), (Int.ofNat 3761868774595674700473178631835), (Int.negOfNat 121955476934542756241537431213), (Int.negOfNat 133991076149701922573843765411), (Int.negOfNat 700812716223374269131374952), (Int.ofNat 2316351872984198392456969443), (Int.ofNat 55405850210737658934932340), (Int.negOfNat 22756022350584371487588460), (Int.negOfNat 780788836659931912620953), (Int.ofNat 141876933850106952030460), (Int.ofNat 5744081484668299365868), (Int.negOfNat 613599517634011243591), (Int.negOfNat 27778129383709615209), (Int.ofNat 2678205149595842974), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(2526511898449565961309848241341059/3518437208883200000000000000000000), (979012697357209480898577038301007/14073748835532800000000000000000000), (-1148868549441000598555545026319/1407374883553280000000000000000000), (2396987335871345574917636574983/14073748835532800000000000000000000), (752373754919134940094635726367/5629499534213120000000000000000000), (-121955476934542756241537431213/28147497671065600000000000000000000), (-133991076149701922573843765411/28147497671065600000000000000000000), (-87601589527921783641421869/3518437208883200000000000000000000), (2316351872984198392456969443/28147497671065600000000000000000000), (2770292510536882946746617/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial145.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial145.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial145.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 24122807552682085941959243505669526), (Int.ofNat 2010604729054337767229582074048209), (Int.ofNat 57818419340835600012957572981760), (Int.ofNat 12263094314249955099524612000008), (Int.negOfNat 3195097209828049073638327293673), (Int.negOfNat 830302073171412643685712122569), (Int.ofNat 73986096782867630818753057826), (Int.ofNat 22295821547633521502842917824), (Int.negOfNat 585925527812896623072613475), (Int.negOfNat 300826704584111725966927545), (Int.negOfNat 614864612383706469787154), (Int.ofNat 2357680364112351908155322), (Int.ofNat 37117678271431181306221), (Int.negOfNat 12200729925114989650977), (Int.negOfNat 284248119243235124314), (Int.ofNat 45601931404206458928), (Int.ofNat 1056550590539893940), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(12061403776341042970979621752834763/14073748835532800000000000000000000), (2010604729054337767229582074048209/28147497671065600000000000000000000), (11292660027506953127530775973/5497558138880000000000000000000), (1532886789281244387440576500001/3518437208883200000000000000000000), (-3195097209828049073638327293673/28147497671065600000000000000000000), (-830302073171412643685712122569/28147497671065600000000000000000000), (36993048391433815409376528913/14073748835532800000000000000000000), (348372211681773773481920591/439804651110400000000000000000000), (-23437021112515864922904539/1125899906842624000000000000000000), (-60165340916822345193385509/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial145.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial145.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial145.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 28402993423984160458188594828416110), (Int.ofNat 2243292678098546205929723535624550), (Int.ofNat 18653556986130548282612823739497), (Int.negOfNat 24762925101000640353565088309670), (Int.negOfNat 2593888142407973285759753536061), (Int.ofNat 1125771512936553722879477412812), (Int.ofNat 150558283373517559030549780626), (Int.negOfNat 18984312622719569810382902274), (Int.negOfNat 3222592497328894266902804625), (Int.ofNat 128651075893795716283117895), (Int.ofNat 33251269624677797251056446), (Int.negOfNat 328847266141598778005222), (Int.negOfNat 209599653765913019104129), (Int.negOfNat 860384493914931699373), (Int.ofNat 908941438531362871236), (Int.ofNat 11367958897060880572), (Int.negOfNat 3544046709326582760), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(2840299342398416045818859482841611/2814749767106560000000000000000000), (44865853561970924118594470712491/562949953421312000000000000000000), (18653556986130548282612823739497/28147497671065600000000000000000000), (-2476292510100064035356508830967/2814749767106560000000000000000000), (-2593888142407973285759753536061/28147497671065600000000000000000000), (281442878234138430719869353203/7036874417766400000000000000000000), (75279141686758779515274890313/14073748835532800000000000000000000), (-9492156311359784905191451137/14073748835532800000000000000000000), (-25780739978631154135222437/225179981368524800000000000000000), (25730215178759143256623579/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial145.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial145.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial145.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 32767091234582327969437950042433593), (Int.ofNat 2045369252050258022346005308064073), (Int.negOfNat 83561285299602385631425412148178), (Int.ofNat 8365356531266932306652817232273), (Int.ofNat 9698207219323274650317528048693), (Int.ofNat 391251421951016219936579331927), (Int.negOfNat 294716528163201029874000404511), (Int.negOfNat 26841203889102128753589405998), (Int.ofNat 3122926033281854950859983043), (Int.ofNat 400016745735785144888857110), (Int.negOfNat 17196456789205158309939960), (Int.negOfNat 3156890941856940649166447), (Int.ofNat 52838040410952594355610), (Int.ofNat 16272183052960362365382), (Int.negOfNat 61494788851987239691), (Int.negOfNat 62013241236957190641), (Int.negOfNat 202978320719663726), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(32767091234582327969437950042433593/28147497671065600000000000000000000), (2045369252050258022346005308064073/28147497671065600000000000000000000), (-41780642649801192815712706074089/14073748835532800000000000000000000), (8365356531266932306652817232273/28147497671065600000000000000000000), (9698207219323274650317528048693/28147497671065600000000000000000000), (391251421951016219936579331927/28147497671065600000000000000000000), (-294716528163201029874000404511/28147497671065600000000000000000000), (-13420601944551064376794702999/14073748835532800000000000000000000), (3122926033281854950859983043/28147497671065600000000000000000000), (40001674573578514488885711/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial145.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial145.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial145.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 36736881828680874137785317998618873), (Int.ofNat 2088538753747601003477893435032640), (Int.ofNat 149077338933199109522347387128945), (Int.ofNat 46775198236024251277283391306712), (Int.negOfNat 6829311426435479519949941919267), (Int.negOfNat 3416050799053848760426209367300), (Int.negOfNat 149869260060714997494078852017), (Int.ofNat 50551472837424030085664117256), (Int.ofNat 4088670335065318170594240385), (Int.negOfNat 381998983909211478698929493), (Int.negOfNat 41984538970494663502652560), (Int.ofNat 1787457659985285738425851), (Int.ofNat 259932908658117185883866), (Int.negOfNat 5556351161133283907198), (Int.negOfNat 1118311532752509934166), (Int.ofNat 11069192191280873953), (Int.ofNat 3983102134147207439), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(36736881828680874137785317998618873/28147497671065600000000000000000000), (6526683605461253135868416984477/87960930222080000000000000000000), (29815467786639821904469477425789/5629499534213120000000000000000000), (5846899779503031409660423913339/3518437208883200000000000000000000), (-6829311426435479519949941919267/28147497671065600000000000000000000), (-34160507990538487604262093673/281474976710656000000000000000000), (-149869260060714997494078852017/28147497671065600000000000000000000), (6318934104678003760708014657/3518437208883200000000000000000000), (817734067013063634118848077/5629499534213120000000000000000000), (-381998983909211478698929493/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial145.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial145.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial145.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 41663579411409748775169742347832061), (Int.ofNat 2751318435167958727072714966420641), (Int.negOfNat 4307443895404095211705381802287), (Int.negOfNat 135440835993282020128952831356624), (Int.negOfNat 33247425005814014534880113481777), (Int.negOfNat 168814880231427045486196804144), (Int.ofNat 657786149385681520364730647322), (Int.ofNat 35620457615803132476056248607), (Int.negOfNat 6349384653093033713556258779), (Int.negOfNat 497516833982011377910273903), (Int.ofNat 38156885731837720872968836), (Int.ofNat 3743610536312813933940535), (Int.negOfNat 157959532816910211413606), (Int.negOfNat 18774964759478677897640), (Int.ofNat 475622229706982526854), (Int.ofNat 69180638900074078566), (Int.negOfNat 1086582051443563774), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(41663579411409748775169742347832061/28147497671065600000000000000000000), (2751318435167958727072714966420641/28147497671065600000000000000000000), (-4307443895404095211705381802287/28147497671065600000000000000000000), (-8465052249580126258059551959789/1759218604441600000000000000000000), (-33247425005814014534880113481777/28147497671065600000000000000000000), (-10550930014464190342887300259/1759218604441600000000000000000000), (328893074692840760182365323661/14073748835532800000000000000000000), (35620457615803132476056248607/28147497671065600000000000000000000), (-6349384653093033713556258779/28147497671065600000000000000000000), (-497516833982011377910273903/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial145.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial145.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial145.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 45572922451748633728723860762333635), (Int.ofNat 166213414526532253518942864852503), (Int.negOfNat 1459729335117260580403343614183112), (Int.negOfNat 296310933243641857272855248977515), (Int.ofNat 6032762959092534492170801330518), (Int.ofNat 7266094007840536265128238447125), (Int.ofNat 281626977813664506893390558570), (Int.negOfNat 86967888634243297363935257288), (Int.negOfNat 5376784293037419169972392398), (Int.ofNat 646250631621409566198513784), (Int.ofNat 49093544225244172164078169), (Int.negOfNat 3306934196414290887680808), (Int.negOfNat 287725812166808801432827), (Int.ofNat 12402096227798488177861), (Int.ofNat 1201385201059057097757), (Int.negOfNat 34760918841684178963), (Int.negOfNat 3992304101580089618), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(9114584490349726745744772152466727/5629499534213120000000000000000000), (166213414526532253518942864852503/28147497671065600000000000000000000), (-182466166889657572550417951772889/3518437208883200000000000000000000), (-59262186648728371454571049795503/5629499534213120000000000000000000), (3016381479546267246085400665259/14073748835532800000000000000000000), (58128752062724290121025907577/225179981368524800000000000000000), (28162697781366450689339055857/2814749767106560000000000000000000), (-10870986079280412170491907161/3518437208883200000000000000000000), (-2688392146518709584986196199/14073748835532800000000000000000000), (80781328952676195774814223/3518437208883200000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial145.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial145.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial145.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 38030872790903441113894086706450739), (Int.negOfNat 8442797463526995146974653275801840), (Int.negOfNat 2508574943871514336726709304537559), (Int.ofNat 33378703270858294446522387447354), (Int.ofNat 68313314832724679118652453733936), (Int.ofNat 2508476589709335210077457182282), (Int.negOfNat 1001264896587330871252636205474), (Int.negOfNat 55747967908537310826661463857), (Int.ofNat 9149955534464536872516448748), (Int.ofNat 596838576753331604141667723), (Int.negOfNat 57060169764586211970496807), (Int.negOfNat 4052212511086231270463988), (Int.ofNat 257919670090367785801660), (Int.ofNat 19341977711338799955750), (Int.negOfNat 882166035587154016570), (Int.negOfNat 69396425967187514477), (Int.ofNat 2376142423606791274), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(38030872790903441113894086706450739/28147497671065600000000000000000000), (-105534968294087439337183165947523/351843720888320000000000000000000), (-2508574943871514336726709304537559/28147497671065600000000000000000000), (16689351635429147223261193723677/14073748835532800000000000000000000), (4269582177045292444915778358371/1759218604441600000000000000000000), (1254238294854667605038728591141/14073748835532800000000000000000000), (-500632448293665435626318102737/14073748835532800000000000000000000), (-55747967908537310826661463857/28147497671065600000000000000000000), (2287488883616134218129112187/7036874417766400000000000000000000), (596838576753331604141667723/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial145.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial145.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial145.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 12482657749219213584300322387117242), (Int.negOfNat 15896652417533766893524996564950722), (Int.negOfNat 727475603553131954437644117967178), (Int.ofNat 507394697791588559920529196534522), (Int.ofNat 29467792875258533397814478668474), (Int.negOfNat 9435645664123796138923772273042), (Int.negOfNat 588826797416711810349215156473), (Int.ofNat 108599419584481750957782067646), (Int.ofNat 6896032417583388230373069871), (Int.negOfNat 834788466722762879663622871), (Int.negOfNat 53013250415816490434979357), (Int.ofNat 4550723071927193065542730), (Int.ofNat 286974852326567337871275), (Int.negOfNat 18446981042712804293457), (Int.negOfNat 1151178677702416226193), (Int.ofNat 56834623073466475233), (Int.ofNat 4001506069012971797), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(6241328874609606792150161193558621/14073748835532800000000000000000000), (-7948326208766883446762498282475361/14073748835532800000000000000000000), (-363737801776565977218822058983589/14073748835532800000000000000000000), (253697348895794279960264598267261/14073748835532800000000000000000000), (14733896437629266698907239334237/14073748835532800000000000000000000), (-4717822832061898069461886136521/14073748835532800000000000000000000), (-588826797416711810349215156473/28147497671065600000000000000000000), (54299709792240875478891033823/14073748835532800000000000000000000), (6896032417583388230373069871/28147497671065600000000000000000000), (-834788466722762879663622871/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial145.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial145.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial145.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 18014338067788746012541180940917132), (Int.negOfNat 12589178974007382728152694901814954), (Int.ofNat 2208972833575736098286826031960354), (Int.ofNat 339588594972946103335581384832983), (Int.negOfNat 65944402418263750804282463282006), (Int.negOfNat 6243629428653555663833053514669), (Int.ofNat 1044303455463697130343423160949), (Int.ofNat 76715888947537101635333165092), (Int.negOfNat 10316423453040138367912866047), (Int.negOfNat 650931429270615272843122116), (Int.ofNat 69162918772931081455589882), (Int.ofNat 3947701779501154038422577), (Int.negOfNat 334295419480104963430351), (Int.negOfNat 17717667398745067905896), (Int.ofNat 1218551250558582472380), (Int.ofNat 59892437570114953205), (Int.negOfNat 3668770118247646167), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-4503584516947186503135295235229283/7036874417766400000000000000000000), (-6294589487003691364076347450907477/14073748835532800000000000000000000), (1104486416787868049143413015980177/14073748835532800000000000000000000), (339588594972946103335581384832983/28147497671065600000000000000000000), (-32972201209131875402141231641003/14073748835532800000000000000000000), (-6243629428653555663833053514669/28147497671065600000000000000000000), (1044303455463697130343423160949/28147497671065600000000000000000000), (19178972236884275408833291273/7036874417766400000000000000000000), (-10316423453040138367912866047/28147497671065600000000000000000000), (-162732857317653818210780529/7036874417766400000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial145.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial145.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial145.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial145.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial145.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial145.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial145.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial145.reflect := by
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

end Bin145
end
end ErdosOverlap.OuterNumerics
