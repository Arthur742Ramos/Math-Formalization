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

/-! # Exact integer weighted outer models for source bin 161

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin161

def weightDenominator : ℤ := (Int.ofNat 5000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 190344103728871670)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 888067470666246400)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 643153140014628300)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 231629392267245750)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 431969243664328550)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 350039039799478900)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 249941233747559350)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 185200687663932170)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 105078438972447780)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 60465339356573090)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial161.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial161.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 4606166970555391000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1796019136520478000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 587740325139257100)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 494919328457946750)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 258129642043198430)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 96773526745333025)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 6931411428375099)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 14301278309488063)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 10550567176671477)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial161.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial161.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4606166970555391000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1796019136520478000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 587740325139257100)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 494919328457946750)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 258129642043198430)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 96773526745333025)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 6931411428375099)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 14301278309488063)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 10550567176671477)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial161.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial161.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial161.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 1973690104060285055094820994702845), (Int.ofNat 2019945253292104404919552708004239), (Int.ofNat 194799498611720000516252883029138), (Int.negOfNat 49815920583118599948773028068198), (Int.negOfNat 6084444470225076899741390130999), (Int.ofNat 885182591915468969358820878755), (Int.ofNat 104217490714813700109940449280), (Int.negOfNat 10434913304151703034375010180), (Int.negOfNat 1100347068506186141949824107), (Int.ofNat 84755591731227406706306119), (Int.ofNat 7829810824612830945282550), (Int.negOfNat 495774027491254421987965), (Int.negOfNat 40029995955359371047044), (Int.ofNat 2168097247821168431824), (Int.ofNat 154228193448698508388), (Int.negOfNat 7228295851858495825), (Int.negOfNat 485009817124830155), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-394738020812057011018964198940569/1125899906842624000000000000000000), (2019945253292104404919552708004239/5629499534213120000000000000000000), (97399749305860000258126441514569/2814749767106560000000000000000000), (-24907960291559299974386514034099/2814749767106560000000000000000000), (-6084444470225076899741390130999/5629499534213120000000000000000000), (177036518383093793871764175751/1125899906842624000000000000000000), (2544372331904631350340343/137438953472000000000000000000), (-521745665207585151718750509/281474976710656000000000000000000), (-1100347068506186141949824107/5629499534213120000000000000000000), (84755591731227406706306119/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial161.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial161.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial161.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial161 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 2382948578673936870358448886389767), (Int.ofNat 2091901675135212916375626977030623), (Int.negOfNat 162815487293428776719485758902277), (Int.negOfNat 53673551807656189750395562478146), (Int.ofNat 5288147665049103294209130857003), (Int.ofNat 982440156060090354187955187418), (Int.negOfNat 90970323345463134995986828422), (Int.negOfNat 11659787135473987285770789174), (Int.ofNat 974789004578197420364685706), (Int.ofNat 93623043411911350461168636), (Int.negOfNat 7098975515155587731680452), (Int.negOfNat 536887529459183235526153), (Int.ofNat 37182504177597190543826), (Int.ofNat 2297579709430057012723), (Int.negOfNat 146379744662649949898), (Int.negOfNat 7523580001562405332), (Int.ofNat 471832267452285439), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(2382948578673936870358448886389767/5629499534213120000000000000000000), (2091901675135212916375626977030623/5629499534213120000000000000000000), (-162815487293428776719485758902277/5629499534213120000000000000000000), (-26836775903828094875197781239073/2814749767106560000000000000000000), (5288147665049103294209130857003/5629499534213120000000000000000000), (491220078030045177093977593709/2814749767106560000000000000000000), (-45485161672731567497993414211/2814749767106560000000000000000000), (-5829893567736993642885394587/2814749767106560000000000000000000), (487394502289098710182342853/2814749767106560000000000000000000), (23405760852977837615292159/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial161.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial161.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial161.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial161 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 5595124740093066498379972773750300), (Int.ofNat 1022855670260434533259194156956921), (Int.negOfNat 306930138396862433438421411645839), (Int.ofNat 8967664484423454973880420290093), (Int.ofNat 7746138385316663281593275570518), (Int.negOfNat 531939449762199583063696443935), (Int.negOfNat 111330425651625684499765526252), (Int.ofNat 8889686834078186086872966768), (Int.ofNat 1029929903788058090580319512), (Int.negOfNat 85793739928248729529459118), (Int.negOfNat 6643380048563480178877190), (Int.ofNat 553964034650558828800094), (Int.ofNat 31518237069118859789893), (Int.negOfNat 2575256544778304663875), (Int.negOfNat 114241715024894477165), (Int.ofNat 9046986149664153946), (Int.ofNat 314164366231782362), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(55951247400930664983799727737503/56294995342131200000000000000000), (1022855670260434533259194156956921/5629499534213120000000000000000000), (-306930138396862433438421411645839/5629499534213120000000000000000000), (8967664484423454973880420290093/5629499534213120000000000000000000), (3873069192658331640796637785259/2814749767106560000000000000000000), (-106387889952439916612739288787/1125899906842624000000000000000000), (-27832606412906421124941381563/1407374883553280000000000000000000), (555605427129886630429560423/351843720888320000000000000000000), (128741237973507261322539939/703687441776640000000000000000000), (-42896869964124364764729559/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial161.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial161.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial161.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial161 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 6585999901144355275242827053928998), (Int.ofNat 91505332691620547686121978361489), (Int.negOfNat 129126369748906292071968197279221), (Int.ofNat 38133043162132175402947649951201), (Int.negOfNat 1019294722154345352555308810880), (Int.negOfNat 867655630734865538957511893339), (Int.ofNat 57927383067628389419591723174), (Int.ofNat 10043525635596922085531671607), (Int.negOfNat 849170592065315322125815220), (Int.negOfNat 74900804357019100181166497), (Int.ofNat 7109217747307989295227895), (Int.ofNat 395426934799116528666753), (Int.negOfNat 40061280647089903590489), (Int.negOfNat 1563059027108455530832), (Int.ofNat 164243263867853433600), (Int.ofNat 4665502952812198086), (Int.negOfNat 503483968982299870), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(3292999950572177637621413526964499/2814749767106560000000000000000000), (91505332691620547686121978361489/5629499534213120000000000000000000), (-129126369748906292071968197279221/5629499534213120000000000000000000), (38133043162132175402947649951201/5629499534213120000000000000000000), (-1592648003366164613367670017/8796093022208000000000000000000), (-867655630734865538957511893339/5629499534213120000000000000000000), (28963691533814194709795861587/2814749767106560000000000000000000), (10043525635596922085531671607/5629499534213120000000000000000000), (-42458529603265766106290761/281474976710656000000000000000000), (-74900804357019100181166497/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial161.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial161.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial161.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial161 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 6518240839599476597797490998398499), (Int.negOfNat 54814269765799314647889335114161), (Int.ofNat 24671470574510121712699821878163), (Int.ofNat 8361894586707112493884203590042), (Int.negOfNat 4554312083427239624337918728553), (Int.ofNat 204323612216805207007717886341), (Int.ofNat 80251127229123964157161732691), (Int.negOfNat 6526238226275072720557027457), (Int.negOfNat 743660995310232118599727041), (Int.ofNat 77160865272463003637189972), (Int.ofNat 4471329129592607164997013), (Int.negOfNat 546181694264144865446208), (Int.negOfNat 19149047430192747828022), (Int.ofNat 2664210654040443949232), (Int.ofNat 61826640184658183002), (Int.negOfNat 9712741651970004030), (Int.negOfNat 132768348162063092), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(6518240839599476597797490998398499/5629499534213120000000000000000000), (-54814269765799314647889335114161/5629499534213120000000000000000000), (24671470574510121712699821878163/5629499534213120000000000000000000), (4180947293353556246942101795021/2814749767106560000000000000000000), (-4554312083427239624337918728553/5629499534213120000000000000000000), (204323612216805207007717886341/5629499534213120000000000000000000), (80251127229123964157161732691/5629499534213120000000000000000000), (-6526238226275072720557027457/5629499534213120000000000000000000), (-743660995310232118599727041/5629499534213120000000000000000000), (19290216318115750909297493/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial161.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial161.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial161.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial161 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 6512015948256822283066348412906821), (Int.ofNat 26739398307544068031916214750380), (Int.negOfNat 4181932465090777722376063169458), (Int.negOfNat 11587734356679359121904202802560), (Int.negOfNat 9534158418796047537257965385), (Int.ofNat 460406252078588588685390109745), (Int.negOfNat 36130119472162544155070139214), (Int.negOfNat 6086779262563944234492315066), (Int.ofNat 690964421540131142382121200), (Int.ofNat 44025105436498178595359180), (Int.negOfNat 6450713011869014434282006), (Int.negOfNat 204964527953380672238647), (Int.ofNat 38375352965617560985905), (Int.ofNat 662239752197015090814), (Int.negOfNat 162193257510838832456), (Int.negOfNat 1475483881815415120), (Int.ofNat 535135670512314301), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(6512015948256822283066348412906821/5629499534213120000000000000000000), (1336969915377203401595810737519/281474976710656000000000000000000), (-2090966232545388861188031584729/2814749767106560000000000000000000), (-18105834932311498627975316879/8796093022208000000000000000000), (-1906831683759209507451593077/1125899906842624000000000000000000), (92081250415717717737078021949/1125899906842624000000000000000000), (-18065059736081272077535069607/2814749767106560000000000000000000), (-3043389631281972117246157533/2814749767106560000000000000000000), (1727411053850327855955303/14073748835532800000000000000000), (2201255271824908929767959/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial161.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial161.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial161.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial161 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 6467746720686697904860595543653152), (Int.negOfNat 101402992056416392426336828257175), (Int.negOfNat 48502572016343744207576208814643), (Int.negOfNat 1065631236388090172666712391495), (Int.ofNat 1583395888704842311772063957525), (Int.negOfNat 140274615132007052407383730732), (Int.negOfNat 36786227207084502134947595755), (Int.ofNat 5007955266333771063202843468), (Int.ofNat 352206110476005319786722761), (Int.negOfNat 65098285057959602502057862), (Int.negOfNat 1799885607106595424967831), (Int.ofNat 486293436474046093838569), (Int.ofNat 5079584262867265741607), (Int.negOfNat 2445400449590748069585), (Int.negOfNat 4443412068579149659), (Int.ofNat 9148089232791049360), (Int.negOfNat 48627669907656178), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(202117085021459309526893610739161/175921860444160000000000000000000), (-4056119682256655697053473130287/225179981368524800000000000000000), (-48502572016343744207576208814643/5629499534213120000000000000000000), (-213126247277618034533342478299/1125899906842624000000000000000000), (63335835548193692470882558301/225179981368524800000000000000000), (-35068653783001763101845932683/1407374883553280000000000000000000), (-7357245441416900426989519151/1125899906842624000000000000000000), (1251988816583442765800710867/1407374883553280000000000000000000), (352206110476005319786722761/5629499534213120000000000000000000), (-32549142528979801251028931/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial161.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial161.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial161.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial161 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 6081593633162530764876142142389712), (Int.negOfNat 273366616318233985320990688878875), (Int.negOfNat 33256077566468935169387819454362), (Int.ofNat 3183158603488386494819255736599), (Int.negOfNat 496183015162745250344153088439), (Int.negOfNat 134895081442485738111510745544), (Int.ofNat 29949877927065280120531184428), (Int.ofNat 1981169455661079462659441448), (Int.negOfNat 555982958518399497645464403), (Int.negOfNat 10750398148100234532104121), (Int.ofNat 5361828596355401483744175), (Int.ofNat 5931466740405011059990), (Int.negOfNat 32741576724849880808615), (Int.ofNat 247150811827390251377), (Int.ofNat 140141456481158290674), (Int.negOfNat 1747955184239291016), (Int.negOfNat 506322032685755642), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(380099602072658172804758883899357/351843720888320000000000000000000), (-2186932930545871882567925511031/45035996273704960000000000000000), (-16628038783234467584693909727181/2814749767106560000000000000000000), (3183158603488386494819255736599/5629499534213120000000000000000000), (-496183015162745250344153088439/5629499534213120000000000000000000), (-16861885180310717263938843193/703687441776640000000000000000000), (7487469481766320030132796107/1407374883553280000000000000000000), (247646181957634932832430181/703687441776640000000000000000000), (-555982958518399497645464403/5629499534213120000000000000000000), (-10750398148100234532104121/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial161.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial161.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial161.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial161 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 5417073707069702307878438245434697), (Int.negOfNat 388791897979206412587425334054316), (Int.negOfNat 29323855496949929546844330392771), (Int.negOfNat 1255696772456885130573571306241), (Int.negOfNat 91069106730224691225567485036), (Int.ofNat 160478951417396387759631073128), (Int.ofNat 4513648301237200204329282176), (Int.negOfNat 4030101461541837936549941050), (Int.negOfNat 1411517453888896230606071), (Int.ofNat 50859020087238101508205727), (Int.negOfNat 701701451146780433587469), (Int.negOfNat 384368064146216465609380), (Int.ofNat 7983533604803428886071), (Int.ofNat 1956259479847342848361), (Int.negOfNat 47732951542601287146), (Int.negOfNat 7332708849818787588), (Int.ofNat 190659482974145312), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(5417073707069702307878438245434697/5629499534213120000000000000000000), (-97197974494801603146856333513579/1407374883553280000000000000000000), (-29323855496949929546844330392771/5629499534213120000000000000000000), (-1255696772456885130573571306241/5629499534213120000000000000000000), (-22767276682556172806391871259/1407374883553280000000000000000000), (20059868927174548469953884141/703687441776640000000000000000000), (35262877353415626596322517/43980465111040000000000000000000), (-80602029230836758730998821/112589990684262400000000000000000), (-1411517453888896230606071/5629499534213120000000000000000000), (50859020087238101508205727/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial161.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial161.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial161.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial161 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 4515624376654518471841250919717175), (Int.negOfNat 512062336691306978722892910463715), (Int.negOfNat 27616581038165273970131453706998), (Int.ofNat 3145534559653668258724465517495), (Int.ofNat 835587719453463101182763652197), (Int.negOfNat 37624748351914190628657750724), (Int.negOfNat 25080031399906285064599065597), (Int.ofNat 953787366035271811893408444), (Int.ofNat 409934013680510758912137063), (Int.negOfNat 16279705067977129195564664), (Int.negOfNat 3890812608449371281669785), (Int.ofNat 160762593464733834240311), (Int.ofNat 23849369382005747672613), (Int.negOfNat 1005051044773178575163), (Int.negOfNat 102625648944043609279), (Int.ofNat 4414619252841863704), (Int.ofNat 406492488325952416), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(180624975066180738873650036788687/225179981368524800000000000000000), (-102412467338261395744578582092743/1125899906842624000000000000000000), (-13808290519082636985065726853499/2814749767106560000000000000000000), (629106911930733651744893103499/1125899906842624000000000000000000), (835587719453463101182763652197/5629499534213120000000000000000000), (-9406187087978547657164437681/1407374883553280000000000000000000), (-25080031399906285064599065597/5629499534213120000000000000000000), (238446841508817952973352111/1407374883553280000000000000000000), (409934013680510758912137063/5629499534213120000000000000000000), (-2034963133497141149445583/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial161.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial161.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial161.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial161 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 3416973070815279069580993465431329), (Int.negOfNat 565076812352115808339531363520790), (Int.ofNat 3543196398817088790469370106804), (Int.ofNat 5442996987289594255968610016138), (Int.negOfNat 427853504123328484193173650551), (Int.negOfNat 132261296139414037440411908332), (Int.ofNat 13673270705555262832559333018), (Int.ofNat 2739791448823400417491256988), (Int.negOfNat 239030913612689915630609092), (Int.negOfNat 33061903010210303984399936), (Int.ofNat 2541804034981442072204038), (Int.ofNat 247846655027347206443467), (Int.negOfNat 17711122563829945387691), (Int.negOfNat 1259098572710906217622), (Int.ofNat 86152549525927017084), (Int.ofNat 4622935319740905104), (Int.negOfNat 282776523860732833), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(3416973070815279069580993465431329/5629499534213120000000000000000000), (-56507681235211580833953136352079/562949953421312000000000000000000), (885799099704272197617342526701/1407374883553280000000000000000000), (2721498493644797127984305008069/2814749767106560000000000000000000), (-427853504123328484193173650551/5629499534213120000000000000000000), (-33065324034853509360102977083/1407374883553280000000000000000000), (6836635352777631416279666509/2814749767106560000000000000000000), (684947862205850104372814247/1407374883553280000000000000000000), (-59757728403172478907652273/1407374883553280000000000000000000), (-516592234534535999756249/87960930222080000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial161.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial161.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial161.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial161 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 2334608882161465175662226869176562), (Int.negOfNat 506313212174766574614325881078989), (Int.ofNat 19928720905159419612583457395156), (Int.negOfNat 107141943351848579737227699479), (Int.negOfNat 521924666981763056623238049404), (Int.ofNat 113936248987836102209039107083), (Int.ofNat 13997173118898293935307981873), (Int.negOfNat 2640603269006707086659719995), (Int.negOfNat 222380340489356229876507623), (Int.ofNat 33210813132007604388319404), (Int.ofNat 2081477690974820399378577), (Int.negOfNat 267711694018630411671312), (Int.negOfNat 12646379420426470569588), (Int.ofNat 1487862569889395050526), (Int.ofNat 53876598143118755132), (Int.negOfNat 6034328389687966074), (Int.negOfNat 225096470256233146), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(1167304441080732587831113434588281/2814749767106560000000000000000000), (-506313212174766574614325881078989/5629499534213120000000000000000000), (4982180226289854903145864348789/1407374883553280000000000000000000), (-107141943351848579737227699479/5629499534213120000000000000000000), (-130481166745440764155809512351/1407374883553280000000000000000000), (113936248987836102209039107083/5629499534213120000000000000000000), (13997173118898293935307981873/5629499534213120000000000000000000), (-528120653801341417331943999/1125899906842624000000000000000000), (-222380340489356229876507623/5629499534213120000000000000000000), (8302703283001901097079851/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial161.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial161.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial161.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial161 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 1396654811843423958214426900506101), (Int.negOfNat 434110039323286585157511860324871), (Int.ofNat 17229780762261665613626788704759), (Int.ofNat 835459462263045733321308014198), (Int.ofNat 618386058288439474351949470695), (Int.ofNat 35531617512813421550846285867), (Int.negOfNat 22920138802282714067589499921), (Int.negOfNat 975540546157594220344731339), (Int.ofNat 362916827653243081123361842), (Int.ofNat 12108885225162047695888773), (Int.negOfNat 3495515930111501337939449), (Int.negOfNat 89730464456688006501373), (Int.ofNat 22655655513418068155977), (Int.ofNat 443514165339897233570), (Int.negOfNat 104892006538662843230), (Int.negOfNat 1524559097654086710), (Int.ofNat 314428225390747264), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(1396654811843423958214426900506101/5629499534213120000000000000000000), (-434110039323286585157511860324871/5629499534213120000000000000000000), (17229780762261665613626788704759/5629499534213120000000000000000000), (417729731131522866660654007099/2814749767106560000000000000000000), (123677211657687894870389894139/1125899906842624000000000000000000), (35531617512813421550846285867/5629499534213120000000000000000000), (-22920138802282714067589499921/5629499534213120000000000000000000), (-975540546157594220344731339/5629499534213120000000000000000000), (181458413826621540561680921/2814749767106560000000000000000000), (12108885225162047695888773/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial161.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial161.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial161.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial161 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 613572400521631792895479167026016), (Int.negOfNat 336991042206060981999280879451502), (Int.ofNat 34434847476280366970434737932292), (Int.ofNat 3650852868682516737114725559756), (Int.negOfNat 267213656370853082982030698688), (Int.negOfNat 162964598946708145484076555019), (Int.ofNat 490037956695449139820426596), (Int.ofNat 3321648105682186577465045774), (Int.ofNat 10667828783355520437740124), (Int.negOfNat 39289548661501369493705238), (Int.negOfNat 120068185110024949462714), (Int.ofNat 302624247011625189516706), (Int.ofNat 539315194833913942629), (Int.negOfNat 1628093879973219702913), (Int.negOfNat 734698982903446565), (Int.ofNat 6465831873755949598), (Int.ofNat 43700452186513876), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(19174137516300993527983723969563/175921860444160000000000000000000), (-168495521103030490999640439725751/2814749767106560000000000000000000), (8608711869070091742608684483073/1407374883553280000000000000000000), (912713217170629184278681389939/1407374883553280000000000000000000), (-4175213380794579421594229667/87960930222080000000000000000000), (-162964598946708145484076555019/5629499534213120000000000000000000), (122509489173862284955106649/1407374883553280000000000000000000), (1660824052841093288732522887/2814749767106560000000000000000000), (2666957195838880109435031/1407374883553280000000000000000000), (-19644774330750684746852619/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial161.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial161.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial161.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial161 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 97485877287266053156230047992635), (Int.negOfNat 175524114390809523738795725057860), (Int.ofNat 39084416378749382609534996981387), (Int.negOfNat 3248481499410400631223577244766), (Int.negOfNat 1073205160278403445552353401107), (Int.ofNat 55022245991616641923308540555), (Int.ofNat 25545565467380001306453702520), (Int.negOfNat 838042043143674218318728414), (Int.negOfNat 376564941609246760748073496), (Int.ofNat 9101291267605110689194118), (Int.ofNat 3513337502953082296335242), (Int.negOfNat 69010079398154876309247), (Int.negOfNat 22287413290084719667460), (Int.ofNat 377980342350175773729), (Int.ofNat 101588139473447698662), (Int.negOfNat 1663897789253015044), (Int.negOfNat 346079926920761695), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(19497175457453210631246009598527/1125899906842624000000000000000000), (-8776205719540476186939786252893/281474976710656000000000000000000), (39084416378749382609534996981387/5629499534213120000000000000000000), (-1624240749705200315611788622383/2814749767106560000000000000000000), (-1073205160278403445552353401107/5629499534213120000000000000000000), (11004449198323328384661708111/1125899906842624000000000000000000), (638639136684500032661342563/140737488355328000000000000000000), (-419021021571837109159364207/2814749767106560000000000000000000), (-47070617701155845093509187/703687441776640000000000000000000), (4550645633802555344597059/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial161.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial161.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial161.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial161 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 137183832895313210097352577098291), (Int.negOfNat 83927645238819764681519880662155), (Int.ofNat 3210409440854122215930396690278), (Int.negOfNat 6592400238085443816820394365075), (Int.ofNat 431759071509251289979933763822), (Int.ofNat 165073453720656044827530501160), (Int.negOfNat 12625001437300947571233134348), (Int.negOfNat 3027125632046592571309336402), (Int.ofNat 184854788272737837558983881), (Int.ofNat 34849797784776858810764947), (Int.negOfNat 1699826750330342817213446), (Int.negOfNat 264952931642270698506845), (Int.ofNat 10717581837064292069410), (Int.ofNat 1415707576457578069274), (Int.negOfNat 48932983262504998592), (Int.negOfNat 5631656579060817559), (Int.ofNat 148246133059876871), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-137183832895313210097352577098291/5629499534213120000000000000000000), (-16785529047763952936303976132431/1125899906842624000000000000000000), (1605204720427061107965198345139/2814749767106560000000000000000000), (-263696009523417752672815774603/225179981368524800000000000000000), (215879535754625644989966881911/2814749767106560000000000000000000), (4126836343016401120688262529/140737488355328000000000000000000), (-3156250359325236892808283587/1407374883553280000000000000000000), (-1513562816023296285654668201/2814749767106560000000000000000000), (184854788272737837558983881/5629499534213120000000000000000000), (34849797784776858810764947/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial161.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial161.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial161.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial161 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 333878726826581491923834200709297), (Int.negOfNat 126694566734946778651804879038740), (Int.negOfNat 17374394397859353125707860607603), (Int.ofNat 232307013505655587542029050486), (Int.ofNat 792724837374309156703172106968), (Int.negOfNat 107687138439834956121012853067), (Int.negOfNat 19615938525104098859993547292), (Int.ofNat 2315790939590658109253366378), (Int.ofNat 286353129974555631961647059), (Int.negOfNat 26967594840090436730495653), (Int.negOfNat 2659383369106425460883254), (Int.ofNat 203914874710344099871415), (Int.ofNat 16891045574982861698490), (Int.negOfNat 1081261216146215765586), (Int.negOfNat 77487779675395119028), (Int.ofNat 4323426710643784881), (Int.ofNat 246250382560958469), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-333878726826581491923834200709297/5629499534213120000000000000000000), (-6334728336747338932590243951937/281474976710656000000000000000000), (-17374394397859353125707860607603/5629499534213120000000000000000000), (116153506752827793771014525243/2814749767106560000000000000000000), (99090604671788644587896513371/703687441776640000000000000000000), (-107687138439834956121012853067/5629499534213120000000000000000000), (-4903984631276024714998386823/1407374883553280000000000000000000), (1157895469795329054626683189/2814749767106560000000000000000000), (286353129974555631961647059/5629499534213120000000000000000000), (-26967594840090436730495653/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial161.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial161.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial161.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial161 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 646571119023303036771935511950004), (Int.negOfNat 179160899365605113816693474094985), (Int.negOfNat 8356812701349482799250188716481), (Int.ofNat 762382315678596185051529104775), (Int.negOfNat 626149260852085084027037917050), (Int.negOfNat 88756620845233004600831587484), (Int.ofNat 21548094707514706359278576600), (Int.ofNat 1821324305569629630107100966), (Int.negOfNat 330043239863723188843749744), (Int.negOfNat 21243847518746747549126922), (Int.ofNat 3077294781616030689896778), (Int.ofNat 163905105007518104285453), (Int.negOfNat 19361780470319041983600), (Int.negOfNat 891887663776942563071), (Int.ofNat 87549763688699359558), (Int.ofNat 3703429048540458356), (Int.negOfNat 290277946126366005), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-161642779755825759192983877987501/1407374883553280000000000000000000), (-35832179873121022763338694818997/1125899906842624000000000000000000), (-8356812701349482799250188716481/5629499534213120000000000000000000), (30495292627143847402061164191/225179981368524800000000000000000), (-12522985217041701680540758341/112589990684262400000000000000000), (-22189155211308251150207896871/1407374883553280000000000000000000), (107740473537573531796392883/28147497671065600000000000000000), (910662152784814815053550483/2814749767106560000000000000000000), (-20627702491482699302734359/351843720888320000000000000000000), (-10621923759373373774563461/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial161.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial161.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial161.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial161 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 1043559468671581019833967978486261), (Int.negOfNat 225993501600092454567283304895428), (Int.negOfNat 20165837080390489313883457267070), (Int.negOfNat 3983265203477119725066447635449), (Int.negOfNat 120562985705662135526163849307), (Int.ofNat 159627707658368615777660945870), (Int.ofNat 7301795622614909443703449364), (Int.negOfNat 3245047299965930716271195066), (Int.negOfNat 113540384425394454594945564), (Int.ofNat 38354987086032643860078202), (Int.ofNat 1107193868337526572648994), (Int.negOfNat 292666039622927651481094), (Int.negOfNat 7451530810288612566189), (Int.ofNat 1554532182785170064187), (Int.ofNat 35840136463151972805), (Int.negOfNat 6142117008449443002), (Int.negOfNat 75404931667910676), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-1043559468671581019833967978486261/5629499534213120000000000000000000), (-56498375400023113641820826223857/1407374883553280000000000000000000), (-2016583708039048931388345726707/562949953421312000000000000000000), (-3983265203477119725066447635449/5629499534213120000000000000000000), (-120562985705662135526163849307/5629499534213120000000000000000000), (15962770765836861577766094587/562949953421312000000000000000000), (1825448905653727360925862341/1407374883553280000000000000000000), (-1622523649982965358135597533/2814749767106560000000000000000000), (-28385096106348613648736391/1407374883553280000000000000000000), (19177493543016321930039101/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial161.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial161.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial161.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial161 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 1604853825680254219818196977209799), (Int.negOfNat 345621288692931877410608244786117), (Int.negOfNat 34639422571334143538900483771523), (Int.ofNat 795407525547097654763604334591), (Int.ofNat 1034853435746075321917833125977), (Int.ofNat 1172168445766718559929278101), (Int.negOfNat 25765007018959480661573794612), (Int.negOfNat 33584684233913884926738899), (Int.ofNat 396581247823535743982366058), (Int.ofNat 1078490806349402924790733), (Int.negOfNat 3766346673277008832323871), (Int.negOfNat 17122941099881746578353), (Int.ofNat 23953416193183651934363), (Int.ofNat 143834867472919468730), (Int.negOfNat 108606124752364221510), (Int.negOfNat 845351999790251110), (Int.ofNat 321929647656380436), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-1604853825680254219818196977209799/5629499534213120000000000000000000), (-345621288692931877410608244786117/5629499534213120000000000000000000), (-34639422571334143538900483771523/5629499534213120000000000000000000), (795407525547097654763604334591/5629499534213120000000000000000000), (1034853435746075321917833125977/5629499534213120000000000000000000), (1172168445766718559929278101/5629499534213120000000000000000000), (-6441251754739870165393448653/1407374883553280000000000000000000), (-33584684233913884926738899/5629499534213120000000000000000000), (198290623911767871991183029/2814749767106560000000000000000000), (1078490806349402924790733/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial161.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial161.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial161.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial161 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 2413250645383770207421442376162701), (Int.negOfNat 445997241188245788653507727786068), (Int.negOfNat 10469517898226025503664986296277), (Int.ofNat 5640469866254691954337008982524), (Int.negOfNat 108575315249681324231267330408), (Int.negOfNat 159499321633486480266017466949), (Int.ofNat 7364146786038581758273242297), (Int.ofNat 3336907019107444328738575805), (Int.negOfNat 109241059299995138556635557), (Int.negOfNat 40890948285543295399423456), (Int.ofNat 879650789323872678546983), (Int.ofNat 319139460050523803268008), (Int.negOfNat 4498966426842096308832), (Int.negOfNat 1718388423074578329194), (Int.ofNat 15543143774557176808), (Int.ofNat 6807872510755293086), (Int.negOfNat 105991086401808594), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-2413250645383770207421442376162701/5629499534213120000000000000000000), (-111499310297061447163376931946517/1407374883553280000000000000000000), (-10469517898226025503664986296277/5629499534213120000000000000000000), (1410117466563672988584252245631/1407374883553280000000000000000000), (-13571914406210165528908416301/703687441776640000000000000000000), (-159499321633486480266017466949/5629499534213120000000000000000000), (7364146786038581758273242297/5629499534213120000000000000000000), (667381403821488865747715161/1125899906842624000000000000000000), (-109241059299995138556635557/5629499534213120000000000000000000), (-1277842133923227981231983/175921860444160000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial161.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial161.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial161.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial161 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 3307989573813282294046100847051694), (Int.negOfNat 433713355310591285081498173534462), (Int.ofNat 11651712775456551618822763561535), (Int.ofNat 1049241961702698873346001180030), (Int.negOfNat 590469946412079096291846287320), (Int.ofNat 93338090231580454016221822306), (Int.ofNat 21425999050902695448779101442), (Int.negOfNat 2055050941953018024058317492), (Int.negOfNat 363863018748591288226204288), (Int.ofNat 22330579744871229055223784), (Int.ofNat 3615004094253113822935282), (Int.negOfNat 151927821551958765276553), (Int.negOfNat 23626040670874020647529), (Int.ofNat 710934833888119913338), (Int.ofNat 109523383532783425416), (Int.negOfNat 2344667071206531856), (Int.negOfNat 353581349186394867), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-1653994786906641147023050423525847/2814749767106560000000000000000000), (-216856677655295642540749086767231/2814749767106560000000000000000000), (2330342555091310323764552712307/1125899906842624000000000000000000), (104924196170269887334600118003/562949953421312000000000000000000), (-14761748660301977407296157183/140737488355328000000000000000000), (46669045115790227008110911153/2814749767106560000000000000000000), (10712999525451347724389550721/2814749767106560000000000000000000), (-513762735488254506014579373/1407374883553280000000000000000000), (-2842679833973369439267221/43980465111040000000000000000000), (2791322468108903631902973/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial161.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial161.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial161.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial161 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 4125846394797889661175081582358187), (Int.negOfNat 383055342346686471926081842112286), (Int.ofNat 14490956673680085265665723122192), (Int.ofNat 1851075254661950116709985372340), (Int.ofNat 775104079726054019587509947834), (Int.ofNat 82433283368114080897352966140), (Int.negOfNat 24357006224745427667480165683), (Int.negOfNat 2471762903631818932707678316), (Int.ofNat 348278754372178238960928437), (Int.ofNat 33489282896831038286116896), (Int.negOfNat 2988801394913696652821915), (Int.negOfNat 276009537907313806061969), (Int.ofNat 17121845842837431077747), (Int.ofNat 1538124308538208684797), (Int.negOfNat 70120624139156164001), (Int.negOfNat 6243220091576338416), (Int.ofNat 287387104471527864), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-4125846394797889661175081582358187/5629499534213120000000000000000000), (-191527671173343235963040921056143/2814749767106560000000000000000000), (905684792105005329104107695137/351843720888320000000000000000000), (92553762733097505835499268617/281474976710656000000000000000000), (387552039863027009793754973917/2814749767106560000000000000000000), (4121664168405704044867648307/281474976710656000000000000000000), (-24357006224745427667480165683/5629499534213120000000000000000000), (-617940725907954733176919579/1407374883553280000000000000000000), (348278754372178238960928437/5629499534213120000000000000000000), (1046540090525969946441153/175921860444160000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial161.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial161.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial161.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial161 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 4805917592992094410754808718456352), (Int.negOfNat 276848635954153865292777670824192), (Int.ofNat 44025465308381604731863814680965), (Int.ofNat 6816834817107209424377466395034), (Int.negOfNat 78158586811960665267541777785), (Int.negOfNat 224044288002692796251878033011), (Int.negOfNat 10289715214788820210992464746), (Int.ofNat 4160058256782112838305757210), (Int.ofNat 230072180262050432710248091), (Int.negOfNat 45333328672844496917541093), (Int.negOfNat 2588921227909544940869551), (Int.ofNat 317776700277161944755960), (Int.ofNat 18226997398478949789589), (Int.negOfNat 1545490064316868536479), (Int.negOfNat 88132982356551761234), (Int.ofNat 5568106137261237992), (Int.ofNat 324767711359836208), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-150184924781002950336087772451761/175921860444160000000000000000000), (-1081439984195913536299912776657/21990232555520000000000000000000), (8805093061676320946372762936193/1125899906842624000000000000000000), (3408417408553604712188733197517/2814749767106560000000000000000000), (-15631717362392133053508355557/1125899906842624000000000000000000), (-224044288002692796251878033011/5629499534213120000000000000000000), (-5144857607394410105496232373/2814749767106560000000000000000000), (416005825678211283830575721/562949953421312000000000000000000), (230072180262050432710248091/5629499534213120000000000000000000), (-45333328672844496917541093/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial161.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial161.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial161.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial161 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 5137490585738680910692354762243331), (Int.negOfNat 39359466853036603480886255778314), (Int.ofNat 65636627498937481464333855033513), (Int.negOfNat 1943146624858961680945722344142), (Int.negOfNat 1715972565884567992334530229434), (Int.ofNat 3390740640855102526275017468), (Int.ofNat 39941232508293540241930173612), (Int.ofNat 769725895774545127370171548), (Int.negOfNat 563363265092894294611034877), (Int.negOfNat 16339350474415251846145561), (Int.ofNat 4910727136815501143614565), (Int.ofNat 165829130075909175464030), (Int.negOfNat 28594473261738694319125), (Int.negOfNat 1032398823058491109823), (Int.ofNat 119023387198898343106), (Int.ofNat 4427839708604076644), (Int.negOfNat 429418917538016998), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-5137490585738680910692354762243331/5629499534213120000000000000000000), (-19679733426518301740443127889157/2814749767106560000000000000000000), (65636627498937481464333855033513/5629499534213120000000000000000000), (-971573312429480840472861172071/2814749767106560000000000000000000), (-857986282942283996167265114717/2814749767106560000000000000000000), (847685160213775631568754367/1407374883553280000000000000000000), (9985308127073385060482543403/1407374883553280000000000000000000), (192431473943636281842542887/1407374883553280000000000000000000), (-563363265092894294611034877/5629499534213120000000000000000000), (-16339350474415251846145561/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial161.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial161.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial161.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial161 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 4994047818053315280039195401100522), (Int.ofNat 152654712453461673635768210762476), (Int.ofNat 22143169669439527316585650721972), (Int.negOfNat 9732035706665185025118242473134), (Int.ofNat 302219830439834672773428573683), (Int.ofNat 303412178033847088838337786592), (Int.negOfNat 6225788071665113846773657825), (Int.negOfNat 5787921939566984420946077452), (Int.ofNat 1552681581786360292082399), (Int.ofNat 64662256644674378236991978), (Int.ofNat 766391467230396565883411), (Int.negOfNat 458110330045528554852911), (Int.negOfNat 8385737215105688070687), (Int.ofNat 2242721260109397773615), (Int.ofNat 48891950695924150539), (Int.negOfNat 8234770205863810680), (Int.negOfNat 224938167000032982), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-2497023909026657640019597700550261/2814749767106560000000000000000000), (38163678113365418408942052690619/1407374883553280000000000000000000), (5535792417359881829146412680493/1407374883553280000000000000000000), (-4866017853332592512559121236567/2814749767106560000000000000000000), (302219830439834672773428573683/5629499534213120000000000000000000), (9481630563557721526198055831/175921860444160000000000000000000), (-249031522866604553870946313/225179981368524800000000000000000), (-1446980484891746105236519363/1407374883553280000000000000000000), (1552681581786360292082399/5629499534213120000000000000000000), (32331128322337189118495989/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial161.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial161.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial161.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial161 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 4664583261898030204568452737121337), (Int.ofNat 154747883541732155433333368151519), (Int.negOfNat 9809990100235343377682477803639), (Int.ofNat 927408445664786441627885742175), (Int.ofNat 1595367867862230381490947507884), (Int.negOfNat 133880475083928935205607149133), (Int.negOfNat 47814912183408919733931709106), (Int.ofNat 1906409483985878682038939214), (Int.ofNat 727036927587149731078671440), (Int.negOfNat 9496363936503909553984080), (Int.negOfNat 6429405228257861971431934), (Int.negOfNat 1973890354987203360667), (Int.ofNat 37446099203609401871195), (Int.ofNat 272833800528725513734), (Int.negOfNat 155781820393784958044), (Int.negOfNat 1718066178526194160), (Int.ofNat 521535958424604519), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-4664583261898030204568452737121337/5629499534213120000000000000000000), (154747883541732155433333368151519/5629499534213120000000000000000000), (-9809990100235343377682477803639/5629499534213120000000000000000000), (37096337826591457665115429687/225179981368524800000000000000000), (398841966965557595372736876971/1407374883553280000000000000000000), (-133880475083928935205607149133/5629499534213120000000000000000000), (-23907456091704459866965854553/2814749767106560000000000000000000), (953204741992939341019469607/2814749767106560000000000000000000), (9087961594839371638483393/70368744177664000000000000000000), (-118704549206298869424801/70368744177664000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial161.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial161.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial161.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial161 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 4368307786334031881475261533045970), (Int.ofNat 159342348726988257112219163579123), (Int.ofNat 14325863953917092867402904027482), (Int.ofNat 2909475060993504030760297341030), (Int.negOfNat 1384355469938050772923414054212), (Int.negOfNat 289132958202128182927330071372), (Int.ofNat 34443492800035248805142821476), (Int.ofNat 6899414615389683657663111703), (Int.negOfNat 325750262948932515483464439), (Int.negOfNat 79311620864935315768465868), (Int.ofNat 1626541962456003477359047), (Int.ofNat 558577417752057011008312), (Int.negOfNat 4419571321409208328038), (Int.negOfNat 2712252471582367109328), (Int.ofNat 3049941963462081858), (Int.ofNat 9854479342709913050), (Int.ofNat 43542148930313712), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-436830778633403188147526153304597/562949953421312000000000000000000), (159342348726988257112219163579123/5629499534213120000000000000000000), (7162931976958546433701452013741/2814749767106560000000000000000000), (290947506099350403076029734103/562949953421312000000000000000000), (-346088867484512693230853513553/1407374883553280000000000000000000), (-72283239550532045731832517843/1407374883553280000000000000000000), (8610873200008812201285705369/1407374883553280000000000000000000), (6899414615389683657663111703/5629499534213120000000000000000000), (-325750262948932515483464439/5629499534213120000000000000000000), (-19827905216233828942116467/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial161.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial161.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial161.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial161 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 3997479496170686782352235112426115), (Int.ofNat 193331649126372197755484603064728), (Int.negOfNat 12585076267471757898209429936592), (Int.negOfNat 11318873469452108178459869494365), (Int.negOfNat 917931795170092268734385830456), (Int.ofNat 426235104905068091396007413249), (Int.ofNat 54146963420135816824407139509), (Int.negOfNat 5615472765363696084516443813), (Int.negOfNat 861561243536957875327418240), (Int.ofNat 40500232928218602802836143), (Int.ofNat 7478031094162729290076545), (Int.negOfNat 188813628149718618005527), (Int.negOfNat 42704827084696837465131), (Int.ofNat 617400937530377977168), (Int.ofNat 175553072009047928740), (Int.negOfNat 1380310043560624234), (Int.negOfNat 553187659954618950), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-799495899234137356470447022485223/1125899906842624000000000000000000), (24166456140796524719435575383091/703687441776640000000000000000000), (-786567266716984868638089371037/351843720888320000000000000000000), (-2263774693890421635691973898873/1125899906842624000000000000000000), (-114741474396261533591798228807/703687441776640000000000000000000), (426235104905068091396007413249/5629499534213120000000000000000000), (54146963420135816824407139509/5629499534213120000000000000000000), (-5615472765363696084516443813/5629499534213120000000000000000000), (-1346189443026496680199091/8796093022208000000000000000000), (40500232928218602802836143/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial161.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial161.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial161.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial161 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 3750200970779593520719068350897868), (Int.ofNat 19016575939150115071312773298858), (Int.negOfNat 60487385439410853394483023277087), (Int.ofNat 2682120530363710659349547917818), (Int.ofNat 4306768574503288266184638317101), (Int.ofNat 350732805663397555880563954715), (Int.negOfNat 73676537524901216518165982638), (Int.negOfNat 8329340803996122275440783232), (Int.ofNat 682266575530273424056408488), (Int.ofNat 90443559699323617631388502), (Int.negOfNat 4127659133410216859848210), (Int.negOfNat 611506606977792015915506), (Int.ofNat 17922376147790285775947), (Int.ofNat 2894825800928103718465), (Int.negOfNat 59159106261111195475), (Int.negOfNat 10285982826777896574), (Int.ofNat 137853869139405558), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-937550242694898380179767087724467/1407374883553280000000000000000000), (9508287969575057535656386649429/2814749767106560000000000000000000), (-60487385439410853394483023277087/5629499534213120000000000000000000), (1341060265181855329674773958909/2814749767106560000000000000000000), (4306768574503288266184638317101/5629499534213120000000000000000000), (70146561132679511176112790943/1125899906842624000000000000000000), (-36838268762450608259082991319/2814749767106560000000000000000000), (-65072975031219705276881119/43980465111040000000000000000000), (85283321941284178007051061/703687441776640000000000000000000), (45221779849661808815694251/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial161.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial161.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial161.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial161 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 3858094519379094499697139536040131), (Int.negOfNat 41870153795518308703973764580826), (Int.ofNat 65322980137827032213867921634841), (Int.ofNat 36335324201832115763560607134298), (Int.ofNat 2112033351442353760053436024300), (Int.negOfNat 793746577338863206791355926483), (Int.negOfNat 74378944044668767482788866758), (Int.ofNat 9150197758094588642585407666), (Int.ofNat 1002278904624260513204297594), (Int.negOfNat 68662272788759671385020784), (Int.negOfNat 8014018415004933811403288), (Int.ofNat 367528901199296458396747), (Int.ofNat 43731375751395707368514), (Int.negOfNat 1481149089422266320917), (Int.negOfNat 175054952695312830322), (Int.ofNat 4568766930467725988), (Int.ofNat 584839361484633381), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-3858094519379094499697139536040131/5629499534213120000000000000000000), (-20935076897759154351986882290413/2814749767106560000000000000000000), (65322980137827032213867921634841/5629499534213120000000000000000000), (18167662100916057881780303567149/2814749767106560000000000000000000), (21120333514423537600534360243/56294995342131200000000000000000), (-793746577338863206791355926483/5629499534213120000000000000000000), (-37189472022334383741394433379/2814749767106560000000000000000000), (4575098879047294321292703833/2814749767106560000000000000000000), (501139452312130256602148797/2814749767106560000000000000000000), (-4291392049297479461563799/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial161.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial161.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial161.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial161 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 3384842557796094160026967855295628), (Int.ofNat 650181750564029283158300736237477), (Int.ofNat 260222360742313136910697298014617), (Int.ofNat 16028964706874055076563698827164), (Int.negOfNat 6967754900994106225956703063916), (Int.negOfNat 657052831122033744789066348213), (Int.ofNat 100486594284720784941233697543), (Int.ofNat 10425655222710299700348390260), (Int.negOfNat 933911015152252723661222093), (Int.negOfNat 97101299464607658148295961), (Int.ofNat 6105128166755267738530470), (Int.ofNat 608171556705188286864895), (Int.negOfNat 29524546826497378715736), (Int.negOfNat 2757023030668944331076), (Int.ofNat 109488188359968518232), (Int.ofNat 9451807532082764535), (Int.negOfNat 329800454385796305), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-846210639449023540006741963823907/1407374883553280000000000000000000), (650181750564029283158300736237477/5629499534213120000000000000000000), (260222360742313136910697298014617/5629499534213120000000000000000000), (4007241176718513769140924706791/1407374883553280000000000000000000), (-1741938725248526556489175765979/1407374883553280000000000000000000), (-657052831122033744789066348213/5629499534213120000000000000000000), (100486594284720784941233697543/5629499534213120000000000000000000), (521282761135514985017419513/281474976710656000000000000000000), (-933911015152252723661222093/5629499534213120000000000000000000), (-97101299464607658148295961/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial161.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial161.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial161.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial161.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial161 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial161 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial161 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 4953842847323622116322227011254895), (Int.negOfNat 885065882150851885298792373541639), (Int.ofNat 306617002653460672563415282247202), (Int.negOfNat 14039867356808829305781220837362), (Int.negOfNat 7215086156567669296642351392601), (Int.ofNat 651339222427868366354153961005), (Int.ofNat 101038794471884014715529435820), (Int.negOfNat 10417111773596856268602019960), (Int.negOfNat 934587760624478725311739693), (Int.ofNat 97093433258432675901015661), (Int.ofNat 6105649947131523482533770), (Int.negOfNat 608166411480068169838495), (Int.negOfNat 29524546826497378715736), (Int.ofNat 2757023030668944331076), (Int.ofNat 109488188359968518232), (Int.negOfNat 9451807532082764535), (Int.negOfNat 329800454385796305), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-990768569464724423264445402250979/1125899906842624000000000000000000), (-885065882150851885298792373541639/5629499534213120000000000000000000), (153308501326730336281707641123601/2814749767106560000000000000000000), (-7019933678404414652890610418681/2814749767106560000000000000000000), (-7215086156567669296642351392601/5629499534213120000000000000000000), (130267844485573673270830792201/1125899906842624000000000000000000), (5051939723594200735776471791/281474976710656000000000000000000), (-260427794339921406715050499/140737488355328000000000000000000), (-934587760624478725311739693/5629499534213120000000000000000000), (97093433258432675901015661/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial161.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial161.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial161.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 5699475603559731699499173029292627), (Int.ofNat 8171210692585473314509119950357), (Int.ofNat 117396193723255960497286232787457), (Int.negOfNat 36461531701392514704880894892554), (Int.ofNat 1842307705573982348078664250577), (Int.ofNat 795062308569386743045002234702), (Int.negOfNat 73786406490066536802013490158), (Int.negOfNat 9153094890230223253939683266), (Int.ofNat 1001558785712420234259844194), (Int.ofNat 68665424852951079235893784), (Int.negOfNat 8013465028534965410387288), (Int.negOfNat 367530830658716502281647), (Int.ofNat 43731375751395707368514), (Int.ofNat 1481149089422266320917), (Int.negOfNat 175054952695312830322), (Int.negOfNat 4568766930467725988), (Int.ofNat 584839361484633381), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-5699475603559731699499173029292627/5629499534213120000000000000000000), (8171210692585473314509119950357/5629499534213120000000000000000000), (117396193723255960497286232787457/5629499534213120000000000000000000), (-18230765850696257352440447446277/2814749767106560000000000000000000), (1842307705573982348078664250577/5629499534213120000000000000000000), (397531154284693371522501117351/2814749767106560000000000000000000), (-36893203245033268401006745079/2814749767106560000000000000000000), (-4576547445115111626969841633/2814749767106560000000000000000000), (500779392856210117129922097/2814749767106560000000000000000000), (8583178106618884904486723/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial161.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial161.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial161.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 5455932884360358434267977170881980), (Int.ofNat 145648625093439926352291699499979), (Int.negOfNat 15400581346421609315460494852321), (Int.negOfNat 4821585462564116163021175205793), (Int.ofNat 4084154785035904745167142812442), (Int.negOfNat 342861870391289448409726205245), (Int.negOfNat 73201283541428233387450987968), (Int.ofNat 8315888610471714086878776432), (Int.ofNat 681697784467896199708848588), (Int.negOfNat 90430297899286682566624602), (Int.negOfNat 4127224883595629876459810), (Int.ofNat 611498245986971825747606), (Int.ofNat 17922376147790285775947), (Int.negOfNat 2894825800928103718465), (Int.negOfNat 59159106261111195475), (Int.ofNat 10285982826777896574), (Int.ofNat 137853869139405558), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-272796644218017921713398858544099/281474976710656000000000000000000), (145648625093439926352291699499979/5629499534213120000000000000000000), (-15400581346421609315460494852321/5629499534213120000000000000000000), (-4821585462564116163021175205793/5629499534213120000000000000000000), (2042077392517952372583571406221/2814749767106560000000000000000000), (-68572374078257889681945241049/1125899906842624000000000000000000), (-1143770055334816146678921687/87960930222080000000000000000000), (519743038154482130429923527/351843720888320000000000000000000), (170424446116974049927212147/1407374883553280000000000000000000), (-45215148949643341283312301/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial161.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial161.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial161.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 5213930905494797384659737210542558), (Int.ofNat 119597895066985167442485618249871), (Int.ofNat 15055949771177591949789550021861), (Int.ofNat 7780901345326504352684970243119), (Int.negOfNat 1037665736002627569996870804140), (Int.negOfNat 414015962889981478659487472981), (Int.ofNat 54380413548277100536276651086), (Int.ofNat 5595195883654617115828723013), (Int.negOfNat 861826094038348547398919640), (Int.negOfNat 40480519097857432088595743), (Int.ofNat 7478227377315510860993945), (Int.ofNat 188801408240058340067827), (Int.negOfNat 42704827084696837465131), (Int.negOfNat 617400937530377977168), (Int.ofNat 175553072009047928740), (Int.ofNat 1380310043560624234), (Int.negOfNat 553187659954618950), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-2606965452747398692329868605271279/2814749767106560000000000000000000), (119597895066985167442485618249871/5629499534213120000000000000000000), (15055949771177591949789550021861/5629499534213120000000000000000000), (7780901345326504352684970243119/5629499534213120000000000000000000), (-51883286800131378499843540207/281474976710656000000000000000000), (-414015962889981478659487472981/5629499534213120000000000000000000), (27190206774138550268138325543/2814749767106560000000000000000000), (5595195883654617115828723013/5629499534213120000000000000000000), (-21545652350958713684972991/140737488355328000000000000000000), (-40480519097857432088595743/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial161.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial161.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial161.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 4878152222784553422156474210094599), (Int.ofNat 218877192843144135078503811322121), (Int.ofNat 18884994126863541155319152314817), (Int.negOfNat 6890922219563090037866272079122), (Int.negOfNat 1373783558962855500286321119627), (Int.ofNat 302372536992163910885187906079), (Int.ofNat 34377120139714387589866233089), (Int.negOfNat 6920970144882860761570624603), (Int.negOfNat 325642084552719946632317339), (Int.ofNat 79332383719560712782166668), (Int.ofNat 1626447693713977147676947), (Int.negOfNat 558590923967997318202612), (Int.negOfNat 4419571321409208328038), (Int.ofNat 2712252471582367109328), (Int.ofNat 3049941963462081858), (Int.negOfNat 9854479342709913050), (Int.ofNat 43542148930313712), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-4878152222784553422156474210094599/5629499534213120000000000000000000), (218877192843144135078503811322121/5629499534213120000000000000000000), (18884994126863541155319152314817/5629499534213120000000000000000000), (-3445461109781545018933136039561/2814749767106560000000000000000000), (-1373783558962855500286321119627/5629499534213120000000000000000000), (302372536992163910885187906079/5629499534213120000000000000000000), (34377120139714387589866233089/5629499534213120000000000000000000), (-6920970144882860761570624603/5629499534213120000000000000000000), (-325642084552719946632317339/5629499534213120000000000000000000), (19833095929890178195541667/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial161.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial161.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial161.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 4431017823444914453908649294869061), (Int.ofNat 195306037828293803697236978409500), (Int.negOfNat 27856777383868211749907097928702), (Int.negOfNat 4317084401282144994701659629460), (Int.ofNat 1728520725074566871227181110385), (Int.ofNat 144602100091462155148473753055), (Int.negOfNat 48157499366284663289325479206), (Int.negOfNat 1923401987413539755409864714), (Int.ofNat 727485209923025323688235040), (Int.ofNat 9512509731868208798140880), (Int.negOfNat 6429762393309675572696634), (Int.ofNat 1963599904746969307867), (Int.ofNat 37446099203609401871195), (Int.negOfNat 272833800528725513734), (Int.negOfNat 155781820393784958044), (Int.ofNat 1718066178526194160), (Int.ofNat 521535958424604519), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-4431017823444914453908649294869061/5629499534213120000000000000000000), (390612075656587607394473956819/11258999068426240000000000000000), (-13928388691934105874953548964351/2814749767106560000000000000000000), (-215854220064107249735082981473/281474976710656000000000000000000), (345704145014913374245436222077/1125899906842624000000000000000000), (28920420018292431029694750611/1125899906842624000000000000000000), (-24078749683142331644662739603/2814749767106560000000000000000000), (-961700993706769877704932357/2814749767106560000000000000000000), (4546782562018908273051469/35184372088832000000000000000000), (118906371648352609976761/70368744177664000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial161.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial161.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial161.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 4157229533902685035203036894864072), (Int.ofNat 89581674669437630264959950509575), (Int.negOfNat 12281041322899941645056036248917), (Int.ofNat 7773002090763743674158795923755), (Int.ofNat 517837781190661862718194905075), (Int.negOfNat 297998747206192332226144666588), (Int.negOfNat 6746550095778561968600428425), (Int.ofNat 5780035899794552947007422452), (Int.ofNat 2215599495903760937236099), (Int.negOfNat 64655104223112264416977678), (Int.ofNat 765870206538027294176211), (Int.ofNat 458106471126688467083111), (Int.negOfNat 8385737215105688070687), (Int.negOfNat 2242721260109397773615), (Int.ofNat 48891950695924150539), (Int.ofNat 8234770205863810680), (Int.negOfNat 224938167000032982), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-519653691737835629400379611858009/703687441776640000000000000000000), (3583266986777505210598398020383/225179981368524800000000000000000), (-12281041322899941645056036248917/5629499534213120000000000000000000), (1554600418152748734831759184751/1125899906842624000000000000000000), (20713511247626474508727796203/225179981368524800000000000000000), (-74499686801548083056536166647/1407374883553280000000000000000000), (-269862003831142478744017137/225179981368524800000000000000000), (1445008974948638236751855613/1407374883553280000000000000000000), (2215599495903760937236099/5629499534213120000000000000000000), (-32327552111556132208488839/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial161.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial161.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial161.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 3965979688595692342159582031088472), (Int.ofNat 127620628846824641108589060135555), (Int.ofNat 24937052588123212492590095328522), (Int.ofNat 1839073981824814522367747839921), (Int.negOfNat 1478909968044271004749466944101), (Int.negOfNat 4581779270025965052856930256), (Int.ofNat 39387319718970065272200725912), (Int.negOfNat 766491646704409073478012248), (Int.negOfNat 562668961304071495986366277), (Int.ofNat 16335616607111569380783461), (Int.ofNat 4910185601871608826585965), (Int.negOfNat 165825914310209102322530), (Int.negOfNat 28594473261738694319125), (Int.ofNat 1032398823058491109823), (Int.ofNat 119023387198898343106), (Int.negOfNat 4427839708604076644), (Int.negOfNat 429418917538016998), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-495747461074461542769947753886059/703687441776640000000000000000000), (25524125769364928221717812027111/1125899906842624000000000000000000), (12468526294061606246295047664261/2814749767106560000000000000000000), (1839073981824814522367747839921/5629499534213120000000000000000000), (-1478909968044271004749466944101/5629499534213120000000000000000000), (-286361204376622815803558141/351843720888320000000000000000000), (4923414964871258159025090739/703687441776640000000000000000000), (-95811455838051134184751531/703687441776640000000000000000000), (-562668961304071495986366277/5629499534213120000000000000000000), (16335616607111569380783461/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial161.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial161.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial161.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 3617795225472983037405708929209257), (Int.ofNat 208449143941897990565747218951796), (Int.ofNat 8166128977521676721858682088351), (Int.negOfNat 5157647154802285056069001584679), (Int.ofNat 115419872588606760849041973636), (Int.ofNat 216777227610657141413761269952), (Int.negOfNat 10724861986125198275833202756), (Int.negOfNat 4146752413515980932039970510), (Int.ofNat 230607326692381140531705991), (Int.ofNat 45319808254906522142214693), (Int.negOfNat 2589335111882756938710551), (Int.negOfNat 317767696133201739959760), (Int.ofNat 18226997398478949789589), (Int.ofNat 1545490064316868536479), (Int.negOfNat 88132982356551761234), (Int.negOfNat 5568106137261237992), (Int.ofNat 324767711359836208), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-3617795225472983037405708929209257/5629499534213120000000000000000000), (52112285985474497641436804737949/1407374883553280000000000000000000), (8166128977521676721858682088351/5629499534213120000000000000000000), (-5157647154802285056069001584679/5629499534213120000000000000000000), (28854968147151690212260493409/1407374883553280000000000000000000), (3387144181416517834590019843/87960930222080000000000000000000), (-2681215496531299568958300689/1407374883553280000000000000000000), (-414675241351598093203997051/562949953421312000000000000000000), (230607326692381140531705991/5629499534213120000000000000000000), (45319808254906522142214693/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial161.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial161.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial161.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 3201848162485951328457063949927415), (Int.ofNat 196664830489105181255708823861475), (Int.negOfNat 7443337014626376216674662854662), (Int.ofNat 1004765789064470388174948258145), (Int.ofNat 874168449102115959480952299883), (Int.negOfNat 93594982671039412464715224376), (Int.negOfNat 24556269122452750321842196583), (Int.ofNat 2491338365982207657734279916), (Int.ofNat 348509211538364012648367237), (Int.negOfNat 33508809036790185893170996), (Int.negOfNat 2988973544896115090648115), (Int.ofNat 276022400970114098627969), (Int.ofNat 17121845842837431077747), (Int.negOfNat 1538124308538208684797), (Int.negOfNat 70120624139156164001), (Int.ofNat 6243220091576338416), (Int.ofNat 287387104471527864), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-640369632497190265691412789985483/1125899906842624000000000000000000), (7866593219564207250228352954459/225179981368524800000000000000000), (-3721668507313188108337331427331/2814749767106560000000000000000000), (200953157812894077634989651629/1125899906842624000000000000000000), (874168449102115959480952299883/5629499534213120000000000000000000), (-11699372833879926558089403047/703687441776640000000000000000000), (-24556269122452750321842196583/5629499534213120000000000000000000), (622834591495551914433569979/1407374883553280000000000000000000), (348509211538364012648367237/5629499534213120000000000000000000), (-8377202259197546473292749/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial161.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial161.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial161.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 2820445154404782069560043885509689), (Int.ofNat 196103586691259740009281472301970), (Int.ofNat 8302727260232539942508924110716), (Int.ofNat 2132032156745111905962085438402), (Int.negOfNat 609319609866870775320473908389), (Int.negOfNat 105183737351793647904050920128), (Int.ofNat 21513092663794289994493076642), (Int.ofNat 2075404425738343965203730392), (Int.negOfNat 363997997353356520756251988), (Int.negOfNat 22350694781854113114872084), (Int.ofNat 3615118698981289969104882), (Int.ofNat 151940684614759057842553), (Int.negOfNat 23626040670874020647529), (Int.negOfNat 710934833888119913338), (Int.ofNat 109523383532783425416), (Int.ofNat 2344667071206531856), (Int.negOfNat 353581349186394867), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-2820445154404782069560043885509689/5629499534213120000000000000000000), (19610358669125974000928147230197/562949953421312000000000000000000), (2075681815058134985627231027679/1407374883553280000000000000000000), (1066016078372555952981042719201/2814749767106560000000000000000000), (-609319609866870775320473908389/5629499534213120000000000000000000), (-1643495896121775748500795627/87960930222080000000000000000000), (10756546331897144997246538321/2814749767106560000000000000000000), (259425553217292995650466299/703687441776640000000000000000000), (-90999499338339130189062997/1407374883553280000000000000000000), (-5587673695463528278718021/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial161.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial161.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial161.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 2389544033122634028045171772325422), (Int.ofNat 231641635433395462733003038532929), (Int.ofNat 3903344725418988002237163206924), (Int.negOfNat 3058833727103763868933738523421), (Int.negOfNat 235187055648061636794440821836), (Int.ofNat 150308769568993195748592816157), (Int.ofNat 7708126773585004034727774287), (Int.negOfNat 3321433350159574213441685105), (Int.negOfNat 109701086293356540182767357), (Int.ofNat 40875800187178029933206956), (Int.ofNat 880021369001774646779983), (Int.negOfNat 319129812753423583843508), (Int.negOfNat 4498966426842096308832), (Int.ofNat 1718388423074578329194), (Int.ofNat 15543143774557176808), (Int.negOfNat 6807872510755293086), (Int.negOfNat 105991086401808594), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-1194772016561317014022585886162711/2814749767106560000000000000000000), (231641635433395462733003038532929/5629499534213120000000000000000000), (975836181354747000559290801731/1407374883553280000000000000000000), (-3058833727103763868933738523421/5629499534213120000000000000000000), (-58796763912015409198610205459/1407374883553280000000000000000000), (150308769568993195748592816157/5629499534213120000000000000000000), (7708126773585004034727774287/5629499534213120000000000000000000), (-664286670031914842688337021/1125899906842624000000000000000000), (-109701086293356540182767357/5629499534213120000000000000000000), (10218950046794507483301739/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial161.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial161.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial161.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 1934009900609890151700918290194001), (Int.ofNat 215022419633613309512338129292771), (Int.negOfNat 8458605198511104758571969959099), (Int.ofNat 468514919859623827949851976782), (Int.ofNat 840736645200036414456639196465), (Int.negOfNat 5168556773727696233314970707), (Int.negOfNat 25264725334260077428566568779), (Int.ofNat 39917219981590605110830799), (Int.ofNat 395926160003302155730099858), (Int.negOfNat 1084506446388878930528333), (Int.negOfNat 3765825197525534078058471), (Int.ofNat 17126800018721834348153), (Int.ofNat 23953416193183651934363), (Int.negOfNat 143834867472919468730), (Int.negOfNat 108606124752364221510), (Int.ofNat 845351999790251110), (Int.ofNat 321929647656380436), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-1934009900609890151700918290194001/5629499534213120000000000000000000), (215022419633613309512338129292771/5629499534213120000000000000000000), (-8458605198511104758571969959099/5629499534213120000000000000000000), (234257459929811913974925988391/2814749767106560000000000000000000), (168147329040007282891327839293/1125899906842624000000000000000000), (-5168556773727696233314970707/5629499534213120000000000000000000), (-25264725334260077428566568779/5629499534213120000000000000000000), (39917219981590605110830799/5629499534213120000000000000000000), (197963080001651077865049929/2814749767106560000000000000000000), (-1084506446388878930528333/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial161.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial161.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial161.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 1522279727390038556496284818552276), (Int.ofNat 208851732108399518129078827507022), (Int.ofNat 8743128451408513544843794370728), (Int.ofNat 3616790961728625001311412802104), (Int.negOfNat 323604468664841614350699426992), (Int.negOfNat 157390100746897318671015729621), (Int.ofNat 7815112107098229796497112664), (Int.ofNat 3240545689482541331638001066), (Int.negOfNat 114207123204086595024011664), (Int.negOfNat 38350240917952519133281202), (Int.ofNat 1107722265449062776433594), (Int.ofNat 292662823857227578339594), (Int.negOfNat 7451530810288612566189), (Int.negOfNat 1554532182785170064187), (Int.ofNat 35840136463151972805), (Int.ofNat 6142117008449443002), (Int.negOfNat 75404931667910676), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-380569931847509639124071204638069/1407374883553280000000000000000000), (104425866054199759064539413753511/2814749767106560000000000000000000), (1092891056426064193105474296341/703687441776640000000000000000000), (452098870216078125163926600263/703687441776640000000000000000000), (-20225279291552600896918714187/351843720888320000000000000000000), (-157390100746897318671015729621/5629499534213120000000000000000000), (976889013387278724562139083/703687441776640000000000000000000), (1620272844741270665819000533/2814749767106560000000000000000000), (-7137945200255412189000729/351843720888320000000000000000000), (-19175120458976259566640601/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial161.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial161.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial161.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1050015800510042776996581792275095), (Int.ofNat 267034853103534326550066468245680), (Int.ofNat 13778324278586231121111745174853), (Int.negOfNat 2585235726399901983791605610514), (Int.negOfNat 777996804306502747217945384833), (Int.ofNat 96490905123344910237873995285), (Int.ofNat 21928618218558965776537626300), (Int.negOfNat 1835325950476760993516612066), (Int.negOfNat 330535629295806814611210044), (Int.ofNat 21258007870010684013519222), (Int.ofNat 3077684349239175674194578), (Int.negOfNat 163914752304618323709953), (Int.negOfNat 19361780470319041983600), (Int.ofNat 891887663776942563071), (Int.ofNat 87549763688699359558), (Int.negOfNat 3703429048540458356), (Int.negOfNat 290277946126366005), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-210003160102008555399316358455019/1125899906842624000000000000000000), (3337935663794179081875830853071/70368744177664000000000000000000), (13778324278586231121111745174853/5629499534213120000000000000000000), (-1292617863199950991895802805257/2814749767106560000000000000000000), (-777996804306502747217945384833/5629499534213120000000000000000000), (19298181024668982047574799057/1125899906842624000000000000000000), (219286182185589657765376263/56294995342131200000000000000000), (-917662975238380496758306033/2814749767106560000000000000000000), (-82633907323951703652802511/1407374883553280000000000000000000), (10629003935005342006759611/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial161.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial161.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial161.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 489777400929769633232182499626309), (Int.ofNat 277060766899069232745836506248855), (Int.negOfNat 9120872537703638117682252904578), (Int.negOfNat 2908327217894407405772761210945), (Int.ofNat 736641532316906084486437336878), (Int.ofNat 118622376308609949332424020420), (Int.negOfNat 19475906974408488155972300392), (Int.negOfNat 2335310706275658260664256178), (Int.ofNat 286172216855973829268306359), (Int.ofNat 26987217039095787031048753), (Int.negOfNat 2659240435784863502008554), (Int.negOfNat 203927737773144392437415), (Int.ofNat 16891045574982861698490), (Int.ofNat 1081261216146215765586), (Int.negOfNat 77487779675395119028), (Int.negOfNat 4323426710643784881), (Int.ofNat 246250382560958469), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-489777400929769633232182499626309/5629499534213120000000000000000000), (55412153379813846549167301249771/1125899906842624000000000000000000), (-4560436268851819058841126452289/2814749767106560000000000000000000), (-581665443578881481154552242189/1125899906842624000000000000000000), (368320766158453042243218668439/2814749767106560000000000000000000), (5931118815430497466621201021/281474976710656000000000000000000), (-2434488371801061019496537549/703687441776640000000000000000000), (-1167655353137829130332128089/2814749767106560000000000000000000), (286172216855973829268306359/5629499534213120000000000000000000), (26987217039095787031048753/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial161.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial161.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial161.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 18714841208209281734246500032177), (Int.ofNat 234293845403085765291724459102080), (Int.negOfNat 5043112419229105466272356600997), (Int.ofNat 3916380033694904663416124230374), (Int.ofNat 487842376567216091991653026532), (Int.negOfNat 154138215851887413016710450833), (Int.negOfNat 12765032987996558275254381248), (Int.ofNat 3007605865361592419898446602), (Int.ofNat 185035701391319640252324581), (Int.negOfNat 34830175585771508510211847), (Int.negOfNat 1699969683651904776088146), (Int.ofNat 264940068579470405940845), (Int.ofNat 10717581837064292069410), (Int.negOfNat 1415707576457578069274), (Int.negOfNat 48932983262504998592), (Int.ofNat 5631656579060817559), (Int.ofNat 148246133059876871), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(18714841208209281734246500032177/5629499534213120000000000000000000), (366084133442321508268319467347/8796093022208000000000000000000), (-5043112419229105466272356600997/5629499534213120000000000000000000), (1958190016847452331708062115187/2814749767106560000000000000000000), (121960594141804022997913256633/1407374883553280000000000000000000), (-154138215851887413016710450833/5629499534213120000000000000000000), (-199453640437446223050849707/87960930222080000000000000000000), (1503802932680796209949223301/2814749767106560000000000000000000), (185035701391319640252324581/5629499534213120000000000000000000), (-34830175585771508510211847/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial161.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial161.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial161.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 500930558774871432877624197345924), (Int.ofNat 263398068129107463547381588661945), (Int.ofNat 16949279398859251604257843704681), (Int.ofNat 1425628088685852200398649571925), (Int.negOfNat 921357616823737971530284883610), (Int.negOfNat 47287961713296449499013240776), (Int.ofNat 25165041956335741889194652820), (Int.ofNat 824040398236542854909217314), (Int.negOfNat 376072552177163134980613196), (Int.negOfNat 9087130916341174224801818), (Int.ofNat 3512947935329937312037442), (Int.ofNat 69000432101054656884747), (Int.negOfNat 22287413290084719667460), (Int.negOfNat 377980342350175773729), (Int.ofNat 101588139473447698662), (Int.ofNat 1663897789253015044), (Int.negOfNat 346079926920761695), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(125232639693717858219406049336481/1407374883553280000000000000000000), (52679613625821492709476317732389/1125899906842624000000000000000000), (16949279398859251604257843704681/5629499534213120000000000000000000), (57025123547434088015945982877/225179981368524800000000000000000), (-92135761682373797153028488361/562949953421312000000000000000000), (-5910995214162056187376655097/703687441776640000000000000000000), (1258252097816787094459732641/281474976710656000000000000000000), (412020199118271427454608657/2814749767106560000000000000000000), (-94018138044290783745153299/1407374883553280000000000000000000), (-4543565458170587112400909/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial161.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial161.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial161.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1092292659241845078917805941621281), (Int.ofNat 319849272714871643911067384064108), (Int.ofNat 5525881944499796685600036430990), (Int.negOfNat 4017327110433915699584845633051), (Int.negOfNat 64172173411217155849713784413), (Int.ofNat 165202205858143338611837161970), (Int.negOfNat 23278527787871212973236704), (Int.negOfNat 3326149716165575962098239774), (Int.ofNat 11334567562047660866806224), (Int.ofNat 39294294829581494220502238), (Int.negOfNat 120596582221561153247314), (Int.negOfNat 302627462777325262658206), (Int.ofNat 539315194833913942629), (Int.ofNat 1628093879973219702913), (Int.negOfNat 734698982903446565), (Int.negOfNat 6465831873755949598), (Int.ofNat 43700452186513876), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(1092292659241845078917805941621281/5629499534213120000000000000000000), (79962318178717910977766846016027/1407374883553280000000000000000000), (552588194449979668560003643099/562949953421312000000000000000000), (-4017327110433915699584845633051/5629499534213120000000000000000000), (-64172173411217155849713784413/5629499534213120000000000000000000), (16520220585814333861183716197/562949953421312000000000000000000), (-727453993370975405413647/175921860444160000000000000000000), (-1663074858082787981049119887/2814749767106560000000000000000000), (708410472627978804175389/351843720888320000000000000000000), (19647147414790747110251119/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial161.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial161.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial161.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 1725810886775853698811707608660299), (Int.ofNat 303511170264503097717867360908757), (Int.negOfNat 8951036610565448076679814806357), (Int.ofNat 428462983141364148253696472429), (Int.ofNat 812502848834790724808237441003), (Int.negOfNat 39528005840789138957994204401), (Int.negOfNat 23420420487003218434950068708), (Int.ofNat 981873081905270940528823239), (Int.ofNat 363571915473476669375628042), (Int.negOfNat 12114900865201523701626373), (Int.negOfNat 3496037405862976092204849), (Int.ofNat 89734323375528094271173), (Int.ofNat 22655655513418068155977), (Int.negOfNat 443514165339897233570), (Int.negOfNat 104892006538662843230), (Int.ofNat 1524559097654086710), (Int.ofNat 314428225390747264), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(1725810886775853698811707608660299/5629499534213120000000000000000000), (303511170264503097717867360908757/5629499534213120000000000000000000), (-8951036610565448076679814806357/5629499534213120000000000000000000), (428462983141364148253696472429/5629499534213120000000000000000000), (812502848834790724808237441003/5629499534213120000000000000000000), (-39528005840789138957994204401/5629499534213120000000000000000000), (-5855105121750804608737517177/1407374883553280000000000000000000), (981873081905270940528823239/5629499534213120000000000000000000), (181785957736738334687814021/2814749767106560000000000000000000), (-12114900865201523701626373/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial161.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial161.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial161.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 2310902269904155650059728626108161), (Int.ofNat 291957606420399477846187145949028), (Int.ofNat 5555858281494369105086955934677), (Int.ofNat 2688778082498293206469032661596), (Int.negOfNat 395312926584719888508684493832), (Int.negOfNat 123126801052314383881932491531), (Int.ofNat 13653193131351871658853449883), (Int.ofNat 2656076937954577201956610695), (Int.negOfNat 221920313495994828250375823), (Int.negOfNat 33225961230372869854535904), (Int.ofNat 2081107111296918431145577), (Int.ofNat 267721341315730631095812), (Int.negOfNat 12646379420426470569588), (Int.negOfNat 1487862569889395050526), (Int.ofNat 53876598143118755132), (Int.ofNat 6034328389687966074), (Int.negOfNat 225096470256233146), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(2310902269904155650059728626108161/5629499534213120000000000000000000), (72989401605099869461546786487257/1407374883553280000000000000000000), (5555858281494369105086955934677/5629499534213120000000000000000000), (672194520624573301617258165399/1407374883553280000000000000000000), (-49414115823089986063585561729/703687441776640000000000000000000), (-123126801052314383881932491531/5629499534213120000000000000000000), (13653193131351871658853449883/5629499534213120000000000000000000), (531215387590915440391322139/1125899906842624000000000000000000), (-221920313495994828250375823/5629499534213120000000000000000000), (-1038311288449152182954247/175921860444160000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial161.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial161.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial161.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 2929428651411450988858370281777994), (Int.ofNat 327467043733104968824956098484642), (Int.ofNat 6892181913978342468640741266825), (Int.negOfNat 2261722868851725288892709064490), (Int.negOfNat 409003840667804524959928628580), (Int.ofNat 120415649019222821597841629194), (Int.ofNat 13586177092663668286845357818), (Int.negOfNat 2719437965038074476345844088), (Int.negOfNat 238895935007924683100561392), (Int.ofNat 33041787973227419924751636), (Int.ofNat 2541689430253265926034438), (Int.negOfNat 247833791964546913877467), (Int.negOfNat 17711122563829945387691), (Int.ofNat 1259098572710906217622), (Int.ofNat 86152549525927017084), (Int.negOfNat 4622935319740905104), (Int.negOfNat 282776523860732833), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(1464714325705725494429185140888997/2814749767106560000000000000000000), (163733521866552484412478049242321/2814749767106560000000000000000000), (275687276559133698745629650673/225179981368524800000000000000000), (-226172286885172528889270906449/562949953421312000000000000000000), (-20450192033390226247996431429/281474976710656000000000000000000), (60207824509611410798920814597/2814749767106560000000000000000000), (6793088546331834143422678909/2814749767106560000000000000000000), (-339929745629759309543230511/703687441776640000000000000000000), (-14930995937995292693785087/351843720888320000000000000000000), (8260446993306854981187909/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial161.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial161.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial161.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 3591626144347554006553190111471007), (Int.ofNat 325671824833686661166774413529146), (Int.negOfNat 5682287349970819863942485836752), (Int.negOfNat 289693515930851422702561568360), (Int.ofNat 736523350077424676377104039266), (Int.ofNat 26463049049146302135901549240), (Int.negOfNat 24880768502198962410237034697), (Int.negOfNat 934211903684883086866806844), (Int.ofNat 409703556514324985224698263), (Int.ofNat 16260178928017981588510564), (Int.negOfNat 3890640458466952843843585), (Int.negOfNat 160749730401933541674311), (Int.ofNat 23849369382005747672613), (Int.ofNat 1005051044773178575163), (Int.negOfNat 102625648944043609279), (Int.negOfNat 4414619252841863704), (Int.ofNat 406492488325952416), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(3591626144347554006553190111471007/5629499534213120000000000000000000), (162835912416843330583387206764573/2814749767106560000000000000000000), (-355142959373176241496405364797/351843720888320000000000000000000), (-7242337898271285567564039209/140737488355328000000000000000000), (368261675038712338188552019633/2814749767106560000000000000000000), (661576226228657553397538731/140737488355328000000000000000000), (-24880768502198962410237034697/5629499534213120000000000000000000), (-233552975921220771716701711/1407374883553280000000000000000000), (409703556514324985224698263/5629499534213120000000000000000000), (4065044732004495397127641/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial161.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial161.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial161.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 4228951339555017738697155015545272), (Int.ofNat 320392405966444384254778836823612), (Int.ofNat 6535480833797080483507948566095), (Int.ofNat 2914884434764274132939876451926), (Int.negOfNat 284647566130619016375761132955), (Int.negOfNat 167746011809467883465863405069), (Int.ofNat 4948795072573578269170020186), (Int.ofNat 4043407304807969842815727750), (Int.negOfNat 1946663884219604052063971), (Int.negOfNat 50872540505176076283532127), (Int.negOfNat 701287567173568435746469), (Int.ofNat 384377068290176670405580), (Int.ofNat 7983533604803428886071), (Int.negOfNat 1956259479847342848361), (Int.negOfNat 47732951542601287146), (Int.ofNat 7332708849818787588), (Int.ofNat 190659482974145312), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(528618917444377217337144376943159/703687441776640000000000000000000), (80098101491611096063694709205903/1407374883553280000000000000000000), (1307096166759416096701589713219/1125899906842624000000000000000000), (1457442217382137066469938225963/2814749767106560000000000000000000), (-56929513226123803275152226591/1125899906842624000000000000000000), (-167746011809467883465863405069/5629499534213120000000000000000000), (2474397536286789134585010093/2814749767106560000000000000000000), (16173629219231879371262911/22517998136852480000000000000000), (-1946663884219604052063971/5629499534213120000000000000000000), (-50872540505176076283532127/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial161.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial161.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial161.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 4910082736022532283260291588605071), (Int.ofNat 361627778311102024247841170914094), (Int.ofNat 7443497344261204978440807171567), (Int.negOfNat 3287231246516921067931577317278), (Int.negOfNat 733245613001744008433759847666), (Int.ofNat 133704042813364842386670192252), (Int.ofNat 30503790716388755090260632128), (Int.negOfNat 1977935206590943408767282148), (Int.negOfNat 556677262307222296270133003), (Int.ofNat 10746664280796552066742021), (Int.ofNat 5362370131299293800772775), (Int.negOfNat 5928250974704937918490), (Int.negOfNat 32741576724849880808615), (Int.negOfNat 247150811827390251377), (Int.ofNat 140141456481158290674), (Int.ofNat 1747955184239291016), (Int.negOfNat 506322032685755642), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(4910082736022532283260291588605071/5629499534213120000000000000000000), (180813889155551012123920585457047/2814749767106560000000000000000000), (7443497344261204978440807171567/5629499534213120000000000000000000), (-1643615623258460533965788658639/2814749767106560000000000000000000), (-366622806500872004216879923833/2814749767106560000000000000000000), (33426010703341210596667548063/1407374883553280000000000000000000), (476621729943574298285322377/87960930222080000000000000000000), (-494483801647735852191820537/1407374883553280000000000000000000), (-556677262307222296270133003/5629499534213120000000000000000000), (10746664280796552066742021/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial161.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial161.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial161.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 5630928436536941275637986137491722), (Int.ofNat 343639379178170268789254426277224), (Int.negOfNat 14078361024024958645173488576932), (Int.negOfNat 893402379505617772993634232346), (Int.ofNat 1367777937954090756095056149057), (Int.ofNat 145688045959504102834201753568), (Int.negOfNat 36265465182971054013120825155), (Int.negOfNat 5015841306106202537141498468), (Int.ofNat 351543192561887919141569061), (Int.ofNat 65105437479521716322072162), (Int.negOfNat 1799364346414226153260631), (Int.negOfNat 486297295392886181608369), (Int.ofNat 5079584262867265741607), (Int.ofNat 2445400449590748069585), (Int.negOfNat 4443412068579149659), (Int.negOfNat 9148089232791049360), (Int.negOfNat 48627669907656178), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(2815464218268470637818993068745861/2814749767106560000000000000000000), (42954922397271283598656803284653/703687441776640000000000000000000), (-3519590256006239661293372144233/1407374883553280000000000000000000), (-446701189752808886496817116173/2814749767106560000000000000000000), (1367777937954090756095056149057/5629499534213120000000000000000000), (4552751436234503213568804799/175921860444160000000000000000000), (-7253093036594210802624165031/1125899906842624000000000000000000), (-1253960326526550634285374617/1407374883553280000000000000000000), (351543192561887919141569061/5629499534213120000000000000000000), (32552718739760858161036081/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial161.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial161.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial161.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 6278450509802282955835481179642577), (Int.ofNat 323314523061371184136453639371241), (Int.ofNat 13864854818588078347730378007939), (Int.ofNat 8198058401070394872886855683365), (Int.negOfNat 142687015632504015468414802064), (Int.negOfNat 449684627071097834121999232147), (Int.negOfNat 35787532289286800599676369114), (Int.ofNat 6069786759136283161121389566), (Int.ofNat 690516139204255549772557600), (Int.negOfNat 44008959641133879351202380), (Int.negOfNat 6450355846817200833017306), (Int.ofNat 204954237503140438185847), (Int.ofNat 38375352965617560985905), (Int.negOfNat 662239752197015090814), (Int.negOfNat 162193257510838832456), (Int.ofNat 1475483881815415120), (Int.ofNat 535135670512314301), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(6278450509802282955835481179642577/5629499534213120000000000000000000), (323314523061371184136453639371241/5629499534213120000000000000000000), (13864854818588078347730378007939/5629499534213120000000000000000000), (1639611680214078974577371136673/1125899906842624000000000000000000), (-8917938477031500966775925129/351843720888320000000000000000000), (-449684627071097834121999232147/5629499534213120000000000000000000), (-17893766144643400299838184557/2814749767106560000000000000000000), (3034893379568141580560694783/2814749767106560000000000000000000), (863145174005319437215697/7036874417766400000000000000000), (-2200447982056693967560119/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial161.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial161.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial161.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 7028085276046607477728800176831450), (Int.ofNat 433033811335096799133410022524517), (Int.ofNat 20112340401653944805516603759558), (Int.negOfNat 12343341745275443934364232922330), (Int.negOfNat 4564883994403003394132287273348), (Int.negOfNat 191084033426840283875185713668), (Int.ofNat 80317499889423724238084978124), (Int.ofNat 6504682696781895616649514557), (Int.negOfNat 743769173706444687450874141), (Int.negOfNat 77140102417837606623489172), (Int.ofNat 4471423398334633494679113), (Int.ofNat 546168188048204558251908), (Int.negOfNat 19149047430192747828022), (Int.negOfNat 2664210654040443949232), (Int.ofNat 61826640184658183002), (Int.ofNat 9712741651970004030), (Int.negOfNat 132768348162063092), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(140561705520932149554576003536629/112589990684262400000000000000000), (433033811335096799133410022524517/5629499534213120000000000000000000), (10056170200826972402758301879779/2814749767106560000000000000000000), (-1234334174527544393436423292233/562949953421312000000000000000000), (-1141220998600750848533071818337/1407374883553280000000000000000000), (-47771008356710070968796428417/1407374883553280000000000000000000), (20079374972355931059521244531/1407374883553280000000000000000000), (6504682696781895616649514557/5629499534213120000000000000000000), (-743769173706444687450874141/5629499534213120000000000000000000), (-19285025604459401655872293/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial161.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial161.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial161.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 7802451310463737854356044733985995), (Int.ofNat 221424211501225488503136782721332), (Int.negOfNat 156767395787480937365601883338808), (Int.negOfNat 41671015286262816329197391330035), (Int.negOfNat 899560781323017835246884367484), (Int.ofNat 879874772749994617073507559931), (Int.ofNat 57693932939508206842075554551), (Int.negOfNat 10063802517306001054219392407), (Int.negOfNat 848905741563924650054313820), (Int.ofNat 74920518187380270895406897), (Int.ofNat 7109021464155207724310495), (Int.negOfNat 395439154708776806604453), (Int.negOfNat 40061280647089903590489), (Int.ofNat 1563059027108455530832), (Int.ofNat 164243263867853433600), (Int.negOfNat 4665502952812198086), (Int.negOfNat 503483968982299870), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(1560490262092747570871208946797199/1125899906842624000000000000000000), (55356052875306372125784195680333/1407374883553280000000000000000000), (-19595924473435117170700235417351/703687441776640000000000000000000), (-8334203057252563265839478266007/1125899906842624000000000000000000), (-224890195330754458811721091871/1407374883553280000000000000000000), (879874772749994617073507559931/5629499534213120000000000000000000), (57693932939508206842075554551/5629499534213120000000000000000000), (-10063802517306001054219392407/5629499534213120000000000000000000), (-42445287078196232502715691/281474976710656000000000000000000), (74920518187380270895406897/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial161.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial161.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial161.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 7300856653668299969422157913541988), (Int.negOfNat 858190469228151964938473907435458), (Int.negOfNat 352016942489821349107189379562433), (Int.negOfNat 11107129416629872866102807373838), (Int.ofNat 7968752174785044333032965662979), (Int.ofNat 539810385034407097916478831565), (Int.negOfNat 111805679635098667630480520922), (Int.negOfNat 8903139027602594275434973568), (Int.ofNat 1030498694850435314927879412), (Int.ofNat 85807001728285664594223018), (Int.negOfNat 6643814298378067162265590), (Int.negOfNat 553972395641379018967994), (Int.ofNat 31518237069118859789893), (Int.ofNat 2575256544778304663875), (Int.negOfNat 114241715024894477165), (Int.negOfNat 9046986149664153946), (Int.ofNat 314164366231782362), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(1825214163417074992355539478385497/1407374883553280000000000000000000), (-429095234614075982469236953717729/2814749767106560000000000000000000), (-352016942489821349107189379562433/5629499534213120000000000000000000), (-5553564708314936433051403686919/2814749767106560000000000000000000), (7968752174785044333032965662979/5629499534213120000000000000000000), (107962077006881419583295766313/1125899906842624000000000000000000), (-55902839817549333815240260461/2814749767106560000000000000000000), (-69555773653145267776835731/43980465111040000000000000000000), (257624673712608828731969853/1407374883553280000000000000000000), (42903500864142832297111509/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial161.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial161.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial161.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 4224329662848524003839580479571051), (Int.negOfNat 2125600618238362759589595472179294), (Int.negOfNat 214888700878825773288141692618661), (Int.ofNat 53547344308098208406845719710442), (Int.ofNat 5557873310919118674135780376880), (Int.negOfNat 981124424829630384448137948477), (Int.negOfNat 91562860900065365676762205022), (Int.ofNat 11656890003338352674416513574), (Int.ofNat 975509123490037699309139106), (Int.negOfNat 93619891347719942610295636), (Int.negOfNat 7099528901625556132696452), (Int.ofNat 536885599999763191641253), (Int.ofNat 37182504177597190543826), (Int.negOfNat 2297579709430057012723), (Int.negOfNat 146379744662649949898), (Int.ofNat 7523580001562405332), (Int.ofNat 471832267452285439), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(4224329662848524003839580479571051/5629499534213120000000000000000000), (-1062800309119181379794797736089647/2814749767106560000000000000000000), (-214888700878825773288141692618661/5629499534213120000000000000000000), (26773672154049104203422859855221/2814749767106560000000000000000000), (69473416386488983426697254711/70368744177664000000000000000000), (-981124424829630384448137948477/5629499534213120000000000000000000), (-45781430450032682838381102511/2814749767106560000000000000000000), (5828445001669176337208256787/2814749767106560000000000000000000), (487754561745018849654569553/2814749767106560000000000000000000), (-23404972836929985652573909/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial161.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial161.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial161.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 404689814539141080965638302021112), (Int.negOfNat 2254829384879021309872714602517317), (Int.ofNat 148404856700614953640999503065643), (Int.ofNat 51805017933186640220173910182896), (Int.negOfNat 5837113214652360891604057885704), (Int.negOfNat 890896200609726516864181311367), (Int.ofNat 103665290527671571469998053957), (Int.ofNat 10443456753265146466121380480), (Int.negOfNat 1099670323033960140299306507), (Int.negOfNat 84763457937402388953586419), (Int.ofNat 7829289044236575201279250), (Int.ofNat 495779172716374539014365), (Int.negOfNat 40029995955359371047044), (Int.negOfNat 2168097247821168431824), (Int.ofNat 154228193448698508388), (Int.ofNat 7228295851858495825), (Int.negOfNat 485009817124830155), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-50586226817392635120704787752639/703687441776640000000000000000000), (-2254829384879021309872714602517317/5629499534213120000000000000000000), (148404856700614953640999503065643/5629499534213120000000000000000000), (3237813620824165013760869386431/351843720888320000000000000000000), (-729639151831545111450507235713/703687441776640000000000000000000), (-890896200609726516864181311367/5629499534213120000000000000000000), (103665290527671571469998053957/5629499534213120000000000000000000), (16317901176976791353314657/8796093022208000000000000000000), (-1099670323033960140299306507/5629499534213120000000000000000000), (-84763457937402388953586419/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial161.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial161.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial161.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial161.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial161.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial161.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial161.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial161.reflect := by
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

end Bin161
end
end ErdosOverlap.OuterNumerics
