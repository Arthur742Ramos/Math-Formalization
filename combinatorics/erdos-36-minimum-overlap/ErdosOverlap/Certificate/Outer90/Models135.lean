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

/-! # Exact integer weighted outer models for source bin 135

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin135

def weightDenominator : ℤ := (Int.ofNat 5000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 1757422491250445200)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1587124311750831500)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 1135915536510205150)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 650523051207778500)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 341431104527005350)⟩, ⟨(19494472361809/1000000000000), (Int.negOfNat 256721977885093950)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 404533319574761150)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 163473982093910300)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 35178389886168075)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial135.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial135.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 4920987327424348500)⟩, ⟨(314159265359/50000000000), (Int.ofNat 819960818735296100)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 844493988820903500)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 289227030903111500)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 50051369510615875)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 75738882115021465)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 51745023896452205)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 6509240468836223)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 2013207677640753)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial135.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial135.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4920987327424348500)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 819960818735296100)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 844493988820903500)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 289227030903111500)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 50051369510615875)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 75738882115021465)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 51745023896452205)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 6509240468836223)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 2013207677640753)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial135.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial135.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial135.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 5383563534842638668422800558121675), (Int.ofNat 2272584466199585166304403625884967), (Int.ofNat 472057869338073275985834538876903), (Int.negOfNat 67489403408438152244372598966681), (Int.negOfNat 11884047663803705979572360756842), (Int.ofNat 1254781142990585957659054007773), (Int.ofNat 163566804844295568796777664818), (Int.negOfNat 14320516514375299711744225931), (Int.negOfNat 1417777171527959923784967928), (Int.ofNat 108558957663562864082697178), (Int.ofNat 8453507096474138664516679), (Int.negOfNat 585500874730983537304242), (Int.negOfNat 36979659010685293175369), (Int.ofNat 2364483921385754582622), (Int.ofNat 123959117535423323130), (Int.negOfNat 7254983353121506063), (Int.negOfNat 320777444990069934), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-215342541393705546736912022324867/225179981368524800000000000000000), (2272584466199585166304403625884967/5629499534213120000000000000000000), (472057869338073275985834538876903/5629499534213120000000000000000000), (-67489403408438152244372598966681/5629499534213120000000000000000000), (-5942023831901852989786180378421/2814749767106560000000000000000000), (1254781142990585957659054007773/5629499534213120000000000000000000), (81783402422147784398388832409/2814749767106560000000000000000000), (-14320516514375299711744225931/5629499534213120000000000000000000), (-177222146440994990473120991/703687441776640000000000000000000), (54279478831781432041348589/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial135.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial135.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial135.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial135 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 368265089185617068527832373741979), (Int.ofNat 3094859536255786167344596471074827), (Int.negOfNat 90042159947457008126864653252314), (Int.negOfNat 96074664193082072264857261221503), (Int.ofNat 5402994513349628494607184284237), (Int.ofNat 1646339498553245820029982216799), (Int.negOfNat 104605192265253030620378628767), (Int.negOfNat 16985203377988202801993502552), (Int.ofNat 1106504470439030996170240135), (Int.ofNat 116016689713658099594993224), (Int.negOfNat 7619789247739289249904655), (Int.negOfNat 564890915176126979165765), (Int.ofNat 37331672533350902811757), (Int.ofNat 2071906078844833682946), (Int.negOfNat 137624464658194511978), (Int.negOfNat 5753447697811260005), (Int.ofNat 424284782476486060), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(368265089185617068527832373741979/5629499534213120000000000000000000), (3094859536255786167344596471074827/5629499534213120000000000000000000), (-45021079973728504063432326626157/2814749767106560000000000000000000), (-96074664193082072264857261221503/5629499534213120000000000000000000), (5402994513349628494607184284237/5629499534213120000000000000000000), (1646339498553245820029982216799/5629499534213120000000000000000000), (-104605192265253030620378628767/5629499534213120000000000000000000), (-2123150422248525350249187819/703687441776640000000000000000000), (221300894087806199234048027/1125899906842624000000000000000000), (14502086214207262449374153/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial135.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial135.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial135.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial135 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 5559814019784286141406785331185430), (Int.ofNat 1860060339986677798826026928980183), (Int.negOfNat 439213847637591865667810534300903), (Int.negOfNat 10775311834105101386411073321261), (Int.ofNat 12420349114050481454746880394986), (Int.negOfNat 379913160115358450571404937154), (Int.negOfNat 171914861329548184001663867235), (Int.ofNat 8233647700882346365681894426), (Int.ofNat 1428683337266184075005798724), (Int.negOfNat 81324702799018616592292795), (Int.negOfNat 7999958820094798301579289), (Int.ofNat 509144064491973084299243), (Int.ofNat 32520738959359507349793), (Int.negOfNat 2260283281796761614996), (Int.negOfNat 100876640208013084270), (Int.ofNat 7585557203633019945), (Int.ofNat 213229067653924956), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(555981401978428614140678533118543/562949953421312000000000000000000), (1860060339986677798826026928980183/5629499534213120000000000000000000), (-439213847637591865667810534300903/5629499534213120000000000000000000), (-10775311834105101386411073321261/5629499534213120000000000000000000), (6210174557025240727373440197493/2814749767106560000000000000000000), (-189956580057679225285702468577/2814749767106560000000000000000000), (-34382972265909636800332773447/1125899906842624000000000000000000), (4116823850441173182840947213/2814749767106560000000000000000000), (357170834316546018751449681/1407374883553280000000000000000000), (-16264940559803723318458559/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial135.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial135.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial135.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial135 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 7613813603768284243977519601710113), (Int.ofNat 312881391153754526423277701056940), (Int.negOfNat 269787507827509119883446058635584), (Int.ofNat 52519986261296765541799391597096), (Int.ofNat 1801170722780296299008350099547), (Int.negOfNat 1322149366972443309022456238184), (Int.ofNat 30735732140981131955485526022), (Int.ofNat 14935209982711572272801598819), (Int.negOfNat 651247871887385070159962052), (Int.negOfNat 101754120415249889438065272), (Int.ofNat 5797582108182999263307452), (Int.ofNat 473151190651315546722478), (Int.negOfNat 32495697301822056963474), (Int.negOfNat 1613526296368444207390), (Int.ofNat 129666190787641728122), (Int.ofNat 3912585064441792755), (Int.negOfNat 418245159443563801), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(7613813603768284243977519601710113/5629499534213120000000000000000000), (15644069557687726321163885052847/281474976710656000000000000000000), (-4215429809804829998178844666181/87960930222080000000000000000000), (6564998282662095692724923949637/703687441776640000000000000000000), (1801170722780296299008350099547/5629499534213120000000000000000000), (-165268670871555413627807029773/703687441776640000000000000000000), (15367866070490565977742763011/2814749767106560000000000000000000), (14935209982711572272801598819/5629499534213120000000000000000000), (-162811967971846267539990513/1407374883553280000000000000000000), (-12719265051906236179758159/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial135.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial135.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial135.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial135 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 7570762934498989686702984516267856), (Int.negOfNat 172438231571158314497388327785580), (Int.negOfNat 1356615342609871513161727837089), (Int.ofNat 25715752286274826966079250530054), (Int.negOfNat 6440651957670573986856795609413), (Int.negOfNat 138600163595408029096693530059), (Int.ofNat 122816123329533123154378230280), (Int.negOfNat 3012711119252720608243068726), (Int.negOfNat 1111479094022975420899042860), (Int.ofNat 51693050146457894605719950), (Int.ofNat 6206603209265974023294753), (Int.negOfNat 398184162278736685502110), (Int.negOfNat 23880973827851357461064), (Int.ofNat 1965396378781004544811), (Int.ofNat 67203065733294988949), (Int.negOfNat 7252229034251780014), (Int.negOfNat 107693897995420731), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(473172683406186855418936532266741/351843720888320000000000000000000), (-8621911578557915724869416389279/281474976710656000000000000000000), (-1356615342609871513161727837089/5629499534213120000000000000000000), (12857876143137413483039625265027/2814749767106560000000000000000000), (-6440651957670573986856795609413/5629499534213120000000000000000000), (-138600163595408029096693530059/5629499534213120000000000000000000), (3070403083238328078859455757/140737488355328000000000000000000), (-1506355559626360304121534363/2814749767106560000000000000000000), (-55573954701148771044952143/281474976710656000000000000000000), (1033861002929157892114399/112589990684262400000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial135.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial135.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial135.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial135 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 7325922384005082509429719399776126), (Int.negOfNat 65225777630482372076051444614098), (Int.ofNat 13031003010597159238999377047006), (Int.negOfNat 15027440848146993992354358448782), (Int.negOfNat 2273336243515584954118936458813), (Int.ofNat 724945782242578239193388174149), (Int.ofNat 4910179126937807277170025309), (Int.negOfNat 9868491404838649397771160297), (Int.ofNat 309318269087033569073532899), (Int.ofNat 70657864885573485386693251), (Int.negOfNat 3980962056881749992894928), (Int.negOfNat 319657614041197351379091), (Int.ofNat 25880010983581083894663), (Int.ofNat 989222442854684597327), (Int.negOfNat 111366818431966197121), (Int.negOfNat 2041629804852804415), (Int.ofNat 412205536410641542), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(3662961192002541254714859699888063/2814749767106560000000000000000000), (-32612888815241186038025722307049/2814749767106560000000000000000000), (6515501505298579619499688523503/2814749767106560000000000000000000), (-7513720424073496996177179224391/2814749767106560000000000000000000), (-2273336243515584954118936458813/5629499534213120000000000000000000), (724945782242578239193388174149/5629499534213120000000000000000000), (4910179126937807277170025309/5629499534213120000000000000000000), (-9868491404838649397771160297/5629499534213120000000000000000000), (309318269087033569073532899/5629499534213120000000000000000000), (70657864885573485386693251/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial135.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial135.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial135.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial135 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 7113362027080552342276850075414044), (Int.negOfNat 211204252649493219389560265222769), (Int.negOfNat 78324340539928278355620912329208), (Int.negOfNat 8094401374460295552962892662164), (Int.ofNat 3075401527432620119312321982365), (Int.ofNat 197213470265454029127339065654), (Int.negOfNat 67565213436745565805988054732), (Int.ofNat 460022249959458561259111132), (Int.ofNat 666356600912939585872859994), (Int.negOfNat 29723844789132075503028277), (Int.negOfNat 3728165906713457725700987), (Int.ofNat 287205840251093689525192), (Int.ofNat 13113010062039093963533), (Int.negOfNat 1563465442853172664313), (Int.negOfNat 28899941515507954291), (Int.ofNat 5962637504617366139), (Int.ofNat 2158728336916506), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(1778340506770138085569212518853511/1407374883553280000000000000000000), (-211204252649493219389560265222769/5629499534213120000000000000000000), (-9790542567491034794452614041151/703687441776640000000000000000000), (-2023600343615073888240723165541/1407374883553280000000000000000000), (615080305486524023862464396473/1125899906842624000000000000000000), (98606735132727014563669532827/2814749767106560000000000000000000), (-16891303359186391451497013683/1407374883553280000000000000000000), (115005562489864640314777783/1407374883553280000000000000000000), (333178300456469792936429997/2814749767106560000000000000000000), (-29723844789132075503028277/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial135.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial135.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial135.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial135 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 6364305093158930457891574453348946), (Int.negOfNat 519612686388999405068008864728120), (Int.negOfNat 52187637286865868215009681385093), (Int.ofNat 14834718968731482434052400664965), (Int.ofNat 1712003388428316798419593109841), (Int.negOfNat 357092237561637791163361036751), (Int.negOfNat 14323429975982418253320315940), (Int.ofNat 4936260931730843456909554955), (Int.negOfNat 122033645979439249408293974), (Int.negOfNat 35952651570568433457649903), (Int.ofNat 2547790556856206928049014), (Int.ofNat 149213367449548754483112), (Int.negOfNat 18922447324389512856636), (Int.negOfNat 336735442883754817406), (Int.ofNat 85960170077703153466), (Int.ofNat 17475718558878435), (Int.negOfNat 370987523491551208), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(3182152546579465228945787226674473/2814749767106560000000000000000000), (-12990317159724985126700221618203/140737488355328000000000000000000), (-52187637286865868215009681385093/5629499534213120000000000000000000), (2966943793746296486810480132993/1125899906842624000000000000000000), (1712003388428316798419593109841/5629499534213120000000000000000000), (-357092237561637791163361036751/5629499534213120000000000000000000), (-716171498799120912666015797/281474976710656000000000000000000), (987252186346168691381910991/1125899906842624000000000000000000), (-61016822989719624704146987/2814749767106560000000000000000000), (-35952651570568433457649903/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial135.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial135.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial135.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial135 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 5250640354766243252237948481680247), (Int.negOfNat 524862077272346987408735145913764), (Int.ofNat 48868820351592580790719021200805), (Int.ofNat 14350918239859538973272926996631), (Int.negOfNat 1579699773652337794511082922702), (Int.negOfNat 218464572151472393374075063607), (Int.ofNat 26594331213548217123161038842), (Int.ofNat 560279629988932739132609297), (Int.negOfNat 261526656328732369985276096), (Int.ofNat 15863317003637110096757527), (Int.ofNat 1327816632706091908084238), (Int.negOfNat 190850182893455160414942), (Int.negOfNat 2824361354527181849862), (Int.ofNat 1118221939941776703778), (Int.negOfNat 5575888881373509174), (Int.negOfNat 4587964415911165721), (Int.ofNat 64171636080138138), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(5250640354766243252237948481680247/5629499534213120000000000000000000), (-131215519318086746852183786478441/1407374883553280000000000000000000), (9773764070318516158143804240161/1125899906842624000000000000000000), (14350918239859538973272926996631/5629499534213120000000000000000000), (-789849886826168897255541461351/2814749767106560000000000000000000), (-218464572151472393374075063607/5629499534213120000000000000000000), (13297165606774108561580519421/2814749767106560000000000000000000), (560279629988932739132609297/5629499534213120000000000000000000), (-4086354005136443281019939/87960930222080000000000000000000), (15863317003637110096757527/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial135.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial135.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial135.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial135 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 4480648655229155935100912389601811), (Int.negOfNat 220072835717552437245719701132324), (Int.ofNat 85957863443425029109775610794233), (Int.negOfNat 2827456581751534718352257675448), (Int.negOfNat 2230937664599339187542035991390), (Int.ofNat 67675742160204010366186289812), (Int.ofNat 17511349054517213492953459170), (Int.negOfNat 1030575128761952717776896474), (Int.ofNat 30493831704130885636310002), (Int.ofNat 6673171978247323944666883), (Int.negOfNat 1503339019756861763119913), (Int.negOfNat 3194617268111457574652), (Int.ofNat 12331854231164167126837), (Int.negOfNat 207897130115518130429), (Int.negOfNat 58131015457743233911), (Int.ofNat 1552326366258778597), (Int.ofNat 296604328363933552), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(4480648655229155935100912389601811/5629499534213120000000000000000000), (-55018208929388109311429925283081/1407374883553280000000000000000000), (85957863443425029109775610794233/5629499534213120000000000000000000), (-353432072718941839794032209431/703687441776640000000000000000000), (-223093766459933918754203599139/562949953421312000000000000000000), (16918935540051002591546572453/1407374883553280000000000000000000), (1751134905451721349295345917/562949953421312000000000000000000), (-515287564380976358888448237/2814749767106560000000000000000000), (15246915852065442818155001/2814749767106560000000000000000000), (6673171978247323944666883/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial135.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial135.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial135.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial135 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 4329183943794217321705130536420100), (Int.ofNat 26792827935430896595051910987124), (Int.ofNat 24443623370769071029864685752269), (Int.negOfNat 15674652298620914332739549219182), (Int.negOfNat 749908364892872130830859465310), (Int.ofNat 207268761739625386583228661339), (Int.ofNat 6528615584606061705162995617), (Int.negOfNat 774229001167769388904630485), (Int.negOfNat 44517551994748864813401889), (Int.negOfNat 7787954087328194565210155), (Int.ofNat 496430639119161172245418), (Int.ofNat 111495916889373155658661), (Int.negOfNat 4867286481876659778781), (Int.negOfNat 674798693188437780239), (Int.ofNat 30776819184621482699), (Int.ofNat 2566639993528106501), (Int.negOfNat 93310402933383954), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(43291839437942173217051305364201/56294995342131200000000000000000), (6698206983857724148762977746781/1407374883553280000000000000000000), (24443623370769071029864685752269/5629499534213120000000000000000000), (-7837326149310457166369774609591/2814749767106560000000000000000000), (-74990836489287213083085946531/562949953421312000000000000000000), (207268761739625386583228661339/5629499534213120000000000000000000), (6528615584606061705162995617/5629499534213120000000000000000000), (-154845800233553877780926097/1125899906842624000000000000000000), (-44517551994748864813401889/5629499534213120000000000000000000), (-1557590817465638913042031/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial135.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial135.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial135.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial135 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 4350084999254584626987668749894514), (Int.negOfNat 70097316602062042661052307815856), (Int.negOfNat 70081231567392374053826269740294), (Int.negOfNat 12882186209252684983164541357798), (Int.ofNat 1427006600219284287172642251162), (Int.ofNat 191554635469928716725034585791), (Int.negOfNat 11620860547935071380818169307), (Int.negOfNat 1723363190383407124815237242), (Int.negOfNat 7000790288729892784061488), (Int.ofNat 12948043352895649510592514), (Int.ofNat 779985164350579570621149), (Int.negOfNat 92077347855861276999160), (Int.negOfNat 6476245932869515620028), (Int.ofNat 545239797044940131001), (Int.ofNat 29933850475152792549), (Int.negOfNat 2640597128129117172), (Int.negOfNat 191069158705429327), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(2175042499627292313493834374947257/2814749767106560000000000000000000), (-4381082287628877666315769238491/351843720888320000000000000000000), (-35040615783696187026913134870147/2814749767106560000000000000000000), (-6441093104626342491582270678899/2814749767106560000000000000000000), (713503300109642143586321125581/2814749767106560000000000000000000), (191554635469928716725034585791/5629499534213120000000000000000000), (-11620860547935071380818169307/5629499534213120000000000000000000), (-861681595191703562407618621/2814749767106560000000000000000000), (-437549393045618299003843/351843720888320000000000000000000), (6474021676447824755296257/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial135.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial135.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial135.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial135 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 3854510904160281944605814491189530), (Int.negOfNat 446997674716988857083326667007766), (Int.negOfNat 101695756034882027585460695158162), (Int.ofNat 3436233273848016201992598700254), (Int.ofNat 2213121435336510757119123142931), (Int.negOfNat 66578142534151396133758469554), (Int.negOfNat 26818327673176122577886581029), (Int.ofNat 196332796336022333173388023), (Int.ofNat 219651216392136592116511276), (Int.ofNat 4189992609525500898124266), (Int.negOfNat 1488030627564927233841414), (Int.negOfNat 49537036411361334701158), (Int.ofNat 8726864643745414553000), (Int.ofNat 270800734228586569872), (Int.negOfNat 41183238534336426248), (Int.negOfNat 779042704955615041), (Int.ofNat 87270779900461695), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(385451090416028194460581449118953/562949953421312000000000000000000), (-223498837358494428541663333503883/2814749767106560000000000000000000), (-50847878017441013792730347579081/2814749767106560000000000000000000), (1718116636924008100996299350127/2814749767106560000000000000000000), (2213121435336510757119123142931/5629499534213120000000000000000000), (-33289071267075698066879234777/2814749767106560000000000000000000), (-26818327673176122577886581029/5629499534213120000000000000000000), (196332796336022333173388023/5629499534213120000000000000000000), (54912804098034148029127819/1407374883553280000000000000000000), (2094996304762750449062133/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial135.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial135.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial135.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial135 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 2612867384860599659961565629759616), (Int.negOfNat 751886803014304590619846534045290), (Int.negOfNat 39199153924694428968045421728212), (Int.ofNat 14689315034784091508273540585727), (Int.ofNat 235186305455073671842920078430), (Int.negOfNat 277589688320472963054749905198), (Int.negOfNat 1842678276972732727570667913), (Int.ofNat 2856104086463177302725185432), (Int.ofNat 33877430828616872048642442), (Int.negOfNat 20739766572799772220858209), (Int.negOfNat 328835945028965667066905), (Int.ofNat 124719167475247548569287), (Int.ofNat 1671037552663766919187), (Int.negOfNat 628772770873625483786), (Int.negOfNat 4603371302798357870), (Int.ofNat 2507829721150624841), (Int.ofNat 85533989046925102), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(20413026444223434843449731482497/43980465111040000000000000000000), (-75188680301430459061984653404529/562949953421312000000000000000000), (-9799788481173607242011355432053/1407374883553280000000000000000000), (14689315034784091508273540585727/5629499534213120000000000000000000), (23518630545507367184292007843/562949953421312000000000000000000), (-138794844160236481527374952599/2814749767106560000000000000000000), (-1842678276972732727570667913/5629499534213120000000000000000000), (357013010807897162840648179/703687441776640000000000000000000), (16938715414308436024321221/2814749767106560000000000000000000), (-20739766572799772220858209/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial135.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial135.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial135.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial135 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 1064937418446779244376221608406575), (Int.negOfNat 746180476230785700911631168482030), (Int.ofNat 33815968111761991639775156979142), (Int.ofNat 6721241730234271403864613047702), (Int.negOfNat 1896409564233453445834151116059), (Int.negOfNat 85422063214042209478374953936), (Int.ofNat 28702526871508710953765223521), (Int.ofNat 729847573346076642933536270), (Int.negOfNat 245506958378114495015345613), (Int.negOfNat 3644526037372750080025588), (Int.ofNat 1573073862825417318839531), (Int.ofNat 5666315348808005338825), (Int.negOfNat 8410729704041038300977), (Int.ofNat 57998371572873650152), (Int.ofNat 37195192503902424872), (Int.negOfNat 897933650291725209), (Int.negOfNat 81231156867539436), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(42597496737871169775048864336263/225179981368524800000000000000000), (-74618047623078570091163116848203/562949953421312000000000000000000), (16907984055880995819887578489571/2814749767106560000000000000000000), (3360620865117135701932306523851/2814749767106560000000000000000000), (-1896409564233453445834151116059/5629499534213120000000000000000000), (-5338878950877638092398434621/351843720888320000000000000000000), (28702526871508710953765223521/5629499534213120000000000000000000), (72984757334607664293353627/562949953421312000000000000000000), (-245506958378114495015345613/5629499534213120000000000000000000), (-911131509343187520006397/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial135.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial135.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial135.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial135 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 269598531302751153355422865952191), (Int.negOfNat 592194594941842008825698458371065), (Int.ofNat 28735880873466703017153040663758), (Int.negOfNat 7301842223386687796647038624453), (Int.negOfNat 1093411108622292743241266307176), (Int.ofNat 215035711659556449816950665164), (Int.ofNat 13885442670215755679807066336), (Int.negOfNat 2375006473274816408684723897), (Int.negOfNat 78364612972944312577871856), (Int.ofNat 16971959310677998245721106), (Int.ofNat 98089536398105881043265), (Int.negOfNat 96338121003861886164328), (Int.ofNat 1744786476929235102367), (Int.ofNat 462756289149459044200), (Int.negOfNat 14577158729440669840), (Int.negOfNat 1888550716503257273), (Int.ofNat 17987972933938370), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-269598531302751153355422865952191/5629499534213120000000000000000000), (-118438918988368401765139691674213/1125899906842624000000000000000000), (14367940436733351508576520331879/2814749767106560000000000000000000), (-7301842223386687796647038624453/5629499534213120000000000000000000), (-136676388577786592905158288397/703687441776640000000000000000000), (53758927914889112454237666291/1407374883553280000000000000000000), (433920083444242364993970823/175921860444160000000000000000000), (-2375006473274816408684723897/5629499534213120000000000000000000), (-4897788310809019536116991/351843720888320000000000000000000), (8485979655338999122860553/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial135.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial135.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial135.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial135 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 1407499160865837535769157592901625), (Int.negOfNat 581099134133486826407926221270648), (Int.negOfNat 22441301044889033255056613786944), (Int.negOfNat 6607468670633544268599922721206), (Int.ofNat 1203352569450901300624735439654), (Int.ofNat 179519778589538373060107887254), (Int.negOfNat 17641991195803119451533763586), (Int.negOfNat 1513588020429548519064669997), (Int.ofNat 146333055799709181590058006), (Int.ofNat 4668652775915116745317556), (Int.negOfNat 875396623214253634640265), (Int.ofNat 18775269478103830917172), (Int.ofNat 4427981453451058642783), (Int.negOfNat 275395237507529271850), (Int.negOfNat 19523268682235955410), (Int.ofNat 1815520231113617327), (Int.ofNat 6847961739921780), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-11259993286926700286153260743213/45035996273704960000000000000000), (-72637391766685853300990777658831/703687441776640000000000000000000), (-350645328826391144610259590421/87960930222080000000000000000000), (-3303734335316772134299961360603/2814749767106560000000000000000000), (601676284725450650312367719827/2814749767106560000000000000000000), (89759889294769186530053943627/2814749767106560000000000000000000), (-8820995597901559725766881793/2814749767106560000000000000000000), (-1513588020429548519064669997/5629499534213120000000000000000000), (73166527899854590795029003/2814749767106560000000000000000000), (1167163193978779186329389/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial135.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial135.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial135.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial135 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 2688607926081836736231099243952398), (Int.negOfNat 701194024193450414962627573369436), (Int.negOfNat 23820842610676514902040868409223), (Int.ofNat 6804896297057369675270507502401), (Int.ofNat 1688415986526369886694991058310), (Int.negOfNat 90516991119388992051947654008), (Int.negOfNat 21778609904426377217528840571), (Int.ofNat 835021186174259823833186470), (Int.ofNat 118988115890319745659220363), (Int.negOfNat 4755502073732769886749688), (Int.negOfNat 66558618334266094997181), (Int.ofNat 21004854818134008855925), (Int.negOfNat 3396179685811728367573), (Int.negOfNat 96826680002957347648), (Int.ofNat 26319934424837081528), (Int.ofNat 730575965808889541), (Int.negOfNat 84318337350993014), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-1344303963040918368115549621976199/2814749767106560000000000000000000), (-175298506048362603740656893342359/1407374883553280000000000000000000), (-23820842610676514902040868409223/5629499534213120000000000000000000), (6804896297057369675270507502401/5629499534213120000000000000000000), (168841598652636988669499105831/562949953421312000000000000000000), (-11314623889923624006493456751/703687441776640000000000000000000), (-21778609904426377217528840571/5629499534213120000000000000000000), (83502118617425982383318647/562949953421312000000000000000000), (118988115890319745659220363/5629499534213120000000000000000000), (-594437759216596235843711/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial135.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial135.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial135.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial135 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 4108981024052866526339616546863326), (Int.negOfNat 671727392991529261242551191799634), (Int.ofNat 45814330455878139706975159646747), (Int.ofNat 13861713827423715799414752750952), (Int.negOfNat 176017878537372625277996325357), (Int.negOfNat 238263513082385610633400898341), (Int.negOfNat 72130677678107655916981037), (Int.ofNat 2015961120896483659873079232), (Int.ofNat 23297531368156445875602558), (Int.negOfNat 6888542378511377762041109), (Int.negOfNat 316352325786412603187195), (Int.negOfNat 20080710078996144246413), (Int.ofNat 2055651208466587287013), (Int.ofNat 346647498540556732414), (Int.negOfNat 8111958291782175780), (Int.negOfNat 2146094081625131209), (Int.ofNat 100700415596223198), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-2054490512026433263169808273431663/2814749767106560000000000000000000), (-335863696495764630621275595899817/2814749767106560000000000000000000), (45814330455878139706975159646747/5629499534213120000000000000000000), (1732714228427964474926844093869/703687441776640000000000000000000), (-176017878537372625277996325357/5629499534213120000000000000000000), (-238263513082385610633400898341/5629499534213120000000000000000000), (-72130677678107655916981037/5629499534213120000000000000000000), (31499392514007557185516863/87960930222080000000000000000000), (11648765684078222937801279/2814749767106560000000000000000000), (-6888542378511377762041109/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial135.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial135.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial135.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial135 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 5168469986181972679487932837646342), (Int.negOfNat 345927649778267670791974010359699), (Int.ofNat 107042504361418418434695754934986), (Int.ofNat 4039760108193649770249905142752), (Int.negOfNat 2004919191602734953935483797814), (Int.negOfNat 76074505836945676629866113497), (Int.ofNat 24958564782220926959917551701), (Int.ofNat 1070713432937151016367136573), (Int.negOfNat 156593940220595185173588226), (Int.negOfNat 11119770681382000986605084), (Int.ofNat 287713999460087893387464), (Int.ofNat 79161325555961241233042), (Int.ofNat 2833065625177056530950), (Int.negOfNat 384693024239291289278), (Int.negOfNat 26717863218999908002), (Int.ofNat 1110286667560577709), (Int.ofNat 78278714318070755), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-2584234993090986339743966418823171/2814749767106560000000000000000000), (-345927649778267670791974010359699/5629499534213120000000000000000000), (53521252180709209217347877467493/2814749767106560000000000000000000), (126242503381051555320309535711/175921860444160000000000000000000), (-1002459595801367476967741898907/2814749767106560000000000000000000), (-76074505836945676629866113497/5629499534213120000000000000000000), (24958564782220926959917551701/5629499534213120000000000000000000), (1070713432937151016367136573/5629499534213120000000000000000000), (-78296970110297592586794113/2814749767106560000000000000000000), (-2779942670345500246651271/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial135.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial135.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial135.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial135 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 5432661195776415194869616438493247), (Int.ofNat 65564277516596346358365867849280), (Int.ofNat 83460427764866976095708449729100), (Int.negOfNat 10782047385976001234634578042325), (Int.negOfNat 1181164724720086667654464216412), (Int.ofNat 225595576148317807888562380031), (Int.ofNat 17141377721093169977406103832), (Int.negOfNat 2321235769374835256587264642), (Int.negOfNat 197574534240556616316602562), (Int.ofNat 11496061194242556155129064), (Int.ofNat 1646412026324694190064351), (Int.negOfNat 8753614110139939929060), (Int.negOfNat 9565466975183613861922), (Int.negOfNat 240215829523304149449), (Int.ofNat 39298028795664255051), (Int.ofNat 1812765912243891278), (Int.negOfNat 206235585254727423), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-5432661195776415194869616438493247/5629499534213120000000000000000000), (204888367239363582369893337029/17592186044416000000000000000000), (834604277648669760957084497291/56294995342131200000000000000000), (-431281895439040049385383121693/225179981368524800000000000000000), (-295291181180021666913616054103/1407374883553280000000000000000000), (225595576148317807888562380031/5629499534213120000000000000000000), (2142672215136646247175762979/703687441776640000000000000000000), (-1160617884687417628293632321/2814749767106560000000000000000000), (-98787267120278308158301281/2814749767106560000000000000000000), (1437007649280319519391133/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial135.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial135.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial135.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial135 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 5064870021486297872749470843453472), (Int.ofNat 252355284385345927334850932532228), (Int.ofNat 10738867903682389534419206962120), (Int.negOfNat 10033261118558287060004764280492), (Int.ofNat 1298898547453463177091668948001), (Int.ofNat 182984501764485170348487646730), (Int.negOfNat 24941176649001557840658575817), (Int.negOfNat 2542100729696590351554828935), (Int.ofNat 217045299634512347330069389), (Int.ofNat 25787000764606345885824095), (Int.negOfNat 897764178653246450480968), (Int.negOfNat 181432283386113599985039), (Int.ofNat 409108862028759062381), (Int.ofNat 892439830940849130861), (Int.ofNat 15501436211081949751), (Int.negOfNat 2981241927149566049), (Int.negOfNat 72239091285148496), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-158277188171446808523420963857921/175921860444160000000000000000000), (63088821096336481833712733133057/1407374883553280000000000000000000), (268471697592059738360480174053/140737488355328000000000000000000), (-2508315279639571765001191070123/1407374883553280000000000000000000), (1298898547453463177091668948001/5629499534213120000000000000000000), (18298450176448517034848764673/562949953421312000000000000000000), (-24941176649001557840658575817/5629499534213120000000000000000000), (-508420145939318070310965787/1125899906842624000000000000000000), (217045299634512347330069389/5629499534213120000000000000000000), (5157400152921269177164819/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial135.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial135.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial135.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial135 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 4572686328645748341464962350369934), (Int.ofNat 225462655142896653210388851760269), (Int.negOfNat 10850054250762241023795389338724), (Int.ofNat 2769578039850954753061637346091), (Int.ofNat 1248203909239009314647505492604), (Int.negOfNat 192886502162394641391178863771), (Int.negOfNat 24368114230227379789571676220), (Int.ofNat 2933641871373555715025724326), (Int.ofNat 320247171519965655251076998), (Int.negOfNat 21271356110570418446749767), (Int.negOfNat 2824548072887077477770587), (Int.ofNat 76374754547097682042498), (Int.ofNat 16797351382333112258613), (Int.negOfNat 58820996159575781829), (Int.negOfNat 70574793788736141039), (Int.negOfNat 779896360494571353), (Int.ofNat 311770754913231648), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-2286343164322874170732481175184967/2814749767106560000000000000000000), (225462655142896653210388851760269/5629499534213120000000000000000000), (-2712513562690560255948847334681/1407374883553280000000000000000000), (2769578039850954753061637346091/5629499534213120000000000000000000), (312050977309752328661876373151/1407374883553280000000000000000000), (-192886502162394641391178863771/5629499534213120000000000000000000), (-1218405711511368989478583811/281474976710656000000000000000000), (1466820935686777857512862163/2814749767106560000000000000000000), (160123585759982827625538499/2814749767106560000000000000000000), (-21271356110570418446749767/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial135.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial135.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial135.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial135 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 4130321346135416393433548562627054), (Int.ofNat 236710297227195630593179653692947), (Int.ofNat 16863023439995633596278449023463), (Int.ofNat 3204881556955674112873819884627), (Int.negOfNat 1081118917163303885725328206222), (Int.negOfNat 157198200595781203749713723103), (Int.ofNat 30841011322877945377917940833), (Int.ofNat 3074587281345298219317131697), (Int.negOfNat 353052347280585242363311554), (Int.negOfNat 36495800796706181218056673), (Int.ofNat 2070174304371241232496512), (Int.ofNat 271053364840146038204408), (Int.negOfNat 6577084004923242019238), (Int.negOfNat 1356972166823846200072), (Int.ofNat 7882153921659189374), (Int.ofNat 5005396013443492029), (Int.ofNat 31021078366058162), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-2065160673067708196716774281313527/2814749767106560000000000000000000), (236710297227195630593179653692947/5629499534213120000000000000000000), (16863023439995633596278449023463/5629499534213120000000000000000000), (3204881556955674112873819884627/5629499534213120000000000000000000), (-540559458581651942862664103111/2814749767106560000000000000000000), (-157198200595781203749713723103/5629499534213120000000000000000000), (30841011322877945377917940833/5629499534213120000000000000000000), (3074587281345298219317131697/5629499534213120000000000000000000), (-176526173640292621181655777/2814749767106560000000000000000000), (-36495800796706181218056673/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial135.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial135.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial135.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial135 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 3583876908708200173907985388886390), (Int.ofNat 302316006244773942453748721098758), (Int.ofNat 6267552702127316181181875362900), (Int.negOfNat 5862414578551212043411238795913), (Int.negOfNat 446361716663962281866498260183), (Int.ofNat 263033744573852312924520664772), (Int.ofNat 20112647856294815931850728440), (Int.negOfNat 4715445400313219720435780245), (Int.negOfNat 382070358457387295591535076), (Int.ofNat 39467512319533781341623897), (Int.ofNat 3769198220502104082379086), (Int.negOfNat 187153877436024516565038), (Int.negOfNat 23032436757396165972814), (Int.ofNat 535998321043673533394), (Int.ofNat 96922850437265876084), (Int.negOfNat 594776728211629065), (Int.negOfNat 378101119330286292), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-358387690870820017390798538888639/562949953421312000000000000000000), (151158003122386971226874360549379/2814749767106560000000000000000000), (62675527021273161811818753629/56294995342131200000000000000000), (-5862414578551212043411238795913/5629499534213120000000000000000000), (-446361716663962281866498260183/5629499534213120000000000000000000), (65758436143463078231130166193/1407374883553280000000000000000000), (502816196407370398296268211/140737488355328000000000000000000), (-943089080062643944087156049/1125899906842624000000000000000000), (-95517589614346823897883769/1407374883553280000000000000000000), (39467512319533781341623897/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial135.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial135.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial135.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial135 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 2999189291902737045571066862347568), (Int.ofNat 265261832208533115803946581332582), (Int.negOfNat 17384749066165020025744338559788), (Int.ofNat 1240544807783663481294256305333), (Int.ofNat 1841749609643147957367828754992), (Int.ofNat 39484422627937578924062966640), (Int.negOfNat 53449688272185268343119821218), (Int.negOfNat 3000186551102402273974594218), (Int.ofNat 616473222963421952598010006), (Int.ofNat 44815463610495327629574923), (Int.negOfNat 3871072408199801374587413), (Int.negOfNat 347037246166398616340858), (Int.ofNat 15282868267780669801167), (Int.ofNat 1739669343387347320687), (Int.negOfNat 39803318419394460459), (Int.negOfNat 6575198098261149061), (Int.ofNat 43362116761559494), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-187449330743921065348191678896723/351843720888320000000000000000000), (132630916104266557901973290666291/2814749767106560000000000000000000), (-4346187266541255006436084639947/1407374883553280000000000000000000), (1240544807783663481294256305333/5629499534213120000000000000000000), (115109350602696747335489297187/351843720888320000000000000000000), (493555282849219736550787083/70368744177664000000000000000000), (-26724844136092634171559910609/2814749767106560000000000000000000), (-1500093275551201136987297109/2814749767106560000000000000000000), (308236611481710976299005003/2814749767106560000000000000000000), (44815463610495327629574923/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial135.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial135.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial135.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial135 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 2501177409997627200856149804535763), (Int.ofNat 261808947823547581512309652069841), (Int.ofNat 23833366552916198981737000679658), (Int.ofNat 8595583073279255580469113525815), (Int.negOfNat 1003464366796620791289190913226), (Int.negOfNat 526814160666361025169922260029), (Int.negOfNat 13188903718098505472080210359), (Int.ofNat 8319315787356176684054065703), (Int.ofNat 448485002492812605932307901), (Int.negOfNat 66537901587911799958224249), (Int.negOfNat 4661595777192155312030922), (Int.ofNat 330937379331328402805909), (Int.ofNat 28200447082169256784537), (Int.negOfNat 1128122695962801914623), (Int.negOfNat 117194666233573359979), (Int.ofNat 2872823128479782235), (Int.ofNat 407239886183532108), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-2501177409997627200856149804535763/5629499534213120000000000000000000), (261808947823547581512309652069841/5629499534213120000000000000000000), (11916683276458099490868500339829/2814749767106560000000000000000000), (1719116614655851116093822705163/1125899906842624000000000000000000), (-501732183398310395644595456613/2814749767106560000000000000000000), (-526814160666361025169922260029/5629499534213120000000000000000000), (-13188903718098505472080210359/5629499534213120000000000000000000), (8319315787356176684054065703/5629499534213120000000000000000000), (448485002492812605932307901/5629499534213120000000000000000000), (-66537901587911799958224249/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial135.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial135.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial135.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial135 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 1846077330478825045433987885042281), (Int.ofNat 387514628302990872685664044482773), (Int.ofNat 12058211757725791277804143595098), (Int.negOfNat 17564986621186847785043978283438), (Int.negOfNat 4545131866882459780197687782976), (Int.ofNat 55094873892778781502603935612), (Int.ofNat 99367513960987089961903194292), (Int.ofNat 3731636162598320141047883324), (Int.negOfNat 993732334846374941191545090), (Int.negOfNat 56384612082659204246207100), (Int.ofNat 6035041571599557995818597), (Int.ofNat 418322674823562309205340), (Int.negOfNat 25078524272927039663336), (Int.negOfNat 2022291404644579299289), (Int.ofNat 76099964088815418201), (Int.ofNat 7406746882246393686), (Int.negOfNat 148897286420063719), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-1846077330478825045433987885042281/5629499534213120000000000000000000), (387514628302990872685664044482773/5629499534213120000000000000000000), (6029105878862895638902071797549/2814749767106560000000000000000000), (-8782493310593423892521989141719/2814749767106560000000000000000000), (-71017685420038434065588871609/87960930222080000000000000000000), (13773718473194695375650983903/1407374883553280000000000000000000), (24841878490246772490475798573/1407374883553280000000000000000000), (932909040649580035261970831/1407374883553280000000000000000000), (-99373233484637494119154509/562949953421312000000000000000000), (-563846120826592042462071/56294995342131200000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial135.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial135.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial135.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial135 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 1227733369015288762712727642718432), (Int.ofNat 103568747388726476090189515535352), (Int.negOfNat 173612688993764923407036415658268), (Int.negOfNat 35710600212513630600841101079171), (Int.ofNat 1767361576861703534227754328450), (Int.ofNat 1060023642587047975662125513969), (Int.ofNat 27031701181617984864606941381), (Int.negOfNat 13099026278803932016003565581), (Int.negOfNat 632389641633069011505479198), (Int.ofNat 95860923114419176941212028), (Int.ofNat 5759883131956088373761048), (Int.negOfNat 475433366994916326451122), (Int.negOfNat 32403118379580760611176), (Int.ofNat 1721771788025067644610), (Int.ofNat 128804979664698849828), (Int.negOfNat 4660420417052273695), (Int.negOfNat 401200263150609849), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-38366667781727773834772738834951/175921860444160000000000000000000), (12946093423590809511273689441919/703687441776640000000000000000000), (-43403172248441230851759103914567/1407374883553280000000000000000000), (-35710600212513630600841101079171/5629499534213120000000000000000000), (35347231537234070684555086569/112589990684262400000000000000000), (1060023642587047975662125513969/5629499534213120000000000000000000), (27031701181617984864606941381/5629499534213120000000000000000000), (-13099026278803932016003565581/5629499534213120000000000000000000), (-316194820816534505752739599/2814749767106560000000000000000000), (23965230778604794235303007/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial135.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial135.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial135.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial135 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 1938587539819186026644175211788377), (Int.negOfNat 879133285764517000886673419346078), (Int.negOfNat 263613079516104889186958253600375), (Int.ofNat 17266291053797543350884243992739), (Int.ofNat 10053978368010071804580394505382), (Int.ofNat 223817632014367073758465617973), (Int.negOfNat 151893400228049521633689157565), (Int.negOfNat 6979493967728422489796332774), (Int.ofNat 1336308649691679079831093876), (Int.ofNat 75372212320496576861979555), (Int.negOfNat 7873965753652726240152511), (Int.negOfNat 487767352000870865715507), (Int.ofNat 33572094847646588592357), (Int.ofNat 2189200988124630427304), (Int.negOfNat 108770110586812519580), (Int.negOfNat 7530701453152995305), (Int.ofNat 254432456078567944), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-1938587539819186026644175211788377/5629499534213120000000000000000000), (-439566642882258500443336709673039/2814749767106560000000000000000000), (-2108904636128839113495666028803/45035996273704960000000000000000), (17266291053797543350884243992739/5629499534213120000000000000000000), (5026989184005035902290197252691/2814749767106560000000000000000000), (223817632014367073758465617973/5629499534213120000000000000000000), (-30378680045609904326737831513/1125899906842624000000000000000000), (-3489746983864211244898166387/2814749767106560000000000000000000), (334077162422919769957773469/1407374883553280000000000000000000), (15074442464099315372395911/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial135.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial135.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial135.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial135 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 4455393058573634930446993878652988), (Int.negOfNat 1417550582767060243807935718766479), (Int.ofNat 60681031180419883564234065754915), (Int.ofNat 81102010582395633985142269342578), (Int.ofNat 2903355298433918614909918577646), (Int.negOfNat 1508488620006053599033812616857), (Int.negOfNat 80590979756246888795379813383), (Int.ofNat 16153915819592180774631304398), (Int.ofNat 962032663573727941782370965), (Int.negOfNat 114105669357691698439468726), (Int.negOfNat 7000626392692327073918045), (Int.ofNat 574617329019303603543435), (Int.ofNat 35144348973676692669143), (Int.negOfNat 2176724875506776885154), (Int.negOfNat 130559682969554527372), (Int.ofNat 6337396772299613945), (Int.ofNat 395160640117687590), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-1113848264643408732611748469663247/1407374883553280000000000000000000), (-1417550582767060243807935718766479/5629499534213120000000000000000000), (12136206236083976712846813150983/1125899906842624000000000000000000), (40551005291197816992571134671289/2814749767106560000000000000000000), (1451677649216959307454959288823/2814749767106560000000000000000000), (-1508488620006053599033812616857/5629499534213120000000000000000000), (-80590979756246888795379813383/5629499534213120000000000000000000), (8076957909796090387315652199/2814749767106560000000000000000000), (192406532714745588356474193/1125899906842624000000000000000000), (-57052834678845849219734363/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial135.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial135.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial135.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial135 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 6403680096621340805530857922702340), (Int.negOfNat 236916979058320224994419847978384), (Int.ofNat 488943811220184686825639836060438), (Int.ofNat 41171454441195351669612165372575), (Int.negOfNat 11942763878044992569371023815635), (Int.negOfNat 954425941107151455542713184981), (Int.ofNat 163124581606522727189472603085), (Int.ofNat 12035396344763509439295687619), (Int.negOfNat 1423543381034295987544989972), (Int.negOfNat 96608390869905556556145822), (Int.ofNat 8614406443003445065729971), (Int.ofNat 537209359753324755524508), (Int.negOfNat 38386444418891942766431), (Int.negOfNat 2198444031316043896278), (Int.ofNat 131257308729998921570), (Int.ofNat 6911422448505627737), (Int.negOfNat 357954418059431416), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-320184004831067040276542896135117/281474976710656000000000000000000), (-14807311191145014062151240498649/351843720888320000000000000000000), (244471905610092343412819918030219/2814749767106560000000000000000000), (1646858177647814066784486614903/225179981368524800000000000000000), (-2388552775608998513874204763127/1125899906842624000000000000000000), (-954425941107151455542713184981/5629499534213120000000000000000000), (32624916321304545437894520617/1125899906842624000000000000000000), (12035396344763509439295687619/5629499534213120000000000000000000), (-355885845258573996886247493/1407374883553280000000000000000000), (-48304195434952778278072911/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial135.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial135.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial135.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial135.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial135 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial135 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial135 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 7718991066418908728340033859848875), (Int.negOfNat 18984812126805790436226932870017), (Int.ofNat 537344225533648817623063139978497), (Int.negOfNat 46558490758997735191479039932369), (Int.negOfNat 12500785757961105670258107414858), (Int.ofNat 1138025160089839738739928545627), (Int.ofNat 166776562602823942996146642632), (Int.negOfNat 13921868046286489446987414919), (Int.negOfNat 1438871225163893637680344922), (Int.ofNat 106951949119153265530827572), (Int.ofNat 8660017069903651184146371), (Int.negOfNat 573159746951507388454708), (Int.negOfNat 38489657528525811054131), (Int.ofNat 2284832874025360640828), (Int.ofNat 131257308729998921570), (Int.negOfNat 6911422448505627737), (Int.negOfNat 357954418059431416), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-61751928531351269826720270878791/45035996273704960000000000000000), (-18984812126805790436226932870017/5629499534213120000000000000000000), (537344225533648817623063139978497/5629499534213120000000000000000000), (-46558490758997735191479039932369/5629499534213120000000000000000000), (-6250392878980552835129053707429/2814749767106560000000000000000000), (1138025160089839738739928545627/5629499534213120000000000000000000), (20847070325352992874518330329/703687441776640000000000000000000), (-13921868046286489446987414919/5629499534213120000000000000000000), (-719435612581946818840172461/2814749767106560000000000000000000), (26737987279788316382706893/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial135.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial135.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial135.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 6135061815353022538770362378196729), (Int.ofNat 1287301257928185999523507932559773), (Int.ofNat 77683122016322809498608352696564), (Int.negOfNat 84054025128239509842365835221597), (Int.ofNat 3895883457068569340717665003913), (Int.ofNat 1590756487900781472361298391401), (Int.negOfNat 98480926940516241440838063383), (Int.negOfNat 16935424153850087325760130548), (Int.ofNat 1096318634651592976940195715), (Int.ofNat 118228542408153028185073976), (Int.negOfNat 7585843152647604870215345), (Int.negOfNat 588652876668094203179035), (Int.ofNat 36836293216110793264393), (Int.ofNat 2210355454609724192604), (Int.negOfNat 134153790659945842672), (Int.negOfNat 6337396772299613945), (Int.ofNat 395160640117687590), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-6135061815353022538770362378196729/5629499534213120000000000000000000), (1287301257928185999523507932559773/5629499534213120000000000000000000), (19420780504080702374652088174141/1407374883553280000000000000000000), (-84054025128239509842365835221597/5629499534213120000000000000000000), (3895883457068569340717665003913/5629499534213120000000000000000000), (1590756487900781472361298391401/5629499534213120000000000000000000), (-98480926940516241440838063383/5629499534213120000000000000000000), (-4233856038462521831440032637/1407374883553280000000000000000000), (219263726930318595388039143/1125899906842624000000000000000000), (14778567801019128523134247/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial135.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial135.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial135.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 3817058799419669619641463446568530), (Int.ofNat 816169391097168209838738768536317), (Int.negOfNat 238487111606794697525200368071547), (Int.negOfNat 12033980964053662910027814876689), (Int.ofNat 10735754464952933538014370896064), (Int.negOfNat 358359405309031497025132364396), (Int.negOfNat 164983105947137642901879104415), (Int.ofNat 8349285425598262257301000074), (Int.ofNat 1435014095717459745723840526), (Int.negOfNat 82916021358238066074316005), (Int.negOfNat 8303573678449663305570361), (Int.ofNat 514094074750033722639107), (Int.ofNat 34810936441285976993907), (Int.negOfNat 2253620768360798921504), (Int.negOfNat 111337330365663459080), (Int.ofNat 7530701453152995305), (Int.ofNat 254432456078567944), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-381705879941966961964146344656853/562949953421312000000000000000000), (816169391097168209838738768536317/5629499534213120000000000000000000), (-238487111606794697525200368071547/5629499534213120000000000000000000), (-12033980964053662910027814876689/5629499534213120000000000000000000), (167746163514889586531474545251/87960930222080000000000000000000), (-89589851327257874256283091099/1407374883553280000000000000000000), (-32996621189427528580375820883/1125899906842624000000000000000000), (4174642712799131128650500037/2814749767106560000000000000000000), (717507047858729872861920263/2814749767106560000000000000000000), (-16583204271647613214863201/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial135.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial135.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial135.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 3083808367971616272375057929247263), (Int.ofNat 5994704156170880892800937008010), (Int.negOfNat 113576622325372284932198279317416), (Int.ofNat 39819135568049582071985611144554), (Int.ofNat 777482173040262971297272567803), (Int.negOfNat 1210151247024870760974012373666), (Int.ofNat 38108000134020743693362007178), (Int.ofNat 14711861946798142666414985181), (Int.negOfNat 705250520286930025922619148), (Int.negOfNat 104876471919308167615185328), (Int.ofNat 6062219984071391153694998), (Int.ofNat 507048373570113272348172), (Int.negOfNat 33258352879066534499176), (Int.negOfNat 1798633866082168151760), (Int.ofNat 130602033509894507478), (Int.ofNat 4660420417052273695), (Int.negOfNat 401200263150609849), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-3083808367971616272375057929247263/5629499534213120000000000000000000), (599470415617088089280093700801/562949953421312000000000000000000), (-14197077790671535616524784914677/703687441776640000000000000000000), (19909567784024791035992805572277/2814749767106560000000000000000000), (777482173040262971297272567803/5629499534213120000000000000000000), (-605075623512435380487006186833/2814749767106560000000000000000000), (19054000067010371846681003589/2814749767106560000000000000000000), (14711861946798142666414985181/5629499534213120000000000000000000), (-176312630071732506480654787/1407374883553280000000000000000000), (-6554779494956760475949083/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial135.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial135.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial135.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 3229762602640116766512186899716906), (Int.negOfNat 29435137499751522542923005303570), (Int.ofNat 64552507327879736278726764413789), (Int.ofNat 10251606034210696256230202447496), (Int.negOfNat 6032805875947774353566055435537), (Int.ofNat 15617231122862699035759169059), (Int.ofNat 120222078754034546666089419720), (Int.negOfNat 4154792726272624925746768874), (Int.negOfNat 1142222879798920894582621540), (Int.ofNat 58137682697012596777978250), (Int.ofNat 6670783292276351472893497), (Int.negOfNat 423601355089648379828940), (Int.negOfNat 26902363714751177765636), (Int.ofNat 2035116888281356322789), (Int.ofNat 79950793757091827451), (Int.negOfNat 7406746882246393686), (Int.negOfNat 148897286420063719), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-1614881301320058383256093449858453/2814749767106560000000000000000000), (-2943513749975152254292300530357/562949953421312000000000000000000), (64552507327879736278726764413789/5629499534213120000000000000000000), (1281450754276337032028775305937/703687441776640000000000000000000), (-6032805875947774353566055435537/5629499534213120000000000000000000), (15617231122862699035759169059/5629499534213120000000000000000000), (3005551968850863666652235493/140737488355328000000000000000000), (-2077396363136312462873384437/2814749767106560000000000000000000), (-57111143989946044729131077/281474976710656000000000000000000), (232550730788050387111913/22517998136852480000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial135.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial135.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial135.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 3037529514780131920952771356896676), (Int.ofNat 180208197134905967283952230555598), (Int.ofNat 6869943264255248052843115162844), (Int.negOfNat 22129436684721605942945215751118), (Int.negOfNat 802370030091831020245424004437), (Int.ofNat 754039534648538037931057129101), (Int.negOfNat 11755858640159806097869290309), (Int.negOfNat 10326792373966039538220106553), (Int.ofNat 425740987887630020659046501), (Int.ofNat 76995314569998522493894099), (Int.negOfNat 4541054449110169376967072), (Int.negOfNat 366556076555412309146759), (Int.ofNat 27824257284773779143237), (Int.ofNat 1213336956407663018773), (Int.negOfNat 116424500299918078129), (Int.negOfNat 2872823128479782235), (Int.ofNat 407239886183532108), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-759382378695032980238192839224169/1407374883553280000000000000000000), (90104098567452983641976115277799/2814749767106560000000000000000000), (1717485816063812013210778790711/1407374883553280000000000000000000), (-11064718342360802971472607875559/2814749767106560000000000000000000), (-802370030091831020245424004437/5629499534213120000000000000000000), (754039534648538037931057129101/5629499534213120000000000000000000), (-11755858640159806097869290309/5629499534213120000000000000000000), (-10326792373966039538220106553/5629499534213120000000000000000000), (425740987887630020659046501/5629499534213120000000000000000000), (76995314569998522493894099/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial135.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial135.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial135.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 2817308568200869247273710584076744), (Int.negOfNat 29514764605074191556574376762331), (Int.negOfNat 93544289064189121614096830107392), (Int.negOfNat 4955736860218856686114270178136), (Int.ofNat 3855777326137131833260476320785), (Int.ofNat 47111394943915955232207441446), (Int.negOfNat 75766162033785782554141770518), (Int.ofNat 2062242474251122609369334818), (Int.ofNat 757200167418393693586993356), (Int.negOfNat 39468064276083891494577773), (Int.negOfNat 4440176133819118507102513), (Int.ofNat 328028580633494648954958), (Int.ofNat 16871827054324648916517), (Int.negOfNat 1693100458720687899637), (Int.negOfNat 43140704131900681809), (Int.ofNat 6318476120376055111), (Int.ofNat 43362116761559494), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-352163571025108655909213823009593/703687441776640000000000000000000), (-29514764605074191556574376762331/5629499534213120000000000000000000), (-365407379156988756305065742607/21990232555520000000000000000000), (-619467107527357085764283772267/703687441776640000000000000000000), (771155465227426366652095264157/1125899906842624000000000000000000), (23555697471957977616103720723/2814749767106560000000000000000000), (-37883081016892891277070885259/2814749767106560000000000000000000), (1031121237125561304684667409/2814749767106560000000000000000000), (189300041854598423396748339/1407374883553280000000000000000000), (-39468064276083891494577773/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial135.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial135.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial135.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 3231376398638542358515773010765796), (Int.negOfNat 348964474820878512395319991228880), (Int.negOfNat 42635215425373676430920482174557), (Int.ofNat 17898968503438813446336895436135), (Int.ofNat 1002949519303077780363773285259), (Int.negOfNat 454175281204796797525570365099), (Int.ofNat 1928153107839740284184714190), (Int.ofNat 6196310702351648008369049795), (Int.negOfNat 258790784762986846701671026), (Int.negOfNat 46580953521359988944979797), (Int.ofNat 3250856757061690319841436), (Int.ofNat 210325759060337999077988), (Int.negOfNat 21553624984497435789214), (Int.negOfNat 589790293517095759544), (Int.ofNat 93842186702644748684), (Int.ofNat 851498706096723015), (Int.negOfNat 378101119330286292), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-807844099659635589628943252691449/1407374883553280000000000000000000), (-4362055935260981404941499890361/70368744177664000000000000000000), (-42635215425373676430920482174557/5629499534213120000000000000000000), (3579793700687762689267379087227/1125899906842624000000000000000000), (1002949519303077780363773285259/5629499534213120000000000000000000), (-454175281204796797525570365099/5629499534213120000000000000000000), (192815310783974028418471419/562949953421312000000000000000000), (1239262140470329601673809959/1125899906842624000000000000000000), (-129395392381493423350835513/2814749767106560000000000000000000), (-46580953521359988944979797/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial135.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial135.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial135.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 3954310780904287887041809625521497), (Int.negOfNat 306165060801872493341117242272986), (Int.ofNat 56485498013987588739530224968295), (Int.ofNat 10876106939788117311986206400269), (Int.negOfNat 2116081801189762521411040732898), (Int.negOfNat 90241587624006054723113755243), (Int.ofNat 41090108280412305968014571908), (Int.negOfNat 990486433512971314094797347), (Int.negOfNat 411545675460569152817699004), (Int.ofNat 25936811712183932841571673), (Int.ofNat 2290369582974112114136012), (Int.negOfNat 235552793048129292290758), (Int.negOfNat 7163034639911998150588), (Int.ofNat 1273041516268410565672), (Int.ofNat 9165763811084659124), (Int.negOfNat 5005396013443492029), (Int.ofNat 31021078366058162), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-3954310780904287887041809625521497/5629499534213120000000000000000000), (-153082530400936246670558621136493/2814749767106560000000000000000000), (11297099602797517747906044993659/1125899906842624000000000000000000), (10876106939788117311986206400269/5629499534213120000000000000000000), (-1058040900594881260705520366449/2814749767106560000000000000000000), (-90241587624006054723113755243/5629499534213120000000000000000000), (10272527070103076492003642977/1407374883553280000000000000000000), (-990486433512971314094797347/5629499534213120000000000000000000), (-102886418865142288204424751/1407374883553280000000000000000000), (25936811712183932841571673/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial135.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial135.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial135.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 4288022341928891236648499240163311), (Int.negOfNat 17550866561600528884653492527926), (Int.ofNat 72334365960198045834072500298067), (Int.negOfNat 4215725267876433625475216809402), (Int.negOfNat 1166393873965341852102086102810), (Int.ofNat 198748082445186594468603812188), (Int.ofNat 2624211564011973366096834380), (Int.negOfNat 2930499838631342024923769776), (Int.ofNat 150400965570204781678605448), (Int.ofNat 21045896050681273699695367), (Int.negOfNat 2139970942783909340692587), (Int.negOfNat 75076230283426996202698), (Int.ofNat 14891862601705806869513), (Int.ofNat 54867959821841956479), (Int.negOfNat 66723964120459731789), (Int.ofNat 779896360494571353), (Int.ofNat 311770754913231648), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-4288022341928891236648499240163311/5629499534213120000000000000000000), (-8775433280800264442326746263963/2814749767106560000000000000000000), (72334365960198045834072500298067/5629499534213120000000000000000000), (-2107862633938216812737608404701/2814749767106560000000000000000000), (-116639387396534185210208610281/562949953421312000000000000000000), (49687020611296648617150953047/1407374883553280000000000000000000), (131210578200598668304841719/281474976710656000000000000000000), (-183156239914458876557735611/351843720888320000000000000000000), (18800120696275597709825681/703687441776640000000000000000000), (21045896050681273699695367/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial135.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial135.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial135.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 4079974937691609894912007277831550), (Int.ofNat 199155180928001279066284734526826), (Int.ofNat 33947645584039899130356811854581), (Int.negOfNat 6469892981933532209194475775868), (Int.ofNat 381215624206758144613242032910), (Int.ofNat 75871532644757590341061605861), (Int.negOfNat 14870405605621449831084338817), (Int.ofNat 412224206533609788203142735), (Int.ofNat 153550091524936389548063889), (Int.negOfNat 15193606350302706644676795), (Int.negOfNat 637203458052773198155918), (Int.ofNat 146369637024718801240489), (Int.negOfNat 330177716346577085119), (Int.negOfNat 810014639826743885661), (Int.ofNat 17041768078392513451), (Int.ofNat 2981241927149566049), (Int.negOfNat 72239091285148496), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-81599498753832197898240145556631/112589990684262400000000000000000), (99577590464000639533142367263413/2814749767106560000000000000000000), (33947645584039899130356811854581/5629499534213120000000000000000000), (-1617473245483383052298618943967/1407374883553280000000000000000000), (38121562420675814461324203291/562949953421312000000000000000000), (75871532644757590341061605861/5629499534213120000000000000000000), (-14870405605621449831084338817/5629499534213120000000000000000000), (82444841306721957640628547/1125899906842624000000000000000000), (153550091524936389548063889/5629499534213120000000000000000000), (-3038721270060541328935359/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial135.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial135.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial135.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 3589973570238192973382924520982564), (Int.ofNat 273025795454298264170664763905506), (Int.ofNat 7257090361678854254460604637544), (Int.negOfNat 2344106625007949540490378382252), (Int.ofNat 471150014292193997626480204888), (Int.negOfNat 30871725521688362320642525091), (Int.negOfNat 2266520843778876034829655043), (Int.ofNat 756636141781032292455938242), (Int.negOfNat 72059878157189714444117812), (Int.negOfNat 3713591242259973709443514), (Int.ofNat 1138968935058964935758501), (Int.negOfNat 17203156882496967077690), (Int.negOfNat 8160851647675958453972), (Int.ofNat 301435303142404012899), (Int.ofNat 36730809016813315551), (Int.negOfNat 2069487890128985228), (Int.negOfNat 206235585254727423), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-897493392559548243345731130245641/1407374883553280000000000000000000), (136512897727149132085332381952753/2814749767106560000000000000000000), (907136295209856781807575579693/703687441776640000000000000000000), (-586026656251987385122594595563/1407374883553280000000000000000000), (58893751786524249703310025611/703687441776640000000000000000000), (-30871725521688362320642525091/5629499534213120000000000000000000), (-2266520843778876034829655043/5629499534213120000000000000000000), (378318070890516146227969121/2814749767106560000000000000000000), (-18014969539297428611029453/1407374883553280000000000000000000), (-1856795621129986854721757/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial135.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial135.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial135.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 3027163421817414909216665124360680), (Int.ofNat 286358852319879647441026919518916), (Int.ofNat 1860708885524058974536156518962), (Int.ofNat 118162290210149893012300451996), (Int.ofNat 156308500433625922621958849369), (Int.negOfNat 26302775924195858758543608896), (Int.ofNat 939166401572438437108626529), (Int.negOfNat 89625261143172216203977123), (Int.negOfNat 3551655516409585542654376), (Int.ofNat 6011153447683679905077434), (Int.negOfNat 332220419491080360406636), (Int.negOfNat 62106036074168496661492), (Int.ofNat 4560662279252853809750), (Int.ofNat 344233158402903861278), (Int.negOfNat 30055248931506129352), (Int.negOfNat 1110286667560577709), (Int.ofNat 78278714318070755), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-75679085545435372730416628109017/140737488355328000000000000000000), (71589713079969911860256729879729/1407374883553280000000000000000000), (930354442762029487268078259481/2814749767106560000000000000000000), (29540572552537473253075112999/1407374883553280000000000000000000), (156308500433625922621958849369/5629499534213120000000000000000000), (-410980873815560293102243889/87960930222080000000000000000000), (939166401572438437108626529/5629499534213120000000000000000000), (-89625261143172216203977123/5629499534213120000000000000000000), (-443956939551198192831797/703687441776640000000000000000000), (3005576723841839952538717/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial135.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial135.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial135.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 2444347979451355147526076527326116), (Int.ofNat 298265392069364660221174945722290), (Int.ofNat 4398146119513933613236793299862), (Int.ofNat 435410977610320554863682307773), (Int.negOfNat 61623381325943736917534689280), (Int.negOfNat 16007403869899977639481791252), (Int.ofNat 1611518811956312895142776163), (Int.ofNat 211072501416686363802676268), (Int.ofNat 6744347654098162398117508), (Int.negOfNat 4478833718319615510236591), (Int.negOfNat 243509702780507133218545), (Int.ofNat 58086368257368004559263), (Int.ofNat 1853101415788986494213), (Int.negOfNat 436260905035444608214), (Int.negOfNat 7598514336011987880), (Int.ofNat 2146094081625131209), (Int.ofNat 100700415596223198), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-611086994862838786881519131831529/1407374883553280000000000000000000), (29826539206936466022117494572229/562949953421312000000000000000000), (2199073059756966806618396649931/2814749767106560000000000000000000), (435410977610320554863682307773/5629499534213120000000000000000000), (-6017908332611693058352997/549755813888000000000000000000), (-4001850967474994409870447813/1407374883553280000000000000000000), (1611518811956312895142776163/5629499534213120000000000000000000), (52768125354171590950669067/1407374883553280000000000000000000), (1686086913524540599529377/1407374883553280000000000000000000), (-4478833718319615510236591/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial135.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial135.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial135.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1828110072585974635030232153791925), (Int.ofNat 318230356377952021164755383695230), (Int.ofNat 4769996371892091765656837291058), (Int.negOfNat 335028103627331371178111132302), (Int.negOfNat 77156499357878218365658932191), (Int.ofNat 14850126539882298427439995036), (Int.ofNat 2366287971435031756950363829), (Int.negOfNat 253715331378056390697090670), (Int.negOfNat 44000442489145624246197037), (Int.ofNat 1896207827677528432595288), (Int.ofNat 604220016455137328405069), (Int.negOfNat 11508157842051989225625), (Int.negOfNat 5269720217547381808473), (Int.ofNat 74491867926954173998), (Int.ofNat 30170764093113490778), (Int.negOfNat 730575965808889541), (Int.negOfNat 84318337350993014), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-73124402903438985401209286151677/225179981368524800000000000000000), (31823035637795202116475538369523/562949953421312000000000000000000), (2384998185946045882828418645529/2814749767106560000000000000000000), (-167514051813665685589055566151/2814749767106560000000000000000000), (-77156499357878218365658932191/5629499534213120000000000000000000), (3712531634970574606859998759/1407374883553280000000000000000000), (2366287971435031756950363829/5629499534213120000000000000000000), (-25371533137805639069709067/562949953421312000000000000000000), (-44000442489145624246197037/5629499534213120000000000000000000), (237025978459691054074411/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial135.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial135.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial135.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 1175899650845893871971820104959759), (Int.ofNat 332311823745665465130217297573365), (Int.ofNat 2429686231177175243601904112692), (Int.negOfNat 182160114836441542068926479497), (Int.ofNat 107669863879695403301079059226), (Int.ofNat 10095226758460007778048579236), (Int.negOfNat 3253504247157636467778548986), (Int.negOfNat 278820492314109288598638553), (Int.ofNat 50132082287016198883224206), (Int.ofNat 4669464946094776635537844), (Int.negOfNat 480206146709813815680315), (Int.negOfNat 50171373003466311360922), (Int.ofNat 3323154883086681941633), (Int.ofNat 350255848380519289150), (Int.negOfNat 16562247830062331360), (Int.negOfNat 1815520231113617327), (Int.ofNat 6847961739921780), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1175899650845893871971820104959759/5629499534213120000000000000000000), (66462364749133093026043459514673/1125899906842624000000000000000000), (607421557794293810900476028173/1407374883553280000000000000000000), (-182160114836441542068926479497/5629499534213120000000000000000000), (53834931939847701650539529613/2814749767106560000000000000000000), (2523806689615001944512144809/1407374883553280000000000000000000), (-1626752123578818233889274493/2814749767106560000000000000000000), (-278820492314109288598638553/5629499534213120000000000000000000), (25066041143508099441612103/2814749767106560000000000000000000), (1167366236523694158884461/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial135.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial135.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial135.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 501198041320936615946718017355775), (Int.ofNat 343407284554193610838729355134798), (Int.ofNat 3864893597483089516838447103844), (Int.ofNat 512213437911014699017632693306), (Int.ofNat 2271596948457766485055619596), (Int.negOfNat 25420706311463570996583685204), (Int.negOfNat 503044278429727303948148264), (Int.ofNat 582597960531158601021415347), (Int.ofNat 17836360539748670128961944), (Int.negOfNat 7633841588668104864865706), (Int.negOfNat 297100940106333937916685), (Int.ofNat 64942017478499405720578), (Int.ofNat 2849613047293611803517), (Int.negOfNat 387895678276469026900), (Int.negOfNat 17538179581614293890), (Int.ofNat 1888550716503257273), (Int.ofNat 17987972933938370), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-20047921652837464637868720694231/225179981368524800000000000000000), (171703642277096805419364677567399/2814749767106560000000000000000000), (966223399370772379209611775961/1407374883553280000000000000000000), (256106718955507349508816346653/2814749767106560000000000000000000), (567899237114441621263904899/1407374883553280000000000000000000), (-6355176577865892749145921301/1407374883553280000000000000000000), (-62880534803715912993518533/703687441776640000000000000000000), (582597960531158601021415347/5629499534213120000000000000000000), (2229545067468583766120243/703687441776640000000000000000000), (-3816920794334052432432853/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial135.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial135.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial135.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 204439564953266391079043364230048), (Int.ofNat 363216808415665831244288623036736), (Int.ofNat 5225129129217565823126966267623), (Int.negOfNat 251373536814554253991663348501), (Int.negOfNat 130837078348728884239051546460), (Int.ofNat 9755198634777465184952569858), (Int.ofNat 4557628995647301979286019121), (Int.negOfNat 148541718549873209797440470), (Int.negOfNat 82518399998649125109928213), (Int.ofNat 785231791317508625871188), (Int.ofNat 902295228036013895437281), (Int.ofNat 3830381627274014291475), (Int.negOfNat 6537189172305384860077), (Int.negOfNat 80333183648876823802), (Int.ofNat 33344362835626015622), (Int.ofNat 897933650291725209), (Int.negOfNat 81231156867539436), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(6388736404789574721220105132189/175921860444160000000000000000000), (5675262631494778613192009734949/87960930222080000000000000000000), (5225129129217565823126966267623/5629499534213120000000000000000000), (-251373536814554253991663348501/5629499534213120000000000000000000), (-6541853917436444211952577323/281474976710656000000000000000000), (4877599317388732592476284929/2814749767106560000000000000000000), (4557628995647301979286019121/5629499534213120000000000000000000), (-14854171854987320979744047/562949953421312000000000000000000), (-82518399998649125109928213/5629499534213120000000000000000000), (196307947829377156467797/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial135.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial135.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial135.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 948234340262224914857342022580126), (Int.ofNat 378424802092515811327551446247034), (Int.ofNat 2217030411645056183324374894153), (Int.negOfNat 392190229753582628146437091102), (Int.ofNat 120791808244774062358681460407), (Int.ofNat 23318771368209385328387278991), (Int.negOfNat 3526327766607153278630425113), (Int.negOfNat 629070464150007279049429932), (Int.ofNat 50430614542675155526127492), (Int.ofNat 9372390475968778948580509), (Int.negOfNat 401678568034871137035555), (Int.negOfNat 86713509296875688256437), (Int.ofNat 1873587345341367711987), (Int.ofNat 539159364378737607986), (Int.negOfNat 5116815258568545770), (Int.negOfNat 2507829721150624841), (Int.ofNat 85533989046925102), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(474117170131112457428671011290063/2814749767106560000000000000000000), (189212401046257905663775723123517/2814749767106560000000000000000000), (2217030411645056183324374894153/5629499534213120000000000000000000), (-196095114876791314073218545551/2814749767106560000000000000000000), (120791808244774062358681460407/5629499534213120000000000000000000), (23318771368209385328387278991/5629499534213120000000000000000000), (-3526327766607153278630425113/5629499534213120000000000000000000), (-157267616037501819762357483/1407374883553280000000000000000000), (12607653635668788881531873/1407374883553280000000000000000000), (9372390475968778948580509/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial135.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial135.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial135.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 1713204339799475878842880673267342), (Int.ofNat 387428877258847190526295771372749), (Int.ofNat 3486039440978482460833435573514), (Int.ofNat 721689124557527774195088347998), (Int.ofNat 51893743300434301047944477164), (Int.negOfNat 35799139227080610821506484803), (Int.negOfNat 2798929292523607639722374351), (Int.ofNat 784755375457956466989771427), (Int.ofNat 66608931687950992485577426), (Int.negOfNat 9298609843223821979651916), (Int.negOfNat 868096208613758980047314), (Int.ofNat 66592325893154079272708), (Int.ofNat 6999267989669617274200), (Int.negOfNat 311260600064973997872), (Int.negOfNat 37845852821830204898), (Int.ofNat 779042704955615041), (Int.ofNat 87270779900461695), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(856602169899737939421440336633671/2814749767106560000000000000000000), (387428877258847190526295771372749/5629499534213120000000000000000000), (1743019720489241230416717786757/2814749767106560000000000000000000), (360844562278763887097544173999/2814749767106560000000000000000000), (12973435825108575261986119291/1407374883553280000000000000000000), (-35799139227080610821506484803/5629499534213120000000000000000000), (-2798929292523607639722374351/5629499534213120000000000000000000), (784755375457956466989771427/5629499534213120000000000000000000), (33304465843975496242788713/2814749767106560000000000000000000), (-2324652460805955494912979/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial135.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial135.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial135.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 2507397373720484142157722186427297), (Int.ofNat 408687389573082175559001459399720), (Int.ofNat 6122105835771938059203157284350), (Int.negOfNat 243967801732142863723555860625), (Int.negOfNat 225308138794536527620680242238), (Int.ofNat 3169215156682744711720487269), (Int.ofNat 7787038016936974631417589568), (Int.ofNat 158763562789604160683910842), (Int.negOfNat 132515446372096794656546238), (Int.negOfNat 5165573400913067064906964), (Int.ofNat 1287428255616308824926999), (Int.ofNat 66120576863224369992410), (Int.negOfNat 7880861260377171027978), (Int.negOfNat 484020323425840267551), (Int.ofNat 32501070254003732049), (Int.ofNat 2383875150244023222), (Int.negOfNat 191069158705429327), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(2507397373720484142157722186427297/5629499534213120000000000000000000), (10217184739327054388975036484993/140737488355328000000000000000000), (122442116715438761184063145687/112589990684262400000000000000000), (-390348482771428581957689377/9007199254740992000000000000000), (-112654069397268263810340121119/2814749767106560000000000000000000), (3169215156682744711720487269/5629499534213120000000000000000000), (121672469014640228615899837/87960930222080000000000000000000), (79381781394802080341955421/2814749767106560000000000000000000), (-66257723186048397328273119/2814749767106560000000000000000000), (-1291393350228266766226741/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial135.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial135.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial135.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 3344288860003781639288343503105672), (Int.ofNat 424717637377887874607062751597972), (Int.ofNat 1234845690353035787896764097530), (Int.negOfNat 828501801880268699804601867858), (Int.ofNat 167774558354771494815981237699), (Int.ofNat 51587272669807309305613446120), (Int.negOfNat 3542155458774046304411241383), (Int.negOfNat 1355647521995211174447055715), (Int.ofNat 18977656114827092968603611), (Int.ofNat 18381348501631833806357455), (Int.ofNat 235869918518687919920368), (Int.negOfNat 146558563250767954403211), (Int.negOfNat 4127999903501323631281), (Int.ofNat 757223884302543025439), (Int.ofNat 29236487317310918999), (Int.negOfNat 2566639993528106501), (Int.negOfNat 93310402933383954), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(418036107500472704911042937888209/703687441776640000000000000000000), (106179409344471968651765687899493/1407374883553280000000000000000000), (123484569035303578789676409753/562949953421312000000000000000000), (-414250900940134349902300933929/2814749767106560000000000000000000), (167774558354771494815981237699/5629499534213120000000000000000000), (1289681816745182732640336153/140737488355328000000000000000000), (-3542155458774046304411241383/5629499534213120000000000000000000), (-271129504399042234889411143/1125899906842624000000000000000000), (18977656114827092968603611/5629499534213120000000000000000000), (3676269700326366761271491/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial135.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial135.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial135.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 4195984668516175239631578772547784), (Int.ofNat 427984624298481407662447891196631), (Int.ofNat 2773443232358755230842493470924), (Int.ofNat 1381309353721345781036175626609), (Int.ofNat 183660118605658639883601522746), (Int.negOfNat 61814161877238568978011235079), (Int.negOfNat 9480976739722139662715051430), (Int.ofNat 1033717161504166407878851024), (Int.ofNat 200340037653891759208781552), (Int.negOfNat 6898632038136468691721283), (Int.negOfNat 2187916149860029900197913), (Int.ofNat 4493141531782143414452), (Int.ofNat 14237343011791472515937), (Int.ofNat 203944093777784305079), (Int.negOfNat 61981845126019643161), (Int.negOfNat 1552326366258778597), (Int.ofNat 296604328363933552), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(524498083564521904953947346568473/703687441776640000000000000000000), (427984624298481407662447891196631/5629499534213120000000000000000000), (693360808089688807710623367731/1407374883553280000000000000000000), (1381309353721345781036175626609/5629499534213120000000000000000000), (91830059302829319941800761373/2814749767106560000000000000000000), (-61814161877238568978011235079/5629499534213120000000000000000000), (-948097673972213966271505143/562949953421312000000000000000000), (64607322594010400492428189/351843720888320000000000000000000), (12521252353368234950548847/351843720888320000000000000000000), (-6898632038136468691721283/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial135.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial135.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial135.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 5074629789537825566185885826595254), (Int.ofNat 455407313696885619914858921666903), (Int.ofNat 9246345777509831575860258135937), (Int.negOfNat 269929743107882018236352204327), (Int.negOfNat 544736889624862255173845520728), (Int.negOfNat 28975216068401310250252365197), (Int.ofNat 16345234256013856533064407767), (Int.ofNat 1523821217843394166089725053), (Int.negOfNat 203033328148748459530888646), (Int.negOfNat 26422306088159358473242527), (Int.ofNat 1107621354103221026444738), (Int.ofNat 226350754685471906328592), (Int.negOfNat 2238410719538425718512), (Int.negOfNat 1202152590497212338178), (Int.negOfNat 6859498770798978924), (Int.ofNat 4587964415911165721), (Int.ofNat 64171636080138138), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(2537314894768912783092942913297627/2814749767106560000000000000000000), (455407313696885619914858921666903/5629499534213120000000000000000000), (9246345777509831575860258135937/5629499534213120000000000000000000), (-269929743107882018236352204327/5629499534213120000000000000000000), (-68092111203107781896730690091/703687441776640000000000000000000), (-28975216068401310250252365197/5629499534213120000000000000000000), (16345234256013856533064407767/5629499534213120000000000000000000), (1523821217843394166089725053/5629499534213120000000000000000000), (-101516664074374229765444323/2814749767106560000000000000000000), (-26422306088159358473242527/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial135.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial135.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial135.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 6011804583090124746668373032020790), (Int.ofNat 472964217811861763707171628392542), (Int.negOfNat 3284869159388751598960768915050), (Int.negOfNat 2798165043831793945135302621487), (Int.ofNat 262692152461816989596693558333), (Int.ofNat 165950700930567805967998368628), (Int.ofNat 3861064772472657394345698310), (Int.negOfNat 3455395629692415168976285405), (Int.negOfNat 245313219673839698298158024), (Int.ofNat 28839210368742225854294003), (Int.ofNat 3066132020296620690586664), (Int.negOfNat 126041485825235271970162), (Int.negOfNat 20401259097288243040236), (Int.ofNat 282943470410332591256), (Int.ofNat 89040833812324280866), (Int.ofNat 239246259326215515), (Int.negOfNat 370987523491551208), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(601180458309012474666837303202079/562949953421312000000000000000000), (236482108905930881853585814196271/2814749767106560000000000000000000), (-65697383187775031979215378301/112589990684262400000000000000000), (-2798165043831793945135302621487/5629499534213120000000000000000000), (262692152461816989596693558333/5629499534213120000000000000000000), (41487675232641951491999592157/1407374883553280000000000000000000), (386106477247265739434569831/562949953421312000000000000000000), (-691079125938483033795257081/1125899906842624000000000000000000), (-30664152459229962287269753/703687441776640000000000000000000), (28839210368742225854294003/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial135.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial135.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial135.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 6931481303377474554457516197694468), (Int.ofNat 446951320251981073414472721271218), (Int.negOfNat 2164800541849402892688823424612), (Int.ofNat 4379209322031156796036547062417), (Int.ofNat 1061373810937465313039227980408), (Int.negOfNat 110617652693665527583798750040), (Int.negOfNat 45248739675145051594966105432), (Int.negOfNat 1397966326810738225864370532), (Int.ofNat 525629656457967844883876644), (Int.ofNat 35071244123543511638025427), (Int.negOfNat 3159062181094140593185887), (Int.negOfNat 306214505783997656911092), (Int.ofNat 11524051275495114848183), (Int.ofNat 1610034327519832085363), (Int.negOfNat 25562555803001732941), (Int.negOfNat 6219359482502460089), (Int.ofNat 2158728336916506), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(1732870325844368638614379049423617/1407374883553280000000000000000000), (223475660125990536707236360635609/2814749767106560000000000000000000), (-541200135462350723172205856153/1407374883553280000000000000000000), (4379209322031156796036547062417/5629499534213120000000000000000000), (132671726367183164129903497551/703687441776640000000000000000000), (-2765441317341638189594968751/140737488355328000000000000000000), (-5656092459393131449370763179/703687441776640000000000000000000), (-349491581702684556466092633/1407374883553280000000000000000000), (131407414114491961220969161/1407374883553280000000000000000000), (35071244123543511638025427/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial135.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial135.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial135.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 7862274488784684506460658377632463), (Int.ofNat 507242922588225938808812149518909), (Int.ofNat 29994426299332279865229274473742), (Int.ofNat 1493587236702459212761878579835), (Int.negOfNat 2474430580222357053940937894224), (Int.negOfNat 497720408260284717903522728221), (Int.ofNat 3477134048999107902959105259), (Int.ofNat 7861014818228786543605119447), (Int.ofNat 332062283692216154346794299), (Int.negOfNat 60200451903486762851023401), (Int.negOfNat 4101503384963735927958778), (Int.ofNat 284038916817113445038241), (Int.ofNat 26256200780976561535963), (Int.negOfNat 904008182409823493177), (Int.negOfNat 112136984365621478971), (Int.ofNat 2041629804852804415), (Int.ofNat 412205536410641542), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(7862274488784684506460658377632463/5629499534213120000000000000000000), (507242922588225938808812149518909/5629499534213120000000000000000000), (14997213149666139932614637236871/2814749767106560000000000000000000), (298717447340491842552375715967/1125899906842624000000000000000000), (-154651911263897315871308618389/351843720888320000000000000000000), (-497720408260284717903522728221/5629499534213120000000000000000000), (3477134048999107902959105259/5629499534213120000000000000000000), (7861014818228786543605119447/5629499534213120000000000000000000), (332062283692216154346794299/5629499534213120000000000000000000), (-60200451903486762851023401/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial135.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial135.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial135.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 8954448206656252839923271966062331), (Int.ofNat 530517722373968326687917641934127), (Int.negOfNat 53850910912696457826784231953098), (Int.negOfNat 33029132873253286289233135380412), (Int.negOfNat 4952977948604262850861645185174), (Int.ofNat 209312268611070580946704870188), (Int.ofNat 101961558536489692865547286358), (Int.ofNat 2589554555578415823544183176), (Int.negOfNat 962988549070429467507966410), (Int.negOfNat 49939979532104502073948800), (Int.ofNat 5570861488589180546219853), (Int.ofNat 392905482012650614878510), (Int.negOfNat 22057134386027219358764), (Int.negOfNat 1952570895144227521311), (Int.ofNat 63352236065018579699), (Int.ofNat 7252229034251780014), (Int.negOfNat 107693897995420731), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(8954448206656252839923271966062331/5629499534213120000000000000000000), (530517722373968326687917641934127/5629499534213120000000000000000000), (-26925455456348228913392115976549/2814749767106560000000000000000000), (-8257283218313321572308283845103/1407374883553280000000000000000000), (-2476488974302131425430822592587/2814749767106560000000000000000000), (52328067152767645236676217547/1407374883553280000000000000000000), (50980779268244846432773643179/2814749767106560000000000000000000), (323694319447301977943022897/703687441776640000000000000000000), (-96298854907042946750796641/562949953421312000000000000000000), (-15606243603782656898109/1759218604441600000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial135.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial135.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial135.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 9469888602719952848655145616761432), (Int.negOfNat 203317939609062843159960831729502), (Int.negOfNat 329823574495842878092652064845632), (Int.negOfNat 48411450905761628956732158672779), (Int.ofNat 2791050126601549734859392216150), (Int.ofNat 1172021762534504015181838801631), (Int.ofNat 19659433188574346711375178719), (Int.negOfNat 13322374314717361622390179219), (Int.negOfNat 578386993233524055742822102), (Int.ofNat 92738571610360898764091972), (Int.ofNat 5495245256067696483373502), (Int.negOfNat 441536184076118600825428), (Int.negOfNat 31640462802336283075474), (Int.ofNat 1536664218311343700240), (Int.ofNat 127869136942446070472), (Int.negOfNat 3912585064441792755), (Int.negOfNat 418245159443563801), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(1183736075339994106081893202095179/703687441776640000000000000000000), (-101658969804531421579980415864751/2814749767106560000000000000000000), (-5153493351497544970197688513213/87960930222080000000000000000000), (-48411450905761628956732158672779/5629499534213120000000000000000000), (55821002532030994697187844323/112589990684262400000000000000000), (1172021762534504015181838801631/5629499534213120000000000000000000), (19659433188574346711375178719/5629499534213120000000000000000000), (-13322374314717361622390179219/5629499534213120000000000000000000), (-289193496616762027871411051/2814749767106560000000000000000000), (23184642902590224691022993/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial135.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial135.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial135.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 7438285279379909938527656764455477), (Int.negOfNat 1923024234654015762560484662996622), (Int.negOfNat 464339815546855049970988051205025), (Int.ofNat 16007621923844537101439645991911), (Int.ofNat 11738573017107026517081890769318), (Int.ofNat 245371386820659937512152282827), (Int.negOfNat 158825155610460062733473920385), (Int.negOfNat 6863856243012506598177227126), (Int.ofNat 1329977891240403409113052074), (Int.ofNat 73780893761277127379956345), (Int.negOfNat 7570350895297861236161439), (Int.negOfNat 482817341742810227375643), (Int.ofNat 31281897365720118948243), (Int.ofNat 2195863501560593120796), (Int.negOfNat 98309420429162144770), (Int.negOfNat 7585557203633019945), (Int.ofNat 213229067653924956), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(7438285279379909938527656764455477/5629499534213120000000000000000000), (-961512117327007881280242331498311/2814749767106560000000000000000000), (-18573592621874201998839522048201/225179981368524800000000000000000), (16007621923844537101439645991911/5629499534213120000000000000000000), (5869286508553513258540945384659/2814749767106560000000000000000000), (245371386820659937512152282827/5629499534213120000000000000000000), (-31765031122092012546694784077/1125899906842624000000000000000000), (-3431928121506253299088613563/2814749767106560000000000000000000), (664988945620201704556526037/2814749767106560000000000000000000), (14756178752255425475991269/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial135.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial135.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial135.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 2047933845960315242591046424890038), (Int.negOfNat 3225108861094524914701199846576021), (Int.negOfNat 107044250783339406647924504762565), (Int.ofNat 93122649647229660448588883168822), (Int.ofNat 4410466354715148389198376483704), (Int.negOfNat 1564071630658397411758410583893), (Int.negOfNat 86715245080983677974920378767), (Int.ofNat 16203695043730296250864676402), (Int.ofNat 972218499361165961012415385), (Int.negOfNat 111893816663196769849387974), (Int.negOfNat 7034572487784011453607355), (Int.ofNat 550855367527336379530165), (Int.ofNat 35639728290916802216507), (Int.negOfNat 2038275499741886375496), (Int.negOfNat 134030356967803196678), (Int.ofNat 5753447697811260005), (Int.ofNat 424284782476486060), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(1023966922980157621295523212445019/2814749767106560000000000000000000), (-3225108861094524914701199846576021/5629499534213120000000000000000000), (-21408850156667881329584900952513/1125899906842624000000000000000000), (46561324823614830224294441584411/2814749767106560000000000000000000), (551308294339393548649797060463/703687441776640000000000000000000), (-1564071630658397411758410583893/5629499534213120000000000000000000), (-86715245080983677974920378767/5629499534213120000000000000000000), (8101847521865148125432338201/2814749767106560000000000000000000), (194443699872233192202483077/1125899906842624000000000000000000), (-55946908331598384924693987/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial135.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial135.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial135.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 4068252565049523489772103167546860), (Int.negOfNat 2528486257384637198058843904243016), (Int.ofNat 423657455024574087177233823322762), (Int.ofNat 62102367090630959934147870956725), (Int.negOfNat 11326025783887034105473971453065), (Int.negOfNat 1071181924007764121036815116319), (Int.ofNat 159914823847990326574748343765), (Int.ofNat 12434044812852319704052498631), (Int.negOfNat 1402449327398362273649612978), (Int.negOfNat 98215399414315155108015428), (Int.ofNat 8407896469573932546100279), (Int.ofNat 549550487532800904374042), (Int.negOfNat 36876445901051424887669), (Int.negOfNat 2278095078676437838072), (Int.ofNat 123959117535423323130), (Int.ofNat 7254983353121506063), (Int.negOfNat 320777444990069934), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-203412628252476174488605158377343/281474976710656000000000000000000), (-316060782173079649757355488030377/703687441776640000000000000000000), (211828727512287043588616911661381/2814749767106560000000000000000000), (2484094683625238397365914838269/225179981368524800000000000000000), (-2265205156777406821094794290613/1125899906842624000000000000000000), (-1071181924007764121036815116319/5629499534213120000000000000000000), (31982964769598065314949668753/1125899906842624000000000000000000), (12434044812852319704052498631/5629499534213120000000000000000000), (-701224663699181136824806489/2814749767106560000000000000000000), (-24553849853578788777003857/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial135.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial135.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial135.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial135.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial135.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial135.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial135.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial135.reflect := by
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

end Bin135
end
end ErdosOverlap.OuterNumerics
