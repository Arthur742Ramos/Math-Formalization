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

/-! # Exact integer weighted outer models for source bin 163

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin163

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 391588125537055000)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 1759681713408036000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 1254808591549198800)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 468721103274731900)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 861044782800534100)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 698580386839304800)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 495696903003157160)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 360417635729105400)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 201257364978375400)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 116441128710642310)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial163.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial163.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9129860167934676000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 3552638496876840400)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1165631339093603900)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 968375551545911200)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 500684575470271700)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 189443170083081800)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 9814707638134883)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 31504533632603447)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 26473334413116686)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial163.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial163.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9129860167934676000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 3552638496876840400)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1165631339093603900)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 968375551545911200)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 500684575470271700)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 189443170083081800)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 9814707638134883)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 31504533632603447)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 26473334413116686)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial163.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial163.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial163.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 3936575471770008755332292790503662), (Int.ofNat 3974125975407296093328632997911067), (Int.ofNat 387550651944433524911201991790880), (Int.negOfNat 96488825851451388824496905457835), (Int.negOfNat 12087988793333218133076585342667), (Int.ofNat 1688704655912802746055384421490), (Int.ofNat 207077555963925420294485062280), (Int.negOfNat 19666056819500463643267594599), (Int.negOfNat 2190088643056024179341012489), (Int.ofNat 158316882729558400031731635), (Int.ofNat 15621753171994858629933663), (Int.negOfNat 920348263849100576824962), (Int.negOfNat 80068862674055174964668), (Int.ofNat 4007715127361027782122), (Int.ofNat 309218748838567216791), (Int.negOfNat 13316153949058713744), (Int.negOfNat 973807548642890513), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1968287735885004377666146395251831/5629499534213120000000000000000000), (3974125975407296093328632997911067/11258999068426240000000000000000000), (2422191574652709530695012448693/70368744177664000000000000000000), (-19297765170290277764899381091567/2251799813685248000000000000000000), (-12087988793333218133076585342667/11258999068426240000000000000000000), (168870465591280274605538442149/1125899906842624000000000000000000), (5176938899098135507362126557/281474976710656000000000000000000), (-19666056819500463643267594599/11258999068426240000000000000000000), (-2190088643056024179341012489/11258999068426240000000000000000000), (31663376545911680006346327/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial163.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial163.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial163.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial163 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 4660869133397132887480374105515755), (Int.ofNat 4143881906525479169860645097468153), (Int.negOfNat 312960376866094095253797025834177), (Int.negOfNat 106405229472017861179287113002310), (Int.ofNat 10065323998459908304631843966987), (Int.ofNat 1951925830325739981116197579093), (Int.negOfNat 171923927149470941597124567859), (Int.negOfNat 23252672686824495058129499232), (Int.ofNat 1833296192370845784685391050), (Int.ofNat 187576868476163732405124977), (Int.negOfNat 13310285841102627090566445), (Int.negOfNat 1080870498436282831912206), (Int.ofNat 69586081258460288805658), (Int.ofNat 4646625797689329819370), (Int.negOfNat 273663932526959427524), (Int.negOfNat 15281746481256194033), (Int.ofNat 878947394667801379), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(932173826679426577496074821103151/2251799813685248000000000000000000), (4143881906525479169860645097468153/11258999068426240000000000000000000), (-312960376866094095253797025834177/11258999068426240000000000000000000), (-10640522947201786117928711300231/1125899906842624000000000000000000), (10065323998459908304631843966987/11258999068426240000000000000000000), (1951925830325739981116197579093/11258999068426240000000000000000000), (-171923927149470941597124567859/11258999068426240000000000000000000), (-726646021463265470566546851/351843720888320000000000000000000), (36665923847416915693707821/225179981368524800000000000000000), (187576868476163732405124977/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial163.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial163.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial163.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial163 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 11055626778306035407003881472314841), (Int.ofNat 2052226560143468417842152605649581), (Int.negOfNat 606586268793341651392706265429043), (Int.ofNat 15717619606966629197818485801951), (Int.ofNat 15353656577749478850529898173819), (Int.negOfNat 995941235109042863013499525631), (Int.negOfNat 221888807350968193071243969051), (Int.ofNat 16740310694404613468713326345), (Int.ofNat 2067515253350492984063579950), (Int.negOfNat 161816167928922101422683590), (Int.negOfNat 13442471130453236593593628), (Int.ofNat 1045611412047455589181261), (Int.ofNat 64285282695539674637255), (Int.negOfNat 4863305573413688105053), (Int.negOfNat 234776206331039827230), (Int.ofNat 17094352621737168533), (Int.ofNat 650957496924080269), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(11055626778306035407003881472314841/11258999068426240000000000000000000), (2052226560143468417842152605649581/11258999068426240000000000000000000), (-606586268793341651392706265429043/11258999068426240000000000000000000), (15717619606966629197818485801951/11258999068426240000000000000000000), (15353656577749478850529898173819/11258999068426240000000000000000000), (-995941235109042863013499525631/11258999068426240000000000000000000), (-221888807350968193071243969051/11258999068426240000000000000000000), (3348062138880922693742665269/2251799813685248000000000000000000), (41350305067009859681271599/225179981368524800000000000000000), (-16181616792892210142268359/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial163.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial163.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial163.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial163 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 13061641072655106680073913425089332), (Int.ofNat 192720202009011404663514017884646), (Int.negOfNat 262634495644492492001782994405411), (Int.ofNat 75260017281784679698741152306756), (Int.negOfNat 1698946599547185045603244114227), (Int.negOfNat 1725148012497724103138994278810), (Int.ofNat 108188969035236181930762683898), (Int.ofNat 20157993954373278852074426270), (Int.negOfNat 1605296804062292105251944135), (Int.negOfNat 152045960630492090039579132), (Int.ofNat 13499111940939818711810788), (Int.ofNat 812909051853521873971004), (Int.negOfNat 76247792921255144414526), (Int.negOfNat 3255896309040504672077), (Int.ofNat 313072838292818910207), (Int.ofNat 9866604769558963706), (Int.negOfNat 958367397907151437), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(3265410268163776670018478356272333/2814749767106560000000000000000000), (96360101004505702331757008942323/5629499534213120000000000000000000), (-262634495644492492001782994405411/11258999068426240000000000000000000), (18815004320446169924685288076689/2814749767106560000000000000000000), (-1698946599547185045603244114227/11258999068426240000000000000000000), (-172514801249772410313899427881/1125899906842624000000000000000000), (54094484517618090965381341949/5629499534213120000000000000000000), (2015799395437327885207442627/1125899906842624000000000000000000), (-321059360812458421050388827/2251799813685248000000000000000000), (-38011490157623022509894783/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial163.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial163.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial163.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial163 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 12925266418433089691877401547588468), (Int.negOfNat 119190517120782573053634745168636), (Int.ofNat 46246105077198450329424722241675), (Int.ofNat 17799534048894925086773685728909), (Int.negOfNat 9020578826405413290391874335677), (Int.ofNat 365127120421630767724557844325), (Int.ofNat 160842038172841383325658586554), (Int.negOfNat 12311820049635158348005324768), (Int.negOfNat 1512092547532680378023757004), (Int.ofNat 147117045567942719773228063), (Int.ofNat 9257761462389222326084408), (Int.negOfNat 1046164013479766483528551), (Int.negOfNat 40528570340565784573294), (Int.ofNat 5116709744429005416022), (Int.ofNat 134247050450202154643), (Int.negOfNat 18692754019043342355), (Int.negOfNat 301634110792153339), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(3231316604608272422969350386897117/2814749767106560000000000000000000), (-29797629280195643263408686292159/2814749767106560000000000000000000), (1849844203087938013176988889667/450359962737049600000000000000000), (17799534048894925086773685728909/11258999068426240000000000000000000), (-9020578826405413290391874335677/11258999068426240000000000000000000), (14605084816865230708982313773/450359962737049600000000000000000), (80421019086420691662829293277/5629499534213120000000000000000000), (-384744376551098698375166399/351843720888320000000000000000000), (-378023136883170094505939251/2814749767106560000000000000000000), (147117045567942719773228063/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial163.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial163.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial163.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial163 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 12890034304127364634979100020701134), (Int.ofNat 44131412717520497194287864450351), (Int.negOfNat 5868319833929317526337133081441), (Int.negOfNat 22743666242523730779961796522127), (Int.negOfNat 189406618016029698596477681858), (Int.ofNat 921586970726186546132499179152), (Int.negOfNat 67594086193505543157383697662), (Int.negOfNat 12394443030679701720434133546), (Int.ofNat 1321288826219530187414129327), (Int.ofNat 91813387771959048622121357), (Int.negOfNat 12425743244358300261515901), (Int.negOfNat 442737658906473084292140), (Int.ofNat 74208297214711221064277), (Int.ofNat 1508560399593451709168), (Int.negOfNat 314441979063876681313), (Int.negOfNat 3689114112178115039), (Int.ofNat 1037787401146501495), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(6445017152063682317489550010350567/5629499534213120000000000000000000), (44131412717520497194287864450351/11258999068426240000000000000000000), (-5868319833929317526337133081441/11258999068426240000000000000000000), (-22743666242523730779961796522127/11258999068426240000000000000000000), (-94703309008014849298238840929/5629499534213120000000000000000000), (57599185670386659133281198697/703687441776640000000000000000000), (-33797043096752771578691848831/5629499534213120000000000000000000), (-6197221515339850860217066773/5629499534213120000000000000000000), (1321288826219530187414129327/11258999068426240000000000000000000), (91813387771959048622121357/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial163.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial163.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial163.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial163 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 12793794226055193320641348440097603), (Int.negOfNat 201632892029596376902721522926267), (Int.negOfNat 95060413352180759440325459001797), (Int.negOfNat 2491040584945136813680933002938), (Int.ofNat 3174336472827718283846897860463), (Int.negOfNat 259238934522336840833253972497), (Int.negOfNat 75252597545051813689237443314), (Int.ofNat 9608921839880861114934378711), (Int.ofNat 742507873529975362575949313), (Int.negOfNat 126133308753704781101381440), (Int.negOfNat 4016472934424561153284838), (Int.ofNat 946870877956076975356645), (Int.ofNat 12965873480994626855773), (Int.negOfNat 4776636612101678653700), (Int.negOfNat 21921056206341881464), (Int.ofNat 17909386173310436605), (Int.negOfNat 47689275339773591), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(12793794226055193320641348440097603/11258999068426240000000000000000000), (-201632892029596376902721522926267/11258999068426240000000000000000000), (-95060413352180759440325459001797/11258999068426240000000000000000000), (-1245520292472568406840466501469/5629499534213120000000000000000000), (3174336472827718283846897860463/11258999068426240000000000000000000), (-259238934522336840833253972497/11258999068426240000000000000000000), (-37626298772525906844618721657/5629499534213120000000000000000000), (9608921839880861114934378711/11258999068426240000000000000000000), (742507873529975362575949313/11258999068426240000000000000000000), (-394166589855327440941817/35184372088832000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial163.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial163.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial163.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial163 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 12029389319591666241505766610810469), (Int.negOfNat 540611197663960770231091815386446), (Int.negOfNat 65435258349562036523408395465116), (Int.ofNat 6505536003477215406991235675861), (Int.negOfNat 933736937257618889884736954607), (Int.negOfNat 281382872083560874986277976578), (Int.ofNat 57919131400531556105077370214), (Int.ofNat 4291767952473294092152568633), (Int.negOfNat 1085416287843635435533228088), (Int.negOfNat 26071401397618315770857886), (Int.ofNat 10522138594811734905305240), (Int.ofNat 49414145011452013855052), (Int.negOfNat 64482214881052060629300), (Int.ofNat 288467432615769234975), (Int.ofNat 276759429005672726604), (Int.negOfNat 2679614096930318888), (Int.negOfNat 1000766275675209243), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(12029389319591666241505766610810469/11258999068426240000000000000000000), (-270305598831980385115545907693223/5629499534213120000000000000000000), (-16358814587390509130852098866279/2814749767106560000000000000000000), (6505536003477215406991235675861/11258999068426240000000000000000000), (-933736937257618889884736954607/11258999068426240000000000000000000), (-140691436041780437493138988289/5629499534213120000000000000000000), (28959565700265778052538685107/5629499534213120000000000000000000), (4291767952473294092152568633/11258999068426240000000000000000000), (-135677035980454429441653511/1407374883553280000000000000000000), (-13035700698809157885428943/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial163.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial163.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial163.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial163 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 10718501710091185944027696456455881), (Int.negOfNat 764751468954183438322859337230066), (Int.negOfNat 56484507797903071312106478389143), (Int.negOfNat 2477722465184425152222694479250), (Int.negOfNat 255798736639687191144975555168), (Int.ofNat 315467449429961301772857111521), (Int.ofNat 11452202151719548232097243996), (Int.negOfNat 7956781889292660770352615531), (Int.negOfNat 45809953766827349397726360), (Int.ofNat 100817435843255490992944420), (Int.negOfNat 965292857689467776136296), (Int.negOfNat 764527730641781312649132), (Int.ofNat 13090555941530196414944), (Int.ofNat 3902671948927387298157), (Int.negOfNat 82233482457312771756), (Int.negOfNat 14665562164719141908), (Int.ofNat 333518201587291583), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(10718501710091185944027696456455881/11258999068426240000000000000000000), (-382375734477091719161429668615033/5629499534213120000000000000000000), (-56484507797903071312106478389143/11258999068426240000000000000000000), (-9910889860737700608890777917/45035996273704960000000000000000), (-7993710519990224723280486099/351843720888320000000000000000000), (315467449429961301772857111521/11258999068426240000000000000000000), (2863050537929887058024310999/2814749767106560000000000000000000), (-7956781889292660770352615531/11258999068426240000000000000000000), (-1145248844170683734943159/281474976710656000000000000000000), (5040871792162774549647221/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial163.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial163.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial163.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial163 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 8948993033492397491220681859898586), (Int.negOfNat 1004563811958398249174868409598910), (Int.negOfNat 54499753110669528792181575218735), (Int.ofNat 5886454226341236284347392186371), (Int.ofNat 1670997083231020426404002856790), (Int.negOfNat 60651820185162451003441565552), (Int.negOfNat 50335203663476974118625548732), (Int.ofNat 1567891148856212906574002467), (Int.ofNat 824295166526425567132301861), (Int.negOfNat 28163337198551918282687514), (Int.negOfNat 7842850424328098129543234), (Int.ofNat 286324485357884692869455), (Int.ofNat 48211062890045677454257), (Int.negOfNat 1818996965542421342512), (Int.negOfNat 208085508104286648244), (Int.ofNat 8074622112120912071), (Int.ofNat 820830687080157995), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(4474496516746198745610340929949293/5629499534213120000000000000000000), (-100456381195839824917486840959891/1125899906842624000000000000000000), (-10899950622133905758436315043747/2251799813685248000000000000000000), (5886454226341236284347392186371/11258999068426240000000000000000000), (167099708323102042640400285679/1125899906842624000000000000000000), (-3790738761572653187715097847/703687441776640000000000000000000), (-12583800915869243529656387183/2814749767106560000000000000000000), (1567891148856212906574002467/11258999068426240000000000000000000), (824295166526425567132301861/11258999068426240000000000000000000), (-14081668599275959141343757/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial163.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial163.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial163.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial163 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 6790921697770487156965020281259812), (Int.negOfNat 1111524230449432856802508553313598), (Int.ofNat 6311902270695164816617410154238), (Int.ofNat 10874863619521850569238849336741), (Int.negOfNat 795024828670005780098874538762), (Int.negOfNat 271138873673916693488986488847), (Int.ofNat 25208026101068412087133207976), (Int.ofNat 5630731842326342802765241044), (Int.negOfNat 441162436171548982336902761), (Int.negOfNat 68001218035825566546814671), (Int.ofNat 4713685602954932425210735), (Int.ofNat 510875607690585846830360), (Int.negOfNat 33007082555954755691307), (Int.negOfNat 2603681995500015785960), (Int.ofNat 161214009800584187447), (Int.ofNat 9600871260990272515), (Int.negOfNat 529379333537283951), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(1697730424442621789241255070314953/2814749767106560000000000000000000), (-555762115224716428401254276656799/5629499534213120000000000000000000), (3155951135347582408308705077119/5629499534213120000000000000000000), (10874863619521850569238849336741/11258999068426240000000000000000000), (-397512414335002890049437269381/5629499534213120000000000000000000), (-271138873673916693488986488847/11258999068426240000000000000000000), (3151003262633551510891650997/1407374883553280000000000000000000), (1407682960581585700691310261/2814749767106560000000000000000000), (-441162436171548982336902761/11258999068426240000000000000000000), (-68001218035825566546814671/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial163.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial163.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial163.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial163 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 4660914926304030032000628992160643), (Int.negOfNat 996127119375775974124334001863125), (Int.ofNat 39585351794554403601263112366020), (Int.negOfNat 210897516897630415702825436842), (Int.negOfNat 1105627425436694622266138842593), (Int.ofNat 218709152443651298825871483038), (Int.ofNat 29941236936609150099965315862), (Int.negOfNat 5037256553799692190690921030), (Int.negOfNat 474328198479413718211121732), (Int.ofNat 63206897899498782628105271), (Int.ofNat 4440858877510200754044184), (Int.negOfNat 509496612941925951204029), (Int.negOfNat 27069812541984549165758), (Int.ofNat 2834043645245902004330), (Int.ofNat 115931697691492503583), (Int.negOfNat 11505323399165486421), (Int.negOfNat 471507300948231065), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(4660914926304030032000628992160643/11258999068426240000000000000000000), (-1593803391001241558598934402981/18014398509481984000000000000000), (1979267589727720180063155618301/562949953421312000000000000000000), (-105448758448815207851412718421/5629499534213120000000000000000000), (-1105627425436694622266138842593/11258999068426240000000000000000000), (109354576221825649412935741519/5629499534213120000000000000000000), (14970618468304575049982657931/5629499534213120000000000000000000), (-503725655379969219069092103/1125899906842624000000000000000000), (-118582049619853429552780433/2814749767106560000000000000000000), (63206897899498782628105271/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial163.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial163.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial163.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial163 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 2815809390749658248111007275547073), (Int.negOfNat 855031390385337131100950441644844), (Int.ofNat 32559229869777033536462616821566), (Int.ofNat 1196522955043189987371011016510), (Int.ofNat 1226965432384876833501496946961), (Int.ofNat 88817843291314475552979264312), (Int.negOfNat 44761638683925059590444400854), (Int.negOfNat 2295724942139169134563334668), (Int.ofNat 704661759499260405472948713), (Int.ofNat 28170593577522886841335346), (Int.negOfNat 6768822033701735514685588), (Int.negOfNat 209236707878101076607304), (Int.ofNat 43821817994978969439318), (Int.ofNat 1044828705921661217769), (Int.negOfNat 202803730223817620493), (Int.negOfNat 3668484532464320942), (Int.ofNat 608799336776634009), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(2815809390749658248111007275547073/11258999068426240000000000000000000), (-213757847596334282775237610411211/2814749767106560000000000000000000), (16279614934888516768231308410783/5629499534213120000000000000000000), (119652295504318998737101101651/1125899906842624000000000000000000), (1226965432384876833501496946961/11258999068426240000000000000000000), (11102230411414309444122408039/1407374883553280000000000000000000), (-22380819341962529795222200427/5629499534213120000000000000000000), (-573931235534792283640833667/2814749767106560000000000000000000), (704661759499260405472948713/11258999068426240000000000000000000), (14085296788761443420667673/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial163.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial163.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial163.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial163 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 1265058374936052292365754230401492), (Int.negOfNat 672940019370156570290630112571106), (Int.ofNat 65317190911856767580407703959924), (Int.ofNat 7423970450140141549697847877123), (Int.negOfNat 404641523576729680328806430914), (Int.negOfNat 324879556352189321517300386192), (Int.negOfNat 2224624275333524072942457029), (Int.ofNat 6566739385466778925422549533), (Int.ofNat 67487561506499163609835258), (Int.negOfNat 77322822131475389208271384), (Int.negOfNat 660122542029829650353044), (Int.ofNat 594033468456630173050799), (Int.ofNat 3690414646091190116079), (Int.negOfNat 3191037378838594583619), (Int.negOfNat 13230393483397957830), (Int.ofNat 12660148780823447943), (Int.ofNat 122183914816304135), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(316264593734013073091438557600373/2814749767106560000000000000000000), (-336470009685078285145315056285553/5629499534213120000000000000000000), (16329297727964191895101925989981/2814749767106560000000000000000000), (7423970450140141549697847877123/11258999068426240000000000000000000), (-202320761788364840164403215457/5629499534213120000000000000000000), (-20304972272011832594831274137/703687441776640000000000000000000), (-2224624275333524072942457029/11258999068426240000000000000000000), (6566739385466778925422549533/11258999068426240000000000000000000), (33743780753249581804917629/5629499534213120000000000000000000), (-9665352766434423651033923/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial163.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial163.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial163.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial163 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 223644837260049882875631509657833), (Int.negOfNat 359113543048876507647082347785486), (Int.ofNat 77811694492609521839316664461560), (Int.negOfNat 5767212719302141855973840036358), (Int.negOfNat 2168866604542951106537085365912), (Int.ofNat 85971032446208262241781114422), (Int.ofNat 51410293170837601453760833399), (Int.negOfNat 1227719219905041958541177330), (Int.negOfNat 753739479454721464881617138), (Int.ofNat 13156250331764647974975729), (Int.ofNat 7005875249014913553701671), (Int.negOfNat 100514952020907466510914), (Int.negOfNat 44328293952470103874826), (Int.ofNat 559463248711857580258), (Int.ofNat 201693060217864429796), (Int.negOfNat 2560486626902679731), (Int.negOfNat 688219340015984067), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(223644837260049882875631509657833/11258999068426240000000000000000000), (-179556771524438253823541173892743/5629499534213120000000000000000000), (1945292362315238045982916611539/281474976710656000000000000000000), (-2883606359651070927986920018179/5629499534213120000000000000000000), (-271108325567868888317135670739/1407374883553280000000000000000000), (42985516223104131120890557211/5629499534213120000000000000000000), (51410293170837601453760833399/11258999068426240000000000000000000), (-122771921990504195854117733/1125899906842624000000000000000000), (-376869739727360732440808569/5629499534213120000000000000000000), (13156250331764647974975729/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial163.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial163.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial163.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial163 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 258470281492379955215949026032256), (Int.negOfNat 170986425091387256656707920094775), (Int.ofNat 8331710852308419288432739962803), (Int.negOfNat 13322474779661307125649855397119), (Int.ofNat 725254177712868953052137729820), (Int.ofNat 338021823059884186029705646230), (Int.negOfNat 21656338256608285309702747382), (Int.negOfNat 6178994970608078598292242659), (Int.ofNat 318221113352865844936071803), (Int.ofNat 70817541643494599375546159), (Int.negOfNat 2933045019653174387167681), (Int.negOfNat 536423839159593132882058), (Int.ofNat 18541615553089907448988), (Int.ofNat 2857911794828597447290), (Int.negOfNat 84892620288507966909), (Int.negOfNat 11337126289427998032), (Int.ofNat 253612805728739481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-2019299074159218400124601765877/87960930222080000000000000000000), (-6839457003655490266268316803791/450359962737049600000000000000000), (8331710852308419288432739962803/11258999068426240000000000000000000), (-13322474779661307125649855397119/11258999068426240000000000000000000), (36262708885643447652606886491/562949953421312000000000000000000), (33802182305988418602970564623/1125899906842624000000000000000000), (-10828169128304142654851373691/5629499534213120000000000000000000), (-6178994970608078598292242659/11258999068426240000000000000000000), (318221113352865844936071803/11258999068426240000000000000000000), (70817541643494599375546159/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial163.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial163.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial163.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial163 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 653338519559442893033792209353646), (Int.negOfNat 253737048132880923787163114740635), (Int.negOfNat 35655743511783489645057506705249), (Int.negOfNat 38719807585642072896930862714), (Int.ofNat 1659118679675188608737337609629), (Int.negOfNat 192368826464481948105719129298), (Int.negOfNat 41084493365655360281115149758), (Int.ofNat 4192437550885216641185499361), (Int.ofNat 597192950710771819077499497), (Int.negOfNat 48962801182829378430161701), (Int.negOfNat 5519377213422906438040339), (Int.ofNat 370650236896348201750882), (Int.ofNat 34898779818009660261132), (Int.negOfNat 1966792105503909338770), (Int.negOfNat 159482160418380785811), (Int.ofNat 7884063345994011248), (Int.ofNat 508283751420932819), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-326669259779721446516896104676823/5629499534213120000000000000000000), (-50747409626576184757432622948127/2251799813685248000000000000000000), (-35655743511783489645057506705249/11258999068426240000000000000000000), (-19359903792821036448465431357/5629499534213120000000000000000000), (1659118679675188608737337609629/11258999068426240000000000000000000), (-96184413232240974052859564649/5629499534213120000000000000000000), (-20542246682827680140557574879/5629499534213120000000000000000000), (4192437550885216641185499361/11258999068426240000000000000000000), (597192950710771819077499497/11258999068426240000000000000000000), (-48962801182829378430161701/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial163.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial163.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial163.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial163 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 1285324983279121544754335309450703), (Int.negOfNat 364657011063164476986453117163284), (Int.negOfNat 17708284529282759864094061583014), (Int.ofNat 2054799709251393885297191110424), (Int.negOfNat 1139278743624778548916428980277), (Int.negOfNat 195179068356673762407053241492), (Int.ofNat 40059578025161542449197952101), (Int.ofNat 3969109954889631058080658070), (Int.negOfNat 615799258606916449640767402), (Int.negOfNat 46001694924251595708858471), (Int.ofNat 5745527447234208388672769), (Int.ofNat 352260413690366551226086), (Int.negOfNat 36146709261275784946674), (Int.negOfNat 1902832297444691471322), (Int.ofNat 163403298759238879224), (Int.ofNat 7833365725704870929), (Int.negOfNat 539441731976257473), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-1285324983279121544754335309450703/11258999068426240000000000000000000), (-91164252765791119246613279290821/2814749767106560000000000000000000), (-8854142264641379932047030791507/5629499534213120000000000000000000), (256849963656424235662148888803/1407374883553280000000000000000000), (-1139278743624778548916428980277/11258999068426240000000000000000000), (-48794767089168440601763310373/2814749767106560000000000000000000), (40059578025161542449197952101/11258999068426240000000000000000000), (396910995488963105808065807/1125899906842624000000000000000000), (-307899629303458224820383701/5629499534213120000000000000000000), (-46001694924251595708858471/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial163.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial163.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial163.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial163 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 2090610830244445063130850623183591), (Int.negOfNat 454138348403390072611724584826425), (Int.negOfNat 37297021462507435022165743919255), (Int.negOfNat 7486540984568811406932196671783), (Int.negOfNat 364311309249787727541222141764), (Int.ofNat 302965381284822107826027343916), (Int.ofNat 17841857198988766870658213369), (Int.negOfNat 6176649264079908840346226547), (Int.negOfNat 273678084293730337446176078), (Int.ofNat 73004240890768634755855136), (Int.ofNat 2621585204244064524890024), (Int.negOfNat 556582694606921120736501), (Int.negOfNat 17291744516235131286479), (Int.ofNat 2953615200075653825581), (Int.ofNat 81774906063850100330), (Int.negOfNat 11662262018672466037), (Int.negOfNat 185433699702122575), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-2090610830244445063130850623183591/11258999068426240000000000000000000), (-18165533936135602904468983393057/450359962737049600000000000000000), (-7459404292501487004433148783851/2251799813685248000000000000000000), (-7486540984568811406932196671783/11258999068426240000000000000000000), (-91077827312446931885305535441/2814749767106560000000000000000000), (75741345321205526956506835979/2814749767106560000000000000000000), (17841857198988766870658213369/11258999068426240000000000000000000), (-6176649264079908840346226547/11258999068426240000000000000000000), (-136839042146865168723088039/5629499534213120000000000000000000), (2281382527836519836120473/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial163.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial163.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial163.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial163 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 3203781946240150438281514790988312), (Int.negOfNat 680032312356333573518195227097922), (Int.negOfNat 66731347608696334819985092401975), (Int.ofNat 1031110777324093689719110730764), (Int.ofNat 2004890627475029467090376885741), (Int.ofNat 26748779017037213446284389406), (Int.negOfNat 49985825844507877027596588590), (Int.negOfNat 562586030640285757227976228), (Int.ofNat 768106851114617601860289127), (Int.ofNat 7724668919108927097483706), (Int.negOfNat 7278629892800233787697792), (Int.negOfNat 74080953858010864687724), (Int.ofNat 46201483210787757347822), (Int.ofNat 485990578737449316069), (Int.negOfNat 209139453701302411427), (Int.negOfNat 2418224014007640602), (Int.ofNat 618861735215607531), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-400472743280018804785189348873539/1407374883553280000000000000000000), (-340016156178166786759097613548961/5629499534213120000000000000000000), (-2669253904347853392799403696079/450359962737049600000000000000000), (257777694331023422429777682691/2814749767106560000000000000000000), (2004890627475029467090376885741/11258999068426240000000000000000000), (13374389508518606723142194703/5629499534213120000000000000000000), (-4998582584450787702759658859/1125899906842624000000000000000000), (-140646507660071439306994057/2814749767106560000000000000000000), (768106851114617601860289127/11258999068426240000000000000000000), (3862334459554463548741853/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial163.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial163.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial163.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial163 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 4792666792951111480469293696375515), (Int.negOfNat 877369913008803652244193335591694), (Int.negOfNat 21332833217648316773780924475371), (Int.ofNat 11135642466878773466221315834052), (Int.negOfNat 88006689273044419222235319625), (Int.negOfNat 316910196486802952759381027564), (Int.ofNat 10483507374536282901640378448), (Int.ofNat 6593609137705221157271741610), (Int.negOfNat 154623403581579919821360388), (Int.negOfNat 80372980987965112240361889), (Int.ofNat 1190978251890260393939396), (Int.ofNat 624858933274634882139831), (Int.negOfNat 5621718834295394986002), (Int.negOfNat 3355141916416340219230), (Int.ofNat 16683106293793132977), (Int.ofNat 13260663415978639859), (Int.negOfNat 163889686429804355), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-958533358590222296093858739275103/2251799813685248000000000000000000), (-438684956504401826122096667795847/5629499534213120000000000000000000), (-21332833217648316773780924475371/11258999068426240000000000000000000), (2783910616719693366555328958513/2814749767106560000000000000000000), (-704053514184355353777882557/90071992547409920000000000000000), (-79227549121700738189845256891/2814749767106560000000000000000000), (655219210908517681352523653/703687441776640000000000000000000), (659360913770522115727174161/1125899906842624000000000000000000), (-38655850895394979955340097/2814749767106560000000000000000000), (-80372980987965112240361889/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial163.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial163.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial163.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial163 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 6553765404069942488741408298396318), (Int.negOfNat 852606484914280333432251490540250), (Int.ofNat 24345966239075002362210103822750), (Int.ofNat 2458901399562706822900982450020), (Int.negOfNat 1238616308319918327357756624945), (Int.ofNat 157913055515370211104609615396), (Int.ofNat 43681359808728494704864734944), (Int.negOfNat 3494216597697256741355408656), (Int.negOfNat 731312571350204790925267999), (Int.ofNat 37664451169753529634616989), (Int.ofNat 7205484828135371480159505), (Int.negOfNat 253478126959669098680300), (Int.negOfNat 46842569632655616515853), (Int.ofNat 1169642647999286276560), (Int.ofNat 216368601397216257813), (Int.negOfNat 3759266643373208065), (Int.negOfNat 698281738454957589), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-3276882702034971244370704149198159/5629499534213120000000000000000000), (-3410425939657121333729005962161/45035996273704960000000000000000), (97383864956300009448840415291/45035996273704960000000000000000), (122945069978135341145049122501/562949953421312000000000000000000), (-247723261663983665471551324989/2251799813685248000000000000000000), (39478263878842552776152403849/2814749767106560000000000000000000), (1365042494022765459527022967/351843720888320000000000000000000), (-218388537356078546334713041/703687441776640000000000000000000), (-731312571350204790925267999/11258999068426240000000000000000000), (37664451169753529634616989/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial163.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial163.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial163.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial163 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 8154500845051537962873357746558597), (Int.negOfNat 746526182329706953883832124036392), (Int.ofNat 29077052070691711029953020302397), (Int.ofNat 2885907221744524565484411875580), (Int.ofNat 1396640244270643490254473165920), (Int.ofNat 183328397618046413216490745926), (Int.negOfNat 43734177543827570340446518928), (Int.negOfNat 5167047340878594409796985073), (Int.ofNat 622227868907775621446509839), (Int.ofNat 68536790118615825163027946), (Int.negOfNat 5316986937628205892903086), (Int.negOfNat 558493445956012976279565), (Int.ofNat 30313661332743256476443), (Int.ofNat 3090842777465587793348), (Int.negOfNat 123439624041781683836), (Int.negOfNat 12477295570245734109), (Int.ofNat 513213072561731285), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-8154500845051537962873357746558597/11258999068426240000000000000000000), (-93315772791213369235479015504549/1407374883553280000000000000000000), (29077052070691711029953020302397/11258999068426240000000000000000000), (144295361087226228274220593779/562949953421312000000000000000000), (8729001526691521814090457287/70368744177664000000000000000000), (91664198809023206608245372963/5629499534213120000000000000000000), (-2733386096489223146277907433/703687441776640000000000000000000), (-5167047340878594409796985073/11258999068426240000000000000000000), (622227868907775621446509839/11258999068426240000000000000000000), (34268395059307912581513973/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial163.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial163.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial163.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial163 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 9483217420568892806123684973062209), (Int.negOfNat 546177678147870230783474648569950), (Int.ofNat 81966032467841957560631568763704), (Int.ofNat 12883583541857982079408548156250), (Int.ofNat 42100199216097412750592650123), (Int.negOfNat 414043921581260311488374056219), (Int.negOfNat 24099460724713120615217393846), (Int.ofNat 7640780164495171976459826129), (Int.ofNat 496756922264264662379737880), (Int.negOfNat 83071147312414879351663780), (Int.negOfNat 5421415039176020900255764), (Int.ofNat 581075282579152983841268), (Int.ofNat 37567663013250226563636), (Int.negOfNat 2818422148451652358823), (Int.negOfNat 179967975574002970384), (Int.ofNat 10127994852481641992), (Int.ofNat 661260612983665337), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-9483217420568892806123684973062209/11258999068426240000000000000000000), (-10923553562957404615669492971399/225179981368524800000000000000000), (10245754058480244695078946095463/1407374883553280000000000000000000), (412274673339455426541073541/360287970189639680000000000000), (42100199216097412750592650123/11258999068426240000000000000000000), (-414043921581260311488374056219/11258999068426240000000000000000000), (-12049730362356560307608696923/5629499534213120000000000000000000), (7640780164495171976459826129/11258999068426240000000000000000000), (12418923056606616559493447/281474976710656000000000000000000), (-4153557365620743967583189/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial163.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial163.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial163.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial163 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 10157699722531039172814971281325427), (Int.negOfNat 96394054061356469243333780717099), (Int.ofNat 126968494652721778907447535844975), (Int.negOfNat 2530285936251918491407024980963), (Int.negOfNat 3228206395453505271860592375829), (Int.negOfNat 30142517989831378643730451239), (Int.ofNat 74553154106913674439408525086), (Int.ofNat 2073179143210986321972478133), (Int.negOfNat 1050579636053050431488635832), (Int.negOfNat 37390906664372031657207366), (Int.ofNat 9152347797791881605215540), (Int.ofNat 359551765209152405864412), (Int.negOfNat 53224314191478008516240), (Int.negOfNat 2183430816559080320725), (Int.ofNat 221121648314740111056), (Int.ofNat 9233471561654439412), (Int.negOfNat 799041998809249277), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-10157699722531039172814971281325427/11258999068426240000000000000000000), (-96394054061356469243333780717099/11258999068426240000000000000000000), (5078739786108871156297901433799/450359962737049600000000000000000), (-2530285936251918491407024980963/11258999068426240000000000000000000), (-3228206395453505271860592375829/11258999068426240000000000000000000), (-30142517989831378643730451239/11258999068426240000000000000000000), (37276577053456837219704262543/5629499534213120000000000000000000), (2073179143210986321972478133/11258999068426240000000000000000000), (-131322454506631303936079479/1407374883553280000000000000000000), (-18695453332186015828603683/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial163.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial163.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial163.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial163 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 9910713449814274022124075223928192), (Int.ofNat 289533047874508435447550611388379), (Int.ofNat 49241124647561358770684193259509), (Int.negOfNat 18406493282470378642035829253143), (Int.ofNat 327536817201230315115820760928), (Int.ofNat 571171919414849754255219918893), (Int.negOfNat 6585898251829398042535582706), (Int.negOfNat 10916450967692108193884995069), (Int.negOfNat 65449127667941594508073893), (Int.ofNat 122096193899517962919318820), (Int.ofNat 2042369604659268468408278), (Int.negOfNat 864770126296781439165735), (Int.negOfNat 19406440475448228832873), (Int.ofNat 4229202936892725057280), (Int.ofNat 107852631003249974824), (Int.negOfNat 15523002867672235175), (Int.negOfNat 481325024388614089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-77427448826674015797844337686939/87960930222080000000000000000000), (289533047874508435447550611388379/11258999068426240000000000000000000), (49241124647561358770684193259509/11258999068426240000000000000000000), (-18406493282470378642035829253143/11258999068426240000000000000000000), (10235525537538447347369398779/351843720888320000000000000000000), (571171919414849754255219918893/11258999068426240000000000000000000), (-3292949125914699021267791353/5629499534213120000000000000000000), (-10916450967692108193884995069/11258999068426240000000000000000000), (-65449127667941594508073893/11258999068426240000000000000000000), (6104809694975898145965941/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial163.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial163.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial163.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial163 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 9260189479440987792959579895055722), (Int.ofNat 315854258849051214808055583428171), (Int.negOfNat 16115767532984612537386727671924), (Int.ofNat 426771985289651784309957376779), (Int.ofNat 2996560700833706724839490672596), (Int.negOfNat 217629003285902340085952229438), (Int.negOfNat 90797570919012649830093868698), (Int.ofNat 3006159960447552844635654194), (Int.ofNat 1386214014798150755771875273), (Int.negOfNat 11389413168296326421983863), (Int.negOfNat 12268050580525640131435699), (Int.negOfNat 51624994771154615901920), (Int.ofNat 71417648027866632263363), (Int.ofNat 760525895950010425848), (Int.negOfNat 296837463811008230827), (Int.negOfNat 4168780657925570019), (Int.ofNat 994903130759241645), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-4630094739720493896479789947527861/5629499534213120000000000000000000), (315854258849051214808055583428171/11258999068426240000000000000000000), (-4028941883246153134346681917981/2814749767106560000000000000000000), (426771985289651784309957376779/11258999068426240000000000000000000), (749140175208426681209872668149/2814749767106560000000000000000000), (-108814501642951170042976114719/5629499534213120000000000000000000), (-45398785459506324915046934349/5629499534213120000000000000000000), (1503079980223776422317827097/5629499534213120000000000000000000), (1386214014798150755771875273/11258999068426240000000000000000000), (-11389413168296326421983863/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial163.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial163.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial163.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial163 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 8653638603934306520826105162833131), (Int.ofNat 320237309831114695876962719787557), (Int.ofNat 23474390510068019405658655405799), (Int.ofNat 5090226074673012346480411440093), (Int.negOfNat 2437265236006088502375650489936), (Int.negOfNat 549893997093390114975328112776), (Int.ofNat 61066079325214768213712207822), (Int.ofNat 13257259334152074144928359152), (Int.negOfNat 555664681093130555377186076), (Int.negOfNat 152695815750064762174295257), (Int.ofNat 2516676520717301720583052), (Int.ofNat 1075373733061931183685549), (Int.negOfNat 4910507523646050492306), (Int.negOfNat 5218566709612770219538), (Int.negOfNat 9371571414251780643), (Int.ofNat 18953704154716809525), (Int.ofNat 132001638256687159), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-8653638603934306520826105162833131/11258999068426240000000000000000000), (320237309831114695876962719787557/11258999068426240000000000000000000), (23474390510068019405658655405799/11258999068426240000000000000000000), (5090226074673012346480411440093/11258999068426240000000000000000000), (-152329077250380531398478155621/703687441776640000000000000000000), (-68736749636673764371916014097/1407374883553280000000000000000000), (30533039662607384106856103911/5629499534213120000000000000000000), (828578708384504634058022447/703687441776640000000000000000000), (-138916170273282638844296519/2814749767106560000000000000000000), (-152695815750064762174295257/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial163.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial163.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial163.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial163 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 7929748020418281354977382413481376), (Int.ofNat 370001308468875639560343368613473), (Int.negOfNat 26546652721487845504084241446937), (Int.negOfNat 20943634984378187501394785074783), (Int.negOfNat 1721463630687376721223022195656), (Int.ofNat 789658154207269916950740548330), (Int.ofNat 104780018347154791605311983056), (Int.negOfNat 10198697590924537055919704810), (Int.negOfNat 1672121926432256780292518505), (Int.ofNat 71123938889463296645332668), (Int.ofNat 14516425114051858230847552), (Int.negOfNat 314670456039181230109176), (Int.negOfNat 82868571589449800248854), (Int.ofNat 946020615878731716623), (Int.ofNat 340498327757436103153), (Int.negOfNat 1763606070600381554), (Int.negOfNat 1074323133998591703), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-247804625638071292343043200421293/351843720888320000000000000000000), (370001308468875639560343368613473/11258999068426240000000000000000000), (-26546652721487845504084241446937/11258999068426240000000000000000000), (-20943634984378187501394785074783/11258999068426240000000000000000000), (-215182953835922090152877774457/1407374883553280000000000000000000), (78965815420726991695074054833/1125899906842624000000000000000000), (6548751146697174475331998941/703687441776640000000000000000000), (-1019869759092453705591970481/1125899906842624000000000000000000), (-334424385286451356058503701/2251799813685248000000000000000000), (17780984722365824161333167/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial163.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial163.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial163.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial163 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 7460732717133498205439258296295609), (Int.ofNat 34646089086386310314250053650617), (Int.negOfNat 114572919396539049524870767006097), (Int.ofNat 5511302959472140769236917175641), (Int.ofNat 8192268924568444112415315819990), (Int.ofNat 684603824294036660527508160713), (Int.negOfNat 137805447240722499939866544049), (Int.negOfNat 16292467894315428189572194695), (Int.ofNat 1248817857464587125531260230), (Int.ofNat 176909305976166999748767650), (Int.negOfNat 7363553996824357553137592), (Int.negOfNat 1195846929054257259906759), (Int.ofNat 31045849354825357691065), (Int.ofNat 5659945444578394387907), (Int.negOfNat 99189739718698840390), (Int.negOfNat 20108529536374771047), (Int.ofNat 217321747875239771), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-7460732717133498205439258296295609/11258999068426240000000000000000000), (34646089086386310314250053650617/11258999068426240000000000000000000), (-114572919396539049524870767006097/11258999068426240000000000000000000), (5511302959472140769236917175641/11258999068426240000000000000000000), (819226892456844411241531581999/1125899906842624000000000000000000), (684603824294036660527508160713/11258999068426240000000000000000000), (-137805447240722499939866544049/11258999068426240000000000000000000), (-3258493578863085637914438939/2251799813685248000000000000000000), (124881785746458712553126023/1125899906842624000000000000000000), (3538186119523339994975353/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial163.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial163.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial163.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial163 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 7663162695385002866927793739880112), (Int.negOfNat 72710447608621840509023502395513), (Int.ofNat 128793338004388382655665804941051), (Int.ofNat 70291327928530246342811004016769), (Int.ofNat 4176436096170180253935973224496), (Int.negOfNat 1511395495157497469888155401141), (Int.negOfNat 146615415086741988863645183161), (Int.ofNat 17114823084083432699258691128), (Int.ofNat 1974121957913171924634660770), (Int.negOfNat 126137936759929944813140023), (Int.negOfNat 15783342504160343450646715), (Int.ofNat 663723094422616621645034), (Int.ofNat 86145539362841137793442), (Int.negOfNat 2633404245226210632290), (Int.negOfNat 344957134247354634776), (Int.ofNat 7992577229967382227), (Int.ofNat 1153743137237941761), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-478947668461562679182987108742507/703687441776640000000000000000000), (-72710447608621840509023502395513/11258999068426240000000000000000000), (128793338004388382655665804941051/11258999068426240000000000000000000), (70291327928530246342811004016769/11258999068426240000000000000000000), (261027256010636265870998326531/703687441776640000000000000000000), (-1511395495157497469888155401141/11258999068426240000000000000000000), (-146615415086741988863645183161/11258999068426240000000000000000000), (2139352885510429087407336391/1407374883553280000000000000000000), (197412195791317192463466077/1125899906842624000000000000000000), (-126137936759929944813140023/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial163.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial163.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial163.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial163 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 6719387666957597956458553204629760), (Int.ofNat 1279869920439556184318545937979989), (Int.ofNat 508976124786439729398023297400776), (Int.ofNat 32026638696172066449160055504454), (Int.negOfNat 13414328437021283952771956804839), (Int.negOfNat 1303128950502743645878919357367), (Int.ofNat 190389118354169339501032128414), (Int.ofNat 20650980362098761952283018061), (Int.negOfNat 1743868335431137613311304011), (Int.negOfNat 192411584398570215559695505), (Int.ofNat 11262622117497674358782437), (Int.ofNat 1206297853090364050647338), (Int.negOfNat 53946419903944191494492), (Int.negOfNat 5474638869250270605058), (Int.ofNat 198594677725595432409), (Int.ofNat 18785507044979321136), (Int.negOfNat 593118468420283387), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-5249521614810623403483244691117/8796093022208000000000000000000), (1279869920439556184318545937979989/11258999068426240000000000000000000), (63622015598304966174752912175097/1407374883553280000000000000000000), (16013319348086033224580027752227/5629499534213120000000000000000000), (-13414328437021283952771956804839/11258999068426240000000000000000000), (-1303128950502743645878919357367/11258999068426240000000000000000000), (95194559177084669750516064207/5629499534213120000000000000000000), (20650980362098761952283018061/11258999068426240000000000000000000), (-1743868335431137613311304011/11258999068426240000000000000000000), (-38482316879714043111939101/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial163.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial163.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial163.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial163.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial163 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial163 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial163 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 9795014553569255794066376871528198), (Int.negOfNat 1741919392739152758953880637306447), (Int.ofNat 599735496820125160744896427077480), (Int.negOfNat 28124736780386811451360367395665), (Int.negOfNat 13897554087132417768230730845973), (Int.ofNat 1291946187201794206696419388630), (Int.ofNat 191467229811340342351708517900), (Int.negOfNat 20634283674412948141386200061), (Int.negOfNat 1745189134684479529403333611), (Int.ofNat 192396224110812312374908705), (Int.ofNat 11263640286886968813634837), (Int.negOfNat 1206287814621631657056938), (Int.negOfNat 53946419903944191494492), (Int.ofNat 5474638869250270605058), (Int.ofNat 198594677725595432409), (Int.negOfNat 18785507044979321136), (Int.negOfNat 593118468420283387), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-4897507276784627897033188435764099/5629499534213120000000000000000000), (-1741919392739152758953880637306447/11258999068426240000000000000000000), (14993387420503129018622410676937/281474976710656000000000000000000), (-5624947356077362290272073479133/2251799813685248000000000000000000), (-13897554087132417768230730845973/11258999068426240000000000000000000), (129194618720179420669641938863/1125899906842624000000000000000000), (1914672298113403423517085179/112589990684262400000000000000000), (-20634283674412948141386200061/11258999068426240000000000000000000), (-1745189134684479529403333611/11258999068426240000000000000000000), (38479244822162462474981741/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial163.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial163.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial163.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 11276654490581103257385258903877135), (Int.ofNat 4376539505195133157807046610847), (Int.ofNat 230739626110628708508929261172237), (Int.negOfNat 70523127219546993218562244148810), (Int.ofNat 3649217377705936172127895673033), (Int.ofNat 1513938352595067704334272913867), (Int.negOfNat 145458268359573609211641961561), (Int.negOfNat 17120456195085622378432551128), (Int.ofNat 1972716335019370073338128770), (Int.ofNat 126144077569716327360394423), (Int.negOfNat 15782262589339289057740315), (Int.negOfNat 663726858848391269241434), (Int.ofNat 86145539362841137793442), (Int.ofNat 2633404245226210632290), (Int.negOfNat 344957134247354634776), (Int.negOfNat 7992577229967382227), (Int.ofNat 1153743137237941761), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-2255330898116220651477051780775427/2251799813685248000000000000000000), (4376539505195133157807046610847/11258999068426240000000000000000000), (230739626110628708508929261172237/11258999068426240000000000000000000), (-7052312721954699321856224414881/1125899906842624000000000000000000), (3649217377705936172127895673033/11258999068426240000000000000000000), (1513938352595067704334272913867/11258999068426240000000000000000000), (-145458268359573609211641961561/11258999068426240000000000000000000), (-2140057024385702797304068891/1407374883553280000000000000000000), (197271633501937007333812877/1125899906842624000000000000000000), (126144077569716327360394423/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial163.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial163.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial163.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 10813242717745262408126449073191921), (Int.ofNat 285574222143587751346593343443979), (Int.negOfNat 26195796214698408972684449212457), (Int.negOfNat 9679618280398900507662410253091), (Int.ofNat 7756795044114370508263749010001), (Int.negOfNat 669257196312775328756995562629), (Int.negOfNat 136876932256075840179966891049), (Int.ofNat 16266230104637588521146742695), (Int.ofNat 1247707364597940329734027030), (Int.negOfNat 176883435480769415344557650), (Int.negOfNat 7362706466655087593533592), (Int.ofNat 1195830616542567120322359), (Int.ofNat 31045849354825357691065), (Int.negOfNat 5659945444578394387907), (Int.negOfNat 99189739718698840390), (Int.ofNat 20108529536374771047), (Int.ofNat 217321747875239771), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-10813242717745262408126449073191921/11258999068426240000000000000000000), (285574222143587751346593343443979/11258999068426240000000000000000000), (-26195796214698408972684449212457/11258999068426240000000000000000000), (-9679618280398900507662410253091/11258999068426240000000000000000000), (7756795044114370508263749010001/11258999068426240000000000000000000), (-669257196312775328756995562629/11258999068426240000000000000000000), (-136876932256075840179966891049/11258999068426240000000000000000000), (3253246020927517704229348539/2251799813685248000000000000000000), (124770736459794032973402703/1125899906842624000000000000000000), (-3537668709615388306891153/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial163.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial163.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial163.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 10328076122088749951399021358450712), (Int.ofNat 241165724649384753138366000889774), (Int.ofNat 27800285914064831656115668199411), (Int.ofNat 14037424311925036514358894590544), (Int.negOfNat 1956235727331570928723335381313), (Int.negOfNat 765812370671238309488813535170), (Int.ofNat 105236789443858786968643993742), (Int.ofNat 10159132146177456773424373610), (Int.negOfNat 1672639436323517207867359305), (Int.negOfNat 71085474500858598063064668), (Int.ofNat 14516808365042254986895552), (Int.ofNat 314646614675941795331976), (Int.negOfNat 82868571589449800248854), (Int.negOfNat 946020615878731716623), (Int.ofNat 340498327757436103153), (Int.ofNat 1763606070600381554), (Int.negOfNat 1074323133998591703), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-1291009515261093743924877669806339/1407374883553280000000000000000000), (120582862324692376569183000444887/5629499534213120000000000000000000), (27800285914064831656115668199411/11258999068426240000000000000000000), (877339019495314782147430911909/703687441776640000000000000000000), (-1956235727331570928723335381313/11258999068426240000000000000000000), (-76581237067123830948881353517/1125899906842624000000000000000000), (52618394721929393484321996871/5629499534213120000000000000000000), (1015913214617745677342437361/1125899906842624000000000000000000), (-334527887264703441573471861/2251799813685248000000000000000000), (-17771368625214649515766167/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial163.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial163.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial163.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 9670463802152552043902143094660048), (Int.ofNat 419907440456151845951096014573736), (Int.ofNat 32739488139710393083241297268845), (Int.negOfNat 12870571211552305654777179428529), (Int.negOfNat 2417671983019084985502829612903), (Int.ofNat 575745586089257975499874315995), (Int.ofNat 60937737381440780796771504646), (Int.negOfNat 13299331339195270916948248352), (Int.negOfNat 555454311596531541881128076), (Int.ofNat 152736332355402117723925657), (Int.ofNat 2516492843286666070297852), (Int.negOfNat 1075400084042353716860349), (Int.negOfNat 4910507523646050492306), (Int.ofNat 5218566709612770219538), (Int.negOfNat 9371571414251780643), (Int.negOfNat 18953704154716809525), (Int.ofNat 132001638256687159), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-604403987634534502743883943416253/703687441776640000000000000000000), (52488430057018980743887001821717/1407374883553280000000000000000000), (6547897627942078616648259453769/2251799813685248000000000000000000), (-12870571211552305654777179428529/11258999068426240000000000000000000), (-2417671983019084985502829612903/11258999068426240000000000000000000), (115149117217851595099974863199/2251799813685248000000000000000000), (30468868690720390398385752323/5629499534213120000000000000000000), (-415604104349852216154632761/351843720888320000000000000000000), (-138863577899132885470282019/2814749767106560000000000000000000), (152736332355402117723925657/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial163.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial163.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial163.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 8820780329507094670868738777849074), (Int.ofNat 370638669163131872112594881136329), (Int.negOfNat 51052889127493325921730856896379), (Int.negOfNat 7059811653699983221476408643633), (Int.ofNat 3255584615615161075560204421038), (Int.ofNat 238580146875894645175607224588), (Int.negOfNat 91465118263012717245947161098), (Int.negOfNat 3039339068060631769996960994), (Int.ofNat 1387088117539065817228231273), (Int.ofNat 11420926258751911240879863), (Int.negOfNat 12268747229607871572505699), (Int.ofNat 51604917833689828721120), (Int.ofNat 71417648027866632263363), (Int.negOfNat 760525895950010425848), (Int.negOfNat 296837463811008230827), (Int.ofNat 4168780657925570019), (Int.ofNat 994903130759241645), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-4410390164753547335434369388924537/5629499534213120000000000000000000), (370638669163131872112594881136329/11258999068426240000000000000000000), (-51052889127493325921730856896379/11258999068426240000000000000000000), (-7059811653699983221476408643633/11258999068426240000000000000000000), (1627792307807580537780102210519/5629499534213120000000000000000000), (59645036718973661293901806147/2814749767106560000000000000000000), (-45732559131506358622973580549/5629499534213120000000000000000000), (-1519669534030315884998480497/5629499534213120000000000000000000), (1387088117539065817228231273/11258999068426240000000000000000000), (11420926258751911240879863/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial163.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial163.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial163.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 8286363159152644134007685523588203), (Int.ofNat 187437705077908978546354259146907), (Int.negOfNat 17782374185637662549938038986123), (Int.ofNat 14560027120581614127235866593218), (Int.ofNat 747825088729885672337554610597), (Int.negOfNat 560569420700131835186157117543), (Int.negOfNat 7601485498281235885781384306), (Int.ofNat 10901032605181288358974267069), (Int.negOfNat 64156016436520159435591893), (Int.negOfNat 122082224223326225168813620), (Int.ofNat 2041352719575417954331478), (Int.ofNat 864762597445232143972935), (Int.negOfNat 19406440475448228832873), (Int.negOfNat 4229202936892725057280), (Int.ofNat 107852631003249974824), (Int.ofNat 15523002867672235175), (Int.negOfNat 481325024388614089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-8286363159152644134007685523588203/11258999068426240000000000000000000), (187437705077908978546354259146907/11258999068426240000000000000000000), (-17782374185637662549938038986123/11258999068426240000000000000000000), (7280013560290807063617933296609/5629499534213120000000000000000000), (747825088729885672337554610597/11258999068426240000000000000000000), (-560569420700131835186157117543/11258999068426240000000000000000000), (-3800742749140617942890692153/5629499534213120000000000000000000), (10901032605181288358974267069/11258999068426240000000000000000000), (-64156016436520159435591893/11258999068426240000000000000000000), (-6104111211166311258440681/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial163.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial163.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial163.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 7871276392291284282858062695229529), (Int.ofNat 273210093188237525944753984365686), (Int.ofNat 47549584890963147958289894468376), (Int.ofNat 2301474089055851587183433006819), (Int.negOfNat 2765654861734526308214647574513), (Int.ofNat 27861906751304107340007035838), (Int.ofNat 73472415357626156063855914286), (Int.negOfNat 2066903431116699286604790533), (Int.negOfNat 1049225007062630040144845432), (Int.ofNat 37383637798644538870866966), (Int.ofNat 9151291248957797179825940), (Int.negOfNat 359545491166194659870412), (Int.negOfNat 53224314191478008516240), (Int.ofNat 2183430816559080320725), (Int.ofNat 221121648314740111056), (Int.negOfNat 9233471561654439412), (Int.negOfNat 799041998809249277), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-7871276392291284282858062695229529/11258999068426240000000000000000000), (136605046594118762972376992182843/5629499534213120000000000000000000), (5943698111370393494786236808547/1407374883553280000000000000000000), (2301474089055851587183433006819/11258999068426240000000000000000000), (-2765654861734526308214647574513/11258999068426240000000000000000000), (13930953375652053670003517919/5629499534213120000000000000000000), (36736207678813078031927957143/5629499534213120000000000000000000), (-2066903431116699286604790533/11258999068426240000000000000000000), (-131153125882828755018105679/1407374883553280000000000000000000), (18691818899322269435433483/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial163.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial163.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial163.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 7155408322915961035591107671680781), (Int.ofNat 416988210968673637776764536327486), (Int.ofNat 11840261508358458194586067307743), (Int.negOfNat 9670238920817153886193730271030), (Int.ofNat 420232441057994487375018801848), (Int.ofNat 399905501938163843302532067179), (Int.negOfNat 24948952007633883592315342336), (Int.negOfNat 7614851852935518514761777729), (Int.ofNat 497801311047413170701185480), (Int.ofNat 83044783386740824786250980), (Int.negOfNat 5422222645784282921234164), (Int.negOfNat 581057715258871295058068), (Int.ofNat 37567663013250226563636), (Int.ofNat 2818422148451652358823), (Int.negOfNat 179967975574002970384), (Int.negOfNat 10127994852481641992), (Int.ofNat 661260612983665337), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-7155408322915961035591107671680781/11258999068426240000000000000000000), (208494105484336818888382268163743/5629499534213120000000000000000000), (11840261508358458194586067307743/11258999068426240000000000000000000), (-967023892081715388619373027103/1125899906842624000000000000000000), (52529055132249310921877350231/1407374883553280000000000000000000), (399905501938163843302532067179/11258999068426240000000000000000000), (-48728421889909928891240903/21990232555520000000000000000000), (-7614851852935518514761777729/11258999068426240000000000000000000), (12445032776185329267529637/281474976710656000000000000000000), (4152239169337041239312549/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial163.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial163.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial163.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 6334320117729291267851324174915266), (Int.ofNat 386212443268337144788698275160090), (Int.negOfNat 14009263748097396341242011543225), (Int.ofNat 2667277972749087692673528842489), (Int.ofNat 1590732076056171749147796873530), (Int.negOfNat 205073963180301281184866625208), (Int.negOfNat 44123854000038431385809280128), (Int.ofNat 5205214702788607594191676273), (Int.ofNat 622678040615820394009002639), (Int.negOfNat 68574874555559525775678746), (Int.negOfNat 5317322996016819442445486), (Int.ofNat 558518542127843960255565), (Int.ofNat 30313661332743256476443), (Int.negOfNat 3090842777465587793348), (Int.negOfNat 123439624041781683836), (Int.ofNat 12477295570245734109), (Int.ofNat 513213072561731285), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-3167160058864645633925662087457633/5629499534213120000000000000000000), (38621244326833714478869827516009/1125899906842624000000000000000000), (-560370549923895853649680461729/450359962737049600000000000000000), (2667277972749087692673528842489/11258999068426240000000000000000000), (159073207605617174914779687353/1125899906842624000000000000000000), (-25634245397537660148108328151/1407374883553280000000000000000000), (-344717609375300245201635001/87960930222080000000000000000000), (5205214702788607594191676273/11258999068426240000000000000000000), (622678040615820394009002639/11258999068426240000000000000000000), (-34287437277779762887839373/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial163.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial163.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial163.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 5579742283799180743625265252972952), (Int.ofNat 390999651167361034717751474929178), (Int.ofNat 17430074458537917406746413456062), (Int.ofNat 3736819161920403419759259760199), (Int.negOfNat 1274326694176149146394370812998), (Int.negOfNat 181005757612719948906759636513), (Int.ofNat 43850092061443411293917073344), (Int.ofNat 3533912054509456418080548256), (Int.negOfNat 731575206744755846693469199), (Int.negOfNat 37703689291987780813558989), (Int.ofNat 7205708154567814845969105), (Int.ofNat 253503223131500082656300), (Int.negOfNat 46842569632655616515853), (Int.negOfNat 1169642647999286276560), (Int.ofNat 216368601397216257813), (Int.ofNat 3759266643373208065), (Int.negOfNat 698281738454957589), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-697467785474897592953158156621619/1407374883553280000000000000000000), (195499825583680517358875737464589/5629499534213120000000000000000000), (8715037229268958703373206728031/5629499534213120000000000000000000), (3736819161920403419759259760199/11258999068426240000000000000000000), (-637163347088074573197185406499/5629499534213120000000000000000000), (-181005757612719948906759636513/11258999068426240000000000000000000), (685157688460053301467454271/175921860444160000000000000000000), (110434751703420513065017133/351843720888320000000000000000000), (-731575206744755846693469199/11258999068426240000000000000000000), (-37703689291987780813558989/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial163.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial163.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial163.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 4721249682606529528022694847169503), (Int.ofNat 459507832604780082381674925348785), (Int.ofNat 6287655861075291485701504055720), (Int.negOfNat 6100763555101570043165284814778), (Int.negOfNat 333853734576494977789851550747), (Int.ofNat 298982471954702741631668583442), (Int.ofNat 11153308910160054405858601158), (Int.negOfNat 6563422222414070579435462010), (Int.negOfNat 155520143470240572693245188), (Int.ofNat 80343427868752781272319889), (Int.ofNat 1191700992142140340871396), (Int.negOfNat 624840111145761644157831), (Int.negOfNat 5621718834295394986002), (Int.ofNat 3355141916416340219230), (Int.ofNat 16683106293793132977), (Int.negOfNat 13260663415978639859), (Int.negOfNat 163889686429804355), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-4721249682606529528022694847169503/11258999068426240000000000000000000), (91901566520956016476334985069757/2251799813685248000000000000000000), (157191396526882287142537601393/281474976710656000000000000000000), (-3050381777550785021582642407389/5629499534213120000000000000000000), (-333853734576494977789851550747/11258999068426240000000000000000000), (149491235977351370815834291721/5629499534213120000000000000000000), (5576654455080027202929300579/5629499534213120000000000000000000), (-656342222241407057943546201/1125899906842624000000000000000000), (-38880035867560143173311297/2814749767106560000000000000000000), (80343427868752781272319889/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial163.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial163.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial163.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 3821788761702352201423193188061133), (Int.ofNat 423910554971037617393966990306104), (Int.negOfNat 16056828462294582887671440292086), (Int.ofNat 1442201699968146275173623202870), (Int.ofNat 1627293695005501632341705858479), (Int.negOfNat 34558171438961941315510084132), (Int.negOfNat 49011024522680285521453584386), (Int.ofNat 574950807536794639772995828), (Int.ofNat 766829511898909841252197927), (Int.negOfNat 7736410159673421748623706), (Int.negOfNat 7277612777402461637884992), (Int.ofNat 74088482709560159880524), (Int.ofNat 46201483210787757347822), (Int.negOfNat 485990578737449316069), (Int.negOfNat 209139453701302411427), (Int.ofNat 2418224014007640602), (Int.ofNat 618861735215607531), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-3821788761702352201423193188061133/11258999068426240000000000000000000), (52988819371379702174245873788263/1407374883553280000000000000000000), (-8028414231147291443835720146043/5629499534213120000000000000000000), (144220169996814627517362320287/1125899906842624000000000000000000), (1627293695005501632341705858479/11258999068426240000000000000000000), (-8639542859740485328877521033/2814749767106560000000000000000000), (-24505512261340142760726792193/5629499534213120000000000000000000), (143737701884198659943248957/2814749767106560000000000000000000), (766829511898909841252197927/11258999068426240000000000000000000), (-3868205079836710874311853/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial163.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial163.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial163.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 3004604397530195252648014758546892), (Int.ofNat 417877935602454288357554013334706), (Int.ofNat 18770225014659710701529912095176), (Int.ofNat 6787258552595409188638153018757), (Int.negOfNat 759515996380174584858121124626), (Int.negOfNat 298626069377246534465592789268), (Int.ofNat 18842307916357225629370026569), (Int.ofNat 6167887487324330754878736147), (Int.negOfNat 274978285296504304801823678), (Int.negOfNat 72994990753782950468704736), (Int.ofNat 2622615877473995884365224), (Int.ofNat 556576420563963374742501), (Int.negOfNat 17291744516235131286479), (Int.negOfNat 2953615200075653825581), (Int.ofNat 81774906063850100330), (Int.ofNat 11662262018672466037), (Int.negOfNat 185433699702122575), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-751151099382548813162003689636723/2814749767106560000000000000000000), (208938967801227144178777006667353/5629499534213120000000000000000000), (2346278126832463837691239011897/1407374883553280000000000000000000), (6787258552595409188638153018757/11258999068426240000000000000000000), (-379757998190087292429060562313/5629499534213120000000000000000000), (-74656517344311633616398197317/2814749767106560000000000000000000), (18842307916357225629370026569/11258999068426240000000000000000000), (6167887487324330754878736147/11258999068426240000000000000000000), (-137489142648252152400911839/5629499534213120000000000000000000), (-2281093461055717202147023/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial163.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial163.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial163.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 2059286486461601090444962440588693), (Int.ofNat 532161646322126934462722488776366), (Int.ofNat 25257444420802110322921837260280), (Int.negOfNat 5589246340856530073641990400042), (Int.negOfNat 1434921951431360545387510579108), (Int.ofNat 210232044118511408307993599818), (Int.ofNat 40801302514707913093520871701), (Int.negOfNat 3996398177631957843459851270), (Int.negOfNat 616759512542267310931254202), (Int.ofNat 46029308512207895011058871), (Int.ofNat 5746287341619139148519969), (Int.negOfNat 352279235819239789208086), (Int.negOfNat 36146709261275784946674), (Int.ofNat 1902832297444691471322), (Int.ofNat 163403298759238879224), (Int.negOfNat 7833365725704870929), (Int.negOfNat 539441731976257473), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-2059286486461601090444962440588693/11258999068426240000000000000000000), (266080823161063467231361244388183/5629499534213120000000000000000000), (631436110520052758073045931507/281474976710656000000000000000000), (-2794623170428265036820995200021/5629499534213120000000000000000000), (-358730487857840136346877644777/2814749767106560000000000000000000), (105116022059255704153996799909/5629499534213120000000000000000000), (40801302514707913093520871701/11258999068426240000000000000000000), (-399639817763195784345985127/1125899906842624000000000000000000), (-308379756271133655465627101/5629499534213120000000000000000000), (46029308512207895011058871/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial163.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial163.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial163.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 952908259048750105692354473785284), (Int.ofNat 542564165005748687846703182609335), (Int.negOfNat 19629802388168828119347209820183), (Int.negOfNat 5156920386231678542196063137661), (Int.ofNat 1549913265990613367637387253920), (Int.ofNat 213661325401847850662449576130), (Int.negOfNat 40811527667528995361285903758), (Int.negOfNat 4230487291905882889083848161), (Int.ofNat 596840127711243684924517497), (Int.ofNat 49001068869499355015234101), (Int.negOfNat 5519098400853234684382339), (Int.negOfNat 370675333068179185726882), (Int.ofNat 34898779818009660261132), (Int.ofNat 1966792105503909338770), (Int.negOfNat 159482160418380785811), (Int.negOfNat 7884063345994011248), (Int.ofNat 508283751420932819), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-238227064762187526423088618446321/2814749767106560000000000000000000), (108512833001149737569340636521867/2251799813685248000000000000000000), (-19629802388168828119347209820183/11258999068426240000000000000000000), (-5156920386231678542196063137661/11258999068426240000000000000000000), (9686957912441333547733670337/70368744177664000000000000000000), (21366132540184785066244957613/1125899906842624000000000000000000), (-20405763833764497680642951879/5629499534213120000000000000000000), (-4230487291905882889083848161/11258999068426240000000000000000000), (596840127711243684924517497/11258999068426240000000000000000000), (49001068869499355015234101/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial163.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial163.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial163.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 41099457997586332314289059292086), (Int.ofNat 459813541964543955022445297966895), (Int.negOfNat 7694230271160605249683492939271), (Int.ofNat 8126834585840201642033179791634), (Int.ofNat 834459591398477859635802043671), (Int.negOfNat 316729324122527850489812495642), (Int.negOfNat 21929303954734650229531993382), (Int.ofNat 6140945229587412350393893859), (Int.ofNat 318573936352393979089053803), (Int.negOfNat 70779273956824622790473759), (Int.negOfNat 2933323832222846140825681), (Int.ofNat 536398742987762148906058), (Int.ofNat 18541615553089907448988), (Int.negOfNat 2857911794828597447290), (Int.negOfNat 84892620288507966909), (Int.ofNat 11337126289427998032), (Int.ofNat 253612805728739481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(20549728998793166157144529646043/5629499534213120000000000000000000), (91962708392908791004489059593379/2251799813685248000000000000000000), (-7694230271160605249683492939271/11258999068426240000000000000000000), (4063417292920100821016589895817/5629499534213120000000000000000000), (834459591398477859635802043671/11258999068426240000000000000000000), (-158364662061263925244906247821/5629499534213120000000000000000000), (-10964651977367325114765996691/5629499534213120000000000000000000), (6140945229587412350393893859/11258999068426240000000000000000000), (318573936352393979089053803/11258999068426240000000000000000000), (-70779273956824622790473759/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial163.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial163.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial163.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 997606340444255380424803222455323), (Int.ofNat 526618178308577591909951723173084), (Int.ofNat 34845965542614473264931694794654), (Int.ofNat 2232766087690074823426282545296), (Int.negOfNat 1873223396735872286463339454103), (Int.negOfNat 70918056683948350348685655368), (Int.ofNat 50668568681291230809437913799), (Int.ofNat 1200430997162715173161984130), (Int.negOfNat 752779225519370603591130338), (Int.negOfNat 13128636743808348672775329), (Int.ofNat 7005115354629982793854471), (Int.ofNat 100496129892034228528914), (Int.negOfNat 44328293952470103874826), (Int.negOfNat 559463248711857580258), (Int.ofNat 201693060217864429796), (Int.ofNat 2560486626902679731), (Int.negOfNat 688219340015984067), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(997606340444255380424803222455323/11258999068426240000000000000000000), (131654544577144397977487930793271/2814749767106560000000000000000000), (17422982771307236632465847397327/5629499534213120000000000000000000), (139547880480629676464142659081/703687441776640000000000000000000), (-1873223396735872286463339454103/11258999068426240000000000000000000), (-8864757085493543793585706921/1407374883553280000000000000000000), (50668568681291230809437913799/11258999068426240000000000000000000), (120043099716271517316198413/1125899906842624000000000000000000), (-376389612759685301795565169/5629499534213120000000000000000000), (-13128636743808348672775329/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial163.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial163.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial163.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 2179051942225302481715457967988711), (Int.ofNat 636679606570219530956781986681665), (Int.ofNat 9249944434723535377978388456015), (Int.negOfNat 8123252882119372976902240639717), (Int.negOfNat 9436836445353473470153386816), (Int.ofNat 329218868259691823412030760424), (Int.negOfNat 3225074992701982831654270229), (Int.negOfNat 6575501162222357010890039933), (Int.ofNat 68787762509273130965482858), (Int.ofNat 77332072268461073495421784), (Int.negOfNat 661153215259761009828244), (Int.negOfNat 594039742499587919044799), (Int.ofNat 3690414646091190116079), (Int.ofNat 3191037378838594583619), (Int.negOfNat 13230393483397957830), (Int.negOfNat 12660148780823447943), (Int.ofNat 122183914816304135), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(2179051942225302481715457967988711/11258999068426240000000000000000000), (127335921314043906191356397336333/2251799813685248000000000000000000), (1849988886944707075595677691203/2251799813685248000000000000000000), (-8123252882119372976902240639717/11258999068426240000000000000000000), (-147450569458648022971146669/175921860444160000000000000000000), (41152358532461477926503845053/1407374883553280000000000000000000), (-3225074992701982831654270229/11258999068426240000000000000000000), (-6575501162222357010890039933/11258999068426240000000000000000000), (34393881254636565482741429/5629499534213120000000000000000000), (9666509033557634186927723/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial163.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial163.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial163.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3433816206217409225261714035762032), (Int.ofNat 598909633001094083178010026829542), (Int.negOfNat 18115289276633593891718476282945), (Int.ofNat 1276789522245050344162577707936), (Int.ofNat 1604562364855038562090999576119), (Int.negOfNat 96627235713282583074193896166), (Int.negOfNat 45736440005805597765413638430), (Int.ofNat 2308089719035678017108354268), (Int.ofNat 705939098714968166081039913), (Int.negOfNat 28182334818087381492475346), (Int.negOfNat 6769839149099507664498388), (Int.ofNat 209244236729650371800104), (Int.ofNat 43821817994978969439318), (Int.negOfNat 1044828705921661217769), (Int.negOfNat 202803730223817620493), (Int.ofNat 3668484532464320942), (Int.ofNat 608799336776634009), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(214613512888588076578857127235127/703687441776640000000000000000000), (299454816500547041589005013414771/5629499534213120000000000000000000), (-3623057855326718778343695256589/2251799813685248000000000000000000), (39899672570157823255080553373/351843720888320000000000000000000), (1604562364855038562090999576119/11258999068426240000000000000000000), (-48313617856641291537096948083/5629499534213120000000000000000000), (-4573644000580559776541363843/1125899906842624000000000000000000), (577022429758919504277088567/2814749767106560000000000000000000), (705939098714968166081039913/11258999068426240000000000000000000), (-14091167409043690746237673/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial163.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial163.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial163.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4589497815967030537600007683836175), (Int.ofNat 578265038972705920703008047802134), (Int.ofNat 11964862715793144065836366312631), (Int.ofNat 5245776428666113629758863854648), (Int.negOfNat 859780380136003064678507264995), (Int.negOfNat 236636876975731385156705980116), (Int.ofNat 29271435400985378595747093152), (Int.ofNat 5067443469090842768527200630), (Int.negOfNat 473431458590753065339236932), (Int.negOfNat 63236451018711113596147271), (Int.ofNat 4440136137258320807112184), (Int.ofNat 509515435070799189186029), (Int.negOfNat 27069812541984549165758), (Int.negOfNat 2834043645245902004330), (Int.ofNat 115931697691492503583), (Int.ofNat 11505323399165486421), (Int.negOfNat 471507300948231065), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(183579912638681221504000307353447/450359962737049600000000000000000), (289132519486352960351504023901067/5629499534213120000000000000000000), (11964862715793144065836366312631/11258999068426240000000000000000000), (655722053583264203719857981831/1407374883553280000000000000000000), (-171956076027200612935701452999/2251799813685248000000000000000000), (-59159219243932846289176495029/2814749767106560000000000000000000), (914732356280793081117096661/351843720888320000000000000000000), (506744346909084276852720063/1125899906842624000000000000000000), (-118357864647688266334809233/2814749767106560000000000000000000), (-63236451018711113596147271/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial163.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial163.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial163.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 5816898577508982769640023897790278), (Int.ofNat 649917396703151337994655121377130), (Int.ofNat 13227794051108131228462961915910), (Int.negOfNat 4679143058059076150427938290640), (Int.negOfNat 759314442812344643650415865735), (Int.ofNat 248046171576643652592375368464), (Int.ofNat 25039293848353495498080869576), (Int.negOfNat 5591036385514143126040101444), (Int.negOfNat 440899800776997926568701561), (Int.ofNat 67961979913591315367872671), (Int.ofNat 4713462276522489059401135), (Int.negOfNat 510850511518754862854360), (Int.negOfNat 33007082555954755691307), (Int.ofNat 2603681995500015785960), (Int.ofNat 161214009800584187447), (Int.negOfNat 9600871260990272515), (Int.negOfNat 529379333537283951), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(2908449288754491384820011948895139/5629499534213120000000000000000000), (64991739670315133799465512137713/1125899906842624000000000000000000), (1322779405110813122846296191591/1125899906842624000000000000000000), (-58489288225738451880349228633/140737488355328000000000000000000), (-151862888562468928730083173147/2251799813685248000000000000000000), (15502885723540228287023460529/703687441776640000000000000000000), (3129911731044186937260108697/1407374883553280000000000000000000), (-1397759096378535781510025361/2814749767106560000000000000000000), (-440899800776997926568701561/11258999068426240000000000000000000), (67961979913591315367872671/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial163.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial163.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial163.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 7128812306180006327553836543713697), (Int.ofNat 644250072896946966337314979315192), (Int.negOfNat 11413437292105197470700533229837), (Int.negOfNat 333269031854875610795816887460), (Int.ofNat 1476905251445715484713718353220), (Int.ofNat 38906254623213397909527669454), (Int.negOfNat 49945527207266113073262787532), (Int.negOfNat 1529723786946199722179311267), (Int.ofNat 823844994818380794569809061), (Int.ofNat 28125252761608217670036714), (Int.negOfNat 7842514365939484580000834), (Int.negOfNat 286299389186053708893455), (Int.ofNat 48211062890045677454257), (Int.ofNat 1818996965542421342512), (Int.negOfNat 208085508104286648244), (Int.negOfNat 8074622112120912071), (Int.ofNat 820830687080157995), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(7128812306180006327553836543713697/11258999068426240000000000000000000), (80531259112118370792164372414399/1407374883553280000000000000000000), (-11413437292105197470700533229837/11258999068426240000000000000000000), (-16663451592743780539790844373/562949953421312000000000000000000), (73845262572285774235685917661/562949953421312000000000000000000), (19453127311606698954763834727/5629499534213120000000000000000000), (-12486381801816528268315696883/2814749767106560000000000000000000), (-1529723786946199722179311267/11258999068426240000000000000000000), (823844994818380794569809061/11258999068426240000000000000000000), (14062626380804108835018357/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial163.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial163.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial163.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 8390692612447007903156859920160409), (Int.ofNat 635562001773972310698583443519610), (Int.ofNat 13641263161356857786172014259696), (Int.ofNat 5691067086231083136594425598990), (Int.negOfNat 633930978481193671173156460103), (Int.negOfNat 329605869073154096279514271061), (Int.ofNat 12301693434640311209195192486), (Int.ofNat 7982710200852314232050663931), (Int.negOfNat 46854342549975857719173960), (Int.negOfNat 100843799768929545558357220), (Int.negOfNat 964485251081205755157896), (Int.ofNat 764545297962063001432332), (Int.ofNat 13090555941530196414944), (Int.negOfNat 3902671948927387298157), (Int.negOfNat 82233482457312771756), (Int.ofNat 14665562164719141908), (Int.ofNat 333518201587291583), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(8390692612447007903156859920160409/11258999068426240000000000000000000), (63556200177397231069858344351961/1125899906842624000000000000000000), (852578947584803611635750891231/703687441776640000000000000000000), (569106708623108313659442559899/1125899906842624000000000000000000), (-633930978481193671173156460103/11258999068426240000000000000000000), (-329605869073154096279514271061/11258999068426240000000000000000000), (6150846717320155604597596243/5629499534213120000000000000000000), (7982710200852314232050663931/11258999068426240000000000000000000), (-1171358563749396442979349/281474976710656000000000000000000), (-5042189988446477277917861/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial163.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial163.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial163.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 9742965989357802805115380935782427), (Int.ofNat 717427236789018099766187664483779), (Int.ofNat 13983651412034396404097757383565), (Int.negOfNat 6734347850661940600542841090757), (Int.negOfNat 1396288470974228419466512879511), (Int.ofNat 279102260845126304563535011359), (Int.ofNat 58999870149819074480629981014), (Int.negOfNat 4285492240379007056784881033), (Int.negOfNat 1086770916834055826877018488), (Int.ofNat 26064132531890822984517486), (Int.ofNat 10523195143645819330694840), (Int.negOfNat 49407870968494267861052), (Int.negOfNat 64482214881052060629300), (Int.negOfNat 288467432615769234975), (Int.ofNat 276759429005672726604), (Int.ofNat 2679614096930318888), (Int.negOfNat 1000766275675209243), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(9742965989357802805115380935782427/11258999068426240000000000000000000), (717427236789018099766187664483779/11258999068426240000000000000000000), (2796730282406879280819551476713/2251799813685248000000000000000000), (-6734347850661940600542841090757/11258999068426240000000000000000000), (-1396288470974228419466512879511/11258999068426240000000000000000000), (279102260845126304563535011359/11258999068426240000000000000000000), (29499935074909537240314990507/5629499534213120000000000000000000), (-4285492240379007056784881033/11258999068426240000000000000000000), (-135846364604256978359627311/1407374883553280000000000000000000), (13032066265945411492258743/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial163.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial163.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial163.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 11169443935395276179528540107164632), (Int.ofNat 678603644979757832484881443940341), (Int.negOfNat 28036914519021243598872893747029), (Int.negOfNat 1355425576929309556159650113077), (Int.ofNat 2754048201299152990885300996752), (Int.ofNat 269841433236772199882965780747), (Int.negOfNat 74237010298599975845991641714), (Int.negOfNat 9624340202391680949845106711), (Int.ofNat 741214762298553927503467313), (Int.ofNat 126147278429896518851886640), (Int.negOfNat 4015456049340710639208038), (Int.negOfNat 946878406807626270549445), (Int.ofNat 12965873480994626855773), (Int.ofNat 4776636612101678653700), (Int.negOfNat 21921056206341881464), (Int.negOfNat 17909386173310436605), (Int.negOfNat 47689275339773591), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(1396180491924409522441067513395579/1407374883553280000000000000000000), (678603644979757832484881443940341/11258999068426240000000000000000000), (-28036914519021243598872893747029/11258999068426240000000000000000000), (-1355425576929309556159650113077/11258999068426240000000000000000000), (172128012581197061930331312297/703687441776640000000000000000000), (269841433236772199882965780747/11258999068426240000000000000000000), (-37118505149299987922995820857/5629499534213120000000000000000000), (-9624340202391680949845106711/11258999068426240000000000000000000), (741214762298553927503467313/11258999068426240000000000000000000), (1576840980373706485648583/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial163.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial163.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial163.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 12450625154190657644769455564183842), (Int.ofNat 642361515292469829875429124383009), (Int.ofNat 29068801760666961839133423715364), (Int.ofNat 16110626574129713824833705148121), (Int.negOfNat 448430532800020204305709209176), (Int.negOfNat 900635827136276879525385660662), (Int.negOfNat 66926538849505475741530405262), (Int.ofNat 12361263923066622795072826746), (Int.ofNat 1320414723478615125957773327), (Int.negOfNat 91781874681503463803225357), (Int.negOfNat 12425046595276068820445901), (Int.ofNat 442717581969008297111340), (Int.ofNat 74208297214711221064277), (Int.negOfNat 1508560399593451709168), (Int.negOfNat 314441979063876681313), (Int.ofNat 3689114112178115039), (Int.ofNat 1037787401146501495), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(6225312577095328822384727782091921/5629499534213120000000000000000000), (642361515292469829875429124383009/11258999068426240000000000000000000), (7267200440166740459783355928841/2814749767106560000000000000000000), (16110626574129713824833705148121/11258999068426240000000000000000000), (-56053816600002525538213651147/1407374883553280000000000000000000), (-450317913568138439762692830331/5629499534213120000000000000000000), (-33463269424752737870765202631/5629499534213120000000000000000000), (6180631961533311397536413373/5629499534213120000000000000000000), (1320414723478615125957773327/11258999068426240000000000000000000), (-91781874681503463803225357/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial163.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial163.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial163.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 13942091616644625672451016540847791), (Int.ofNat 859335267406390119517779054137243), (Int.ofNat 36981007447733291170837510722721), (Int.negOfNat 25579879185770929208368037763553), (Int.negOfNat 9040172079393506122694184702644), (Int.negOfNat 339275531425931809604929314744), (Int.ofNat 160970380116562424073773056358), (Int.ofNat 12269748044591961575985435568), (Int.negOfNat 1512302917029279391519815004), (Int.negOfNat 147076528962605364223597663), (Int.ofNat 9257945139819857976369608), (Int.ofNat 1046137662499343950353751), (Int.negOfNat 40528570340565784573294), (Int.negOfNat 5116709744429005416022), (Int.ofNat 134247050450202154643), (Int.ofNat 18692754019043342355), (Int.negOfNat 301634110792153339), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(13942091616644625672451016540847791/11258999068426240000000000000000000), (859335267406390119517779054137243/11258999068426240000000000000000000), (36981007447733291170837510722721/11258999068426240000000000000000000), (-25579879185770929208368037763553/11258999068426240000000000000000000), (-2260043019848376530673546175661/2814749767106560000000000000000000), (-42409441428241476200616164343/1407374883553280000000000000000000), (80485190058281212036886528179/5629499534213120000000000000000000), (766859252786997598499089723/703687441776640000000000000000000), (-378075729257319847879953751/2814749767106560000000000000000000), (-147076528962605364223597663/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial163.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial163.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial163.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 15459969174316205851572913143019976), (Int.ofNat 418446831108233014278259816080027), (Int.negOfNat 316981434279895162071959625370383), (Int.negOfNat 82166227954247610532089058713877), (Int.negOfNat 1464174502905495978169864379264), (Int.ofNat 1748993796033838349083462768630), (Int.ofNat 107732197938585133236256906584), (Int.negOfNat 20197559399120359134569757470), (Int.negOfNat 1604779294171031677677103335), (Int.ofNat 152084425019096788621847132), (Int.ofNat 13498728689949421955762788), (Int.negOfNat 812932893216761308748204), (Int.negOfNat 76247792921255144414526), (Int.ofNat 3255896309040504672077), (Int.ofNat 313072838292818910207), (Int.negOfNat 9866604769558963706), (Int.negOfNat 958367397907151437), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(1932496146789525731446614142877497/1407374883553280000000000000000000), (418446831108233014278259816080027/11258999068426240000000000000000000), (-316981434279895162071959625370383/11258999068426240000000000000000000), (-82166227954247610532089058713877/11258999068426240000000000000000000), (-11438863303949187329452065463/87960930222080000000000000000000), (174899379603383834908346276863/1125899906842624000000000000000000), (13466524742323141654532113323/1407374883553280000000000000000000), (-2019755939912035913456975747/1125899906842624000000000000000000), (-320955858834206335535420667/2251799813685248000000000000000000), (38021106254774197155461783/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial163.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial163.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial163.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 14408136778906840246617591682817529), (Int.negOfNat 1732006248914099911329426555023137), (Int.negOfNat 694963391975121700778409736430503), (Int.negOfNat 19885934927905821782528732646341), (Int.ofNat 15789130458205528690984050257770), (Int.ofNat 1011287863090536106256195004247), (Int.negOfNat 222817322335614852831143622051), (Int.negOfNat 16766548484082453137138778345), (Int.ofNat 2068625746217139779860813150), (Int.ofNat 161842038424319685826893590), (Int.negOfNat 13443318660622506553197628), (Int.negOfNat 1045627724559145728765661), (Int.ofNat 64285282695539674637255), (Int.ofNat 4863305573413688105053), (Int.negOfNat 234776206331039827230), (Int.negOfNat 17094352621737168533), (Int.ofNat 650957496924080269), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(14408136778906840246617591682817529/11258999068426240000000000000000000), (-1732006248914099911329426555023137/11258999068426240000000000000000000), (-694963391975121700778409736430503/11258999068426240000000000000000000), (-19885934927905821782528732646341/11258999068426240000000000000000000), (1578913045820552869098405025777/1125899906842624000000000000000000), (1011287863090536106256195004247/11258999068426240000000000000000000), (-222817322335614852831143622051/11258999068426240000000000000000000), (-3353309696816490627427755669/2251799813685248000000000000000000), (41372514924342795597216263/225179981368524800000000000000000), (16184203842431968582689359/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial163.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial163.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial163.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 8274360928581252135835668195211172), (Int.negOfNat 4212215814629334927435195837696647), (Int.negOfNat 414906664972272432956030195614511), (Int.ofNat 106173430181005977824686870352591), (Int.ofNat 10592542716927484249831455079164), (Int.negOfNat 1949382972888305331821447776399), (Int.negOfNat 173081073876639321249127789459), (Int.ofNat 23247039575822305378955639232), (Int.ofNat 1834701815264647635981923050), (Int.negOfNat 187570727666377349857870577), (Int.negOfNat 13311365755923681483472845), (Int.ofNat 1080866734010508184315806), (Int.ofNat 69586081258460288805658), (Int.negOfNat 4646625797689329819370), (Int.negOfNat 273663932526959427524), (Int.ofNat 15281746481256194033), (Int.ofNat 878947394667801379), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(2068590232145313033958917048802793/2814749767106560000000000000000000), (-4212215814629334927435195837696647/11258999068426240000000000000000000), (-414906664972272432956030195614511/11258999068426240000000000000000000), (106173430181005977824686870352591/11258999068426240000000000000000000), (2648135679231871062457863769791/2814749767106560000000000000000000), (-1949382972888305331821447776399/11258999068426240000000000000000000), (-173081073876639321249127789459/11258999068426240000000000000000000), (363234993372223521546181863/175921860444160000000000000000000), (36694036305292952719638461/225179981368524800000000000000000), (-187570727666377349857870577/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial163.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial163.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial163.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 860948585170995261179347951225560), (Int.negOfNat 4436175447707080898009665776990509), (Int.ofNat 296791279910832649101351067658944), (Int.ofNat 100390727767242486862629555958986), (Int.negOfNat 11604763143223811311154595546001), (Int.negOfNat 1699887419213950779456517307153), (Int.ofNat 205999444506807364112634906166), (Int.ofNat 19682753507186277454164412599), (Int.negOfNat 2188767843802682263248982889), (Int.negOfNat 158332243017316303216518435), (Int.ofNat 15620735002605564175081263), (Int.ofNat 920358302317832970415362), (Int.negOfNat 80068862674055174964668), (Int.negOfNat 4007715127361027782122), (Int.ofNat 309218748838567216791), (Int.ofNat 13316153949058713744), (Int.negOfNat 973807548642890513), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-21523714629274881529483698780639/281474976710656000000000000000000), (-4436175447707080898009665776990509/11258999068426240000000000000000000), (4637363748606760142208610432171/175921860444160000000000000000000), (50195363883621243431314777979493/5629499534213120000000000000000000), (-11604763143223811311154595546001/11258999068426240000000000000000000), (-1699887419213950779456517307153/11258999068426240000000000000000000), (102999722253403682056317453083/5629499534213120000000000000000000), (19682753507186277454164412599/11258999068426240000000000000000000), (-2188767843802682263248982889/11258999068426240000000000000000000), (-31666448603463260643303687/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial163.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial163.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial163.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial163.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial163.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial163.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial163.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial163.reflect := by
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

end Bin163
end
end ErdosOverlap.OuterNumerics
