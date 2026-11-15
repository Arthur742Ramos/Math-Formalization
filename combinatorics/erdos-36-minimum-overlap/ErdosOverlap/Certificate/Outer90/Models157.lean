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

/-! # Exact integer weighted outer models for source bin 157

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin157

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 1562219132517276000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 1147692468253481700)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 534346143483916750)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 905149366736250500)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 714590655941485100)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 513452252119612700)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 384508376632943500)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 237852978966794430)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 121196988144135660)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial157.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial157.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9236256060788323000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 3606798354131624000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1315170617208853700)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 1121447172242794300)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 669555509801951500)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 305992138576478700)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 109025959792398830)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 31360273737889607)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 29677198573250300)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial157.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial157.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9236256060788323000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 3606798354131624000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1315170617208853700)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 1121447172242794300)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 669555509801951500)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 305992138576478700)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 109025959792398830)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 31360273737889607)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 29677198573250300)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial157.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial157.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial157.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 2894633654516051453525055792718889), (Int.ofNat 4431051929179610653247081804016369), (Int.ofNat 322168865439155284459783859246442), (Int.negOfNat 123663232988075558315564492725121), (Int.negOfNat 9627504488404420448657704689734), (Int.ofNat 2346607045699789690152344118079), (Int.ofNat 158058390493547933610640056319), (Int.negOfNat 28624966086762146062474497871), (Int.negOfNat 1607743175220348661705696034), (Int.ofNat 236656003162128004997468613), (Int.ofNat 11054736512591765924127008), (Int.negOfNat 1396262159146876788358820), (Int.negOfNat 54777776319643371238762), (Int.ofNat 6128941746327864885524), (Int.ofNat 205516829152194922820), (Int.negOfNat 20421529361842013392), (Int.negOfNat 634414454510081323), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-2894633654516051453525055792718889/11258999068426240000000000000000000), (4431051929179610653247081804016369/11258999068426240000000000000000000), (161084432719577642229891929623221/5629499534213120000000000000000000), (-123663232988075558315564492725121/11258999068426240000000000000000000), (-4813752244202210224328852344867/5629499534213120000000000000000000), (2346607045699789690152344118079/11258999068426240000000000000000000), (158058390493547933610640056319/11258999068426240000000000000000000), (-28624966086762146062474497871/11258999068426240000000000000000000), (-803871587610174330852848017/5629499534213120000000000000000000), (236656003162128004997468613/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial157.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial157.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial157.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial157 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 6194060771286316706500721920521409), (Int.ofNat 4131879038748448582722546899859340), (Int.negOfNat 446149238497714245684530539545718), (Int.negOfNat 99061879140596197662947293675680), (Int.ofNat 14545652263131428625931476776473), (Int.ofNat 1640109613060813029451338874481), (Int.negOfNat 249015975876961211503181449311), (Int.negOfNat 17691689229909872343635108039), (Int.ofNat 2638525200544553869799645036), (Int.ofNat 130267873899403129512570637), (Int.negOfNat 18968176376535234564606342), (Int.negOfNat 690795400140338693023320), (Int.ofNat 98153976470182170989078), (Int.ofNat 2755635385041662534096), (Int.negOfNat 382348533899865586150), (Int.negOfNat 8452206076632669718), (Int.ofNat 1236300964006634857), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(6194060771286316706500721920521409/11258999068426240000000000000000000), (206593951937422429136127344992967/562949953421312000000000000000000), (-223074619248857122842265269772859/5629499534213120000000000000000000), (-619136744628726235393420585473/70368744177664000000000000000000), (14545652263131428625931476776473/11258999068426240000000000000000000), (1640109613060813029451338874481/11258999068426240000000000000000000), (-249015975876961211503181449311/11258999068426240000000000000000000), (-17691689229909872343635108039/11258999068426240000000000000000000), (659631300136138467449911259/2814749767106560000000000000000000), (130267873899403129512570637/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial157.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial157.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial157.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial157 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 12148460986414964899558645669026907), (Int.ofNat 1702371834901532338417555167211282), (Int.negOfNat 626771267486540238623573197663159), (Int.ofNat 38277416296480488548048175974072), (Int.ofNat 14261434225445412868908502562224), (Int.negOfNat 1552438017969562769186323182639), (Int.negOfNat 181486463517518575243709243899), (Int.ofNat 24041903336945117220880356841), (Int.ofNat 1471618766355862816404295614), (Int.negOfNat 222241005375251664767898443), (Int.negOfNat 8272349987442134346963428), (Int.ofNat 1392517517741354234077300), (Int.ofNat 34093299241927951825922), (Int.negOfNat 6330764301411849283794), (Int.negOfNat 107053790457373742110), (Int.ofNat 21810820514235346422), (Int.ofNat 241146291504424043), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(12148460986414964899558645669026907/11258999068426240000000000000000000), (851185917450766169208777583605641/5629499534213120000000000000000000), (-626771267486540238623573197663159/11258999068426240000000000000000000), (4784677037060061068506021996759/1407374883553280000000000000000000), (891339639090338304306781410139/703687441776640000000000000000000), (-1552438017969562769186323182639/11258999068426240000000000000000000), (-181486463517518575243709243899/11258999068426240000000000000000000), (24041903336945117220880356841/11258999068426240000000000000000000), (735809383177931408202147807/5629499534213120000000000000000000), (-222241005375251664767898443/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial157.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial157.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial157.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial157 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 13522563492379470914483046415795406), (Int.negOfNat 36319294931050236865769720512869), (Int.negOfNat 204869740096429538615685273532625), (Int.ofNat 76073078103502494564685065179631), (Int.negOfNat 4718669726558668809770306583203), (Int.negOfNat 1523714471303369313995054480301), (Int.ofNat 163966961802798026152666564591), (Int.ofNat 15154046517940482167887343529), (Int.negOfNat 2172854663332952992724878456), (Int.negOfNat 93618999256333372579929237), (Int.ofNat 17247413376659850926224542), (Int.ofNat 390759223526146720458300), (Int.negOfNat 93808789485298533352928), (Int.negOfNat 1143647295696323405986), (Int.ofNat 374833201130473079300), (Int.ofNat 2056224650619531048), (Int.negOfNat 1147269368286883957), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(6761281746189735457241523207897703/5629499534213120000000000000000000), (-36319294931050236865769720512869/11258999068426240000000000000000000), (-1638957920771436308925482188261/90071992547409920000000000000000), (76073078103502494564685065179631/11258999068426240000000000000000000), (-4718669726558668809770306583203/11258999068426240000000000000000000), (-1523714471303369313995054480301/11258999068426240000000000000000000), (163966961802798026152666564591/11258999068426240000000000000000000), (15154046517940482167887343529/11258999068426240000000000000000000), (-271606832916619124090609807/1407374883553280000000000000000000), (-93618999256333372579929237/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial157.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial157.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial157.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial157 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 13126620482207618315975954874020168), (Int.negOfNat 179895553935119252879497863610883), (Int.ofNat 61837246510729565081877224208186), (Int.ofNat 7969873282809780305839138956697), (Int.negOfNat 8449345352199866071580628185461), (Int.ofNat 695786071240428103758845657869), (Int.ofNat 128066592909292990186489714219), (Int.negOfNat 16813133700743659477415933931), (Int.negOfNat 957428616643425020131491514), (Int.ofNat 182245968429604459272778103), (Int.ofNat 4124985526346276123856178), (Int.negOfNat 1226924308850849516007000), (Int.negOfNat 9525544269166269596462), (Int.ofNat 5779921035545038629224), (Int.ofNat 828570559519185200), (Int.negOfNat 20489082752514065622), (Int.ofNat 122444672927982937), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(1640827560275952289496994359252521/1407374883553280000000000000000000), (-179895553935119252879497863610883/11258999068426240000000000000000000), (30918623255364782540938612104093/5629499534213120000000000000000000), (7969873282809780305839138956697/11258999068426240000000000000000000), (-8449345352199866071580628185461/11258999068426240000000000000000000), (695786071240428103758845657869/11258999068426240000000000000000000), (128066592909292990186489714219/11258999068426240000000000000000000), (-16813133700743659477415933931/11258999068426240000000000000000000), (-478714308321712510065745757/5629499534213120000000000000000000), (182245968429604459272778103/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial157.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial157.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial157.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial157 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 12970907083264696639255036547718032), (Int.negOfNat 35120895609931219167398269244432), (Int.negOfNat 18890050383742048642978148742082), (Int.negOfNat 21441986533561319951927169136295), (Int.ofNat 1151798147420024546803193136900), (Int.ofNat 756626999591256307421541943971), (Int.negOfNat 95702138345005101835623661511), (Int.negOfNat 8045009701122935192910836349), (Int.ofNat 1592880869419687663396592836), (Int.ofNat 38162122347084453019383367), (Int.negOfNat 13927997675708342554669922), (Int.negOfNat 42055028708627756228460), (Int.ofNat 79309766588592123474488), (Int.negOfNat 535375215894725734564), (Int.negOfNat 324496430893366629420), (Int.ofNat 3988606780216872942), (Int.ofNat 1058237772567133057), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(810681692704043539953439784232377/703687441776640000000000000000000), (-2195055975620701197962391827777/703687441776640000000000000000000), (-9445025191871024321489074371041/5629499534213120000000000000000000), (-4288397306712263990385433827259/2251799813685248000000000000000000), (11517981474200245468031931369/112589990684262400000000000000000), (756626999591256307421541943971/11258999068426240000000000000000000), (-95702138345005101835623661511/11258999068426240000000000000000000), (-8045009701122935192910836349/11258999068426240000000000000000000), (398220217354921915849148209/2814749767106560000000000000000000), (38162122347084453019383367/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial157.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial157.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial157.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial157 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 12689468617950111236654849651617410), (Int.negOfNat 290927074392246403449550998153016), (Int.negOfNat 84869596082157909033434517535846), (Int.ofNat 1072369296421922971866775360927), (Int.ofNat 2481804429303708378342528920531), (Int.negOfNat 383041114541547045838553894659), (Int.negOfNat 47363657480056422426070039899), (Int.ofNat 11164116116979458429444486821), (Int.ofNat 267227694657043992906651874), (Int.negOfNat 134399152392020115214779773), (Int.ofNat 491441215623993053887502), (Int.ofNat 954418488284372569790490), (Int.negOfNat 14763274556022206729828), (Int.negOfNat 4615841539685733979524), (Int.ofNat 98869646090317837270), (Int.ofNat 16802759625056572222), (Int.negOfNat 486035637360389917), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(1268946861795011123665484965161741/1125899906842624000000000000000000), (-36365884299030800431193874769127/1407374883553280000000000000000000), (-42434798041078954516717258767923/5629499534213120000000000000000000), (1072369296421922971866775360927/11258999068426240000000000000000000), (2481804429303708378342528920531/11258999068426240000000000000000000), (-383041114541547045838553894659/11258999068426240000000000000000000), (-47363657480056422426070039899/11258999068426240000000000000000000), (11164116116979458429444486821/11258999068426240000000000000000000), (133613847328521996453325937/5629499534213120000000000000000000), (-134399152392020115214779773/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial157.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial157.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial157.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial157 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 11802566286847816908935897281943963), (Int.negOfNat 572878214031148207157049862283137), (Int.negOfNat 53489941476438617463028873537398), (Int.ofNat 4080172581450004740253811931096), (Int.negOfNat 1263573569775766324398539173240), (Int.negOfNat 135537002859359679622957349848), (Int.ofNat 62535389477983821388733675251), (Int.ofNat 783576118089622349869521229), (Int.negOfNat 1080010448819867621553014716), (Int.ofNat 17363786560021319745767913), (Int.ofNat 9887291693417336911676482), (Int.negOfNat 279621299186293868185830), (Int.negOfNat 57801772266983229741608), (Int.ofNat 1985963698193510992634), (Int.ofNat 238044008763828070430), (Int.negOfNat 9097220687356400472), (Int.negOfNat 848009188703246497), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(11802566286847816908935897281943963/11258999068426240000000000000000000), (-572878214031148207157049862283137/11258999068426240000000000000000000), (-26744970738219308731514436768699/5629499534213120000000000000000000), (510021572681250592531726491387/1407374883553280000000000000000000), (-31589339244394158109963479331/281474976710656000000000000000000), (-16942125357419959952869668731/1407374883553280000000000000000000), (62535389477983821388733675251/11258999068426240000000000000000000), (783576118089622349869521229/11258999068426240000000000000000000), (-270002612204966905388253679/2814749767106560000000000000000000), (17363786560021319745767913/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial157.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial157.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial157.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial157 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 10454781417589168325763331248507155), (Int.negOfNat 777815127735820033690592160292695), (Int.negOfNat 56395423386389571766126939145757), (Int.negOfNat 2713175353542332150954247144828), (Int.ofNat 327671518328540155386879293672), (Int.ofNat 298338218173746693173389872929), (Int.negOfNat 9526346048696050386976051131), (Int.negOfNat 7141106263918948028237223951), (Int.ofNat 303667667225454657946564156), (Int.ofNat 86145894195080638153873813), (Int.negOfNat 4307327242661152602990442), (Int.negOfNat 622432747084446747753850), (Int.ofNat 33878540738893296737848), (Int.ofNat 3032272136412047801854), (Int.negOfNat 173709071603417395110), (Int.negOfNat 10971762550227355152), (Int.ofNat 669075216502160637), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(2090956283517833665152666249701431/2251799813685248000000000000000000), (-155563025547164006738118432058539/2251799813685248000000000000000000), (-56395423386389571766126939145757/11258999068426240000000000000000000), (-678293838385583037738561786207/2814749767106560000000000000000000), (40958939791067519423359911709/1407374883553280000000000000000000), (298338218173746693173389872929/11258999068426240000000000000000000), (-9526346048696050386976051131/11258999068426240000000000000000000), (-7141106263918948028237223951/11258999068426240000000000000000000), (75916916806363664486641039/2814749767106560000000000000000000), (86145894195080638153873813/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial157.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial157.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial157.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial157 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 8665246205910177181389473888238415), (Int.negOfNat 1006149310358837419671783830786307), (Int.negOfNat 47151761797398338359814053240669), (Int.ofNat 7237889595145773273237499034803), (Int.ofNat 1348430069015584641543029430627), (Int.negOfNat 155026686228154122049513990442), (Int.negOfNat 38761047138409305910677053581), (Int.ofNat 3803139756569262078402987581), (Int.ofNat 610792107423460599235712766), (Int.negOfNat 56098100210890219130708173), (Int.negOfNat 5551026304265565161285782), (Int.ofNat 501013439950347835518310), (Int.ofNat 32357862633307342819168), (Int.negOfNat 2938988080298321054844), (Int.negOfNat 131781944012059750390), (Int.ofNat 12276635559594295282), (Int.ofNat 546260815268474577), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(1733049241182035436277894777647683/2251799813685248000000000000000000), (-1006149310358837419671783830786307/11258999068426240000000000000000000), (-47151761797398338359814053240669/11258999068426240000000000000000000), (7237889595145773273237499034803/11258999068426240000000000000000000), (1348430069015584641543029430627/11258999068426240000000000000000000), (-77513343114077061024756995221/5629499534213120000000000000000000), (-38761047138409305910677053581/11258999068426240000000000000000000), (3803139756569262078402987581/11258999068426240000000000000000000), (305396053711730299617856383/5629499534213120000000000000000000), (-56098100210890219130708173/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial157.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial157.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial157.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial157 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 6536986865878983167415198751868153), (Int.negOfNat 1082418319517333988211676609964244), (Int.ofNat 10276700558626908318258466121657), (Int.ofNat 8483818314847713674219998419669), (Int.negOfNat 1055238410544605964501981060475), (Int.negOfNat 167887226765574020475353490769), (Int.ofNat 35149188542103922656097887891), (Int.ofNat 3274966305348675503333239771), (Int.negOfNat 616111182905959684560135096), (Int.negOfNat 37789023166471523685553973), (Int.ofNat 6450336192928982121456102), (Int.ofNat 266335105085218718546480), (Int.negOfNat 44065647260544336234508), (Int.negOfNat 1249596724823069150084), (Int.ofNat 210421410502985935920), (Int.ofNat 4161236794840514962), (Int.negOfNat 701240608926545397), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(6536986865878983167415198751868153/11258999068426240000000000000000000), (-270604579879333497052919152491061/2814749767106560000000000000000000), (10276700558626908318258466121657/11258999068426240000000000000000000), (8483818314847713674219998419669/11258999068426240000000000000000000), (-42209536421784238580079242419/450359962737049600000000000000000), (-167887226765574020475353490769/11258999068426240000000000000000000), (35149188542103922656097887891/11258999068426240000000000000000000), (3274966305348675503333239771/11258999068426240000000000000000000), (-77013897863244960570016887/1407374883553280000000000000000000), (-37789023166471523685553973/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial157.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial157.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial157.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial157 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 4461370004482134256774624562310100), (Int.negOfNat 979171538490119328028477857654792), (Int.ofNat 31860000534252524772257302830409), (Int.negOfNat 417793206503453026217393414972), (Int.negOfNat 458456228636309777762928338534), (Int.ofNat 232032752403781799642379964062), (Int.ofNat 9496359378291761402580306841), (Int.negOfNat 5585128049162556467494372091), (Int.negOfNat 142805764929854191727433486), (Int.ofNat 71664258932226641821698323), (Int.ofNat 1202783593571417963445542), (Int.negOfNat 581104768983044805813880), (Int.negOfNat 6030314896147260797338), (Int.ofNat 3225425533725526745184), (Int.ofNat 18760178556698386420), (Int.negOfNat 12995238829726758682), (Int.negOfNat 182669850836067597), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(44613700044821342567746245623101/112589990684262400000000000000000), (-122396442311264916003559732206849/1407374883553280000000000000000000), (31860000534252524772257302830409/11258999068426240000000000000000000), (-104448301625863256554348353743/2814749767106560000000000000000000), (-229228114318154888881464169267/5629499534213120000000000000000000), (116016376201890899821189982031/5629499534213120000000000000000000), (9496359378291761402580306841/11258999068426240000000000000000000), (-5585128049162556467494372091/11258999068426240000000000000000000), (-71402882464927095863716743/5629499534213120000000000000000000), (71664258932226641821698323/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial157.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial157.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial157.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial157 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 2627107380007262997526344970874282), (Int.negOfNat 853513353681649130238755200674647), (Int.ofNat 35510749143750303082778941548570), (Int.ofNat 3711156615484064021376816476350), (Int.ofNat 988844809849352121922909398825), (Int.negOfNat 49714713390378970746036799491), (Int.negOfNat 40747078897675272483089122311), (Int.ofNat 724996935700594136888623349), (Int.ofNat 674986711926906322524963936), (Int.negOfNat 8595501602724632763429357), (Int.negOfNat 6661765951772233153615122), (Int.ofNat 76789904940165768332500), (Int.ofNat 43711334248613729535528), (Int.negOfNat 496183448541039827366), (Int.negOfNat 203567108615019856680), (Int.ofNat 2398418541313189688), (Int.ofNat 612209013206794497), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(1313553690003631498763172485437141/5629499534213120000000000000000000), (-853513353681649130238755200674647/11258999068426240000000000000000000), (3551074914375030308277894154857/1125899906842624000000000000000000), (74223132309681280427536329527/225179981368524800000000000000000), (39553792393974084876916375953/450359962737049600000000000000000), (-49714713390378970746036799491/11258999068426240000000000000000000), (-40747078897675272483089122311/11258999068426240000000000000000000), (724996935700594136888623349/11258999068426240000000000000000000), (21093334747715822578905123/351843720888320000000000000000000), (-8595501602724632763429357/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial157.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial157.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial157.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial157 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 1103690457895927726365334517572288), (Int.negOfNat 646130097002745612446415745787919), (Int.ofNat 69338875313830374711585890314544), (Int.ofNat 4588711463040218159394806569778), (Int.negOfNat 1109930554528531856982056320376), (Int.negOfNat 240092474557782705129353289992), (Int.ofNat 20307541259052511977253847559), (Int.ofNat 5268667862918079406458520261), (Int.negOfNat 286828539241493090294266834), (Int.negOfNat 65047528046028135937122123), (Int.ofNat 2715843974963781538992068), (Int.ofNat 514167598409917213143960), (Int.negOfNat 17868026207328318921142), (Int.negOfNat 2809697707783865173134), (Int.ofNat 85420103620847156510), (Int.ofNat 11230547939830008282), (Int.negOfNat 180921113596339383), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(17245163404623870724458351837067/175921860444160000000000000000000), (-646130097002745612446415745787919/11258999068426240000000000000000000), (4333679707114398419474118144659/703687441776640000000000000000000), (2294355731520109079697403284889/5629499534213120000000000000000000), (-138741319316066482122757040047/1407374883553280000000000000000000), (-30011559319722838141169161249/1407374883553280000000000000000000), (20307541259052511977253847559/11258999068426240000000000000000000), (5268667862918079406458520261/11258999068426240000000000000000000), (-143414269620746545147133417/5629499534213120000000000000000000), (-65047528046028135937122123/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial157.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial157.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial157.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial157 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 101924688047109634398450772098846), (Int.negOfNat 362600284431309986886405511901652), (Int.ofNat 58670181425884956249313259315973), (Int.negOfNat 8497782750393641112482975370596), (Int.negOfNat 1345653153182636719112261264298), (Int.ofNat 221015708771757406428883064281), (Int.ofNat 33375966816400718126301545911), (Int.negOfNat 4073348440468006301384695899), (Int.negOfNat 523134321931448931675751896), (Int.ofNat 47213717011453429538586777), (Int.ofNat 5095433840264504124405162), (Int.negOfNat 363128374225433292215400), (Int.negOfNat 33274528292730471222318), (Int.ofNat 1967843256309463750376), (Int.ofNat 154538320407648180550), (Int.negOfNat 8122135929713617018), (Int.negOfNat 523177417487043597), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(50962344023554817199225386049423/5629499534213120000000000000000000), (-90650071107827496721601377975413/2814749767106560000000000000000000), (58670181425884956249313259315973/11258999068426240000000000000000000), (-2124445687598410278120743842649/2814749767106560000000000000000000), (-672826576591318359556130632149/5629499534213120000000000000000000), (221015708771757406428883064281/11258999068426240000000000000000000), (33375966816400718126301545911/11258999068426240000000000000000000), (-4073348440468006301384695899/11258999068426240000000000000000000), (-65391790241431116459468987/1407374883553280000000000000000000), (47213717011453429538586777/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial157.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial157.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial157.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial157 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 469526084456422404137219883422556), (Int.negOfNat 251094878579233874530319342071970), (Int.negOfNat 2331298755338930319151393327137), (Int.negOfNat 7987081495525403495798988182367), (Int.ofNat 1380761003773419658661349416649), (Int.ofNat 167943015439249334225646094262), (Int.negOfNat 40202362802006191268631360179), (Int.negOfNat 3245080604131101784069627211), (Int.ofNat 603957165142551706311252814), (Int.ofNat 39981658286918038214621473), (Int.negOfNat 5652991143538186677279848), (Int.negOfNat 320108979002163390685200), (Int.ofNat 35981423718175970862482), (Int.ofNat 1777029860210408977044), (Int.negOfNat 164996394168827656800), (Int.negOfNat 7329006438282445312), (Int.ofNat 514834879455496063), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-117381521114105601034304970855639/2814749767106560000000000000000000), (-25109487857923387453031934207197/1125899906842624000000000000000000), (-2331298755338930319151393327137/11258999068426240000000000000000000), (-7987081495525403495798988182367/11258999068426240000000000000000000), (1380761003773419658661349416649/11258999068426240000000000000000000), (83971507719624667112823047131/5629499534213120000000000000000000), (-40202362802006191268631360179/11258999068426240000000000000000000), (-3245080604131101784069627211/11258999068426240000000000000000000), (301978582571275853155626407/5629499534213120000000000000000000), (39981658286918038214621473/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial157.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial157.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial157.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial157 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 1020290859156075740220368137481244), (Int.negOfNat 307138928628192445941224816648719), (Int.negOfNat 14314304657974551089474947817123), (Int.ofNat 2728424739180049531502535678035), (Int.ofNat 492592376755331237985414878418), (Int.negOfNat 286899884749394396401437642791), (Int.negOfNat 12471433152437460008268417901), (Int.ofNat 6084843047342597299629818449), (Int.ofNat 206101130472496122278598606), (Int.negOfNat 71802382694670830206542187), (Int.negOfNat 2138780201457032105192252), (Int.ofNat 550125067983897481380120), (Int.ofNat 14829537169019205421818), (Int.negOfNat 2947494697163406498356), (Int.negOfNat 72750957489211184360), (Int.ofNat 11806705275292124208), (Int.ofNat 221429044052271677), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-255072714789018935055092034370311/2814749767106560000000000000000000), (-307138928628192445941224816648719/11258999068426240000000000000000000), (-14314304657974551089474947817123/11258999068426240000000000000000000), (545684947836009906300507135607/2251799813685248000000000000000000), (246296188377665618992707439209/5629499534213120000000000000000000), (-286899884749394396401437642791/11258999068426240000000000000000000), (-12471433152437460008268417901/11258999068426240000000000000000000), (6084843047342597299629818449/11258999068426240000000000000000000), (103050565236248061139299303/5629499534213120000000000000000000), (-71802382694670830206542187/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial157.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial157.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial157.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial157 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 1671302195817039808180105381814759), (Int.negOfNat 338471527575073657045773275690261), (Int.negOfNat 7947824182270757449985294093863), (Int.negOfNat 3420264253322363808460887338324), (Int.negOfNat 1484358981128603364889062842679), (Int.ofNat 21663219038590938391264499348), (Int.ofNat 48699874007299107373932871369), (Int.negOfNat 65507887223369539710266499), (Int.negOfNat 753086935336337969665963804), (Int.negOfNat 1946797112162934370388983), (Int.ofNat 7131497653799164394667778), (Int.ofNat 36385300752979153448020), (Int.negOfNat 45526635227312652663742), (Int.negOfNat 304324609861554515024), (Int.ofNat 208486633997259373210), (Int.ofNat 1844439509307715382), (Int.negOfNat 697874458597266783), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-1671302195817039808180105381814759/11258999068426240000000000000000000), (-338471527575073657045773275690261/11258999068426240000000000000000000), (-7947824182270757449985294093863/11258999068426240000000000000000000), (-855066063330590952115221834581/2814749767106560000000000000000000), (-1484358981128603364889062842679/11258999068426240000000000000000000), (5415804759647734597816124837/2814749767106560000000000000000000), (48699874007299107373932871369/11258999068426240000000000000000000), (-65507887223369539710266499/11258999068426240000000000000000000), (-188271733834084492416490951/2814749767106560000000000000000000), (-1946797112162934370388983/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial157.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial157.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial157.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial157 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 2427533370871248155712894472580671), (Int.negOfNat 448491231374532824312690776943160), (Int.negOfNat 51995390160589468405658724256394), (Int.negOfNat 7927294998714620452854749350314), (Int.ofNat 876333197049480213848768430239), (Int.ofNat 313332257921651290533163431404), (Int.negOfNat 15972077968047810392409357419), (Int.negOfNat 6454116896492481189204806219), (Int.ofNat 209490682097966291921135914), (Int.ofNat 77904128669732653186355317), (Int.negOfNat 1652948778712686460956928), (Int.negOfNat 606638410192217424330600), (Int.ofNat 8428888644299452386022), (Int.ofNat 3279586595931471467026), (Int.negOfNat 30410891372766966150), (Int.negOfNat 13195996427685457238), (Int.ofNat 171839118953385603), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-2427533370871248155712894472580671/11258999068426240000000000000000000), (-11212280784363320607817269423579/281474976710656000000000000000000), (-25997695080294734202829362128197/5629499534213120000000000000000000), (-3963647499357310226427374675157/5629499534213120000000000000000000), (876333197049480213848768430239/11258999068426240000000000000000000), (78333064480412822633290857851/2814749767106560000000000000000000), (-15972077968047810392409357419/11258999068426240000000000000000000), (-6454116896492481189204806219/11258999068426240000000000000000000), (104745341048983145960567957/5629499534213120000000000000000000), (77904128669732653186355317/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial157.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial157.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial157.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial157 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 3573625488794923190804988062236309), (Int.negOfNat 704070083828033624536365942362598), (Int.negOfNat 60931711768927946200719696278570), (Int.ofNat 6191893561512003622348991310115), (Int.ofNat 1747280694019978251854981068112), (Int.negOfNat 198972045130834901487950461188), (Int.negOfNat 43873304410843335017004880289), (Int.ofNat 3866625075040541343842849009), (Int.ofNat 699614468051527020774499124), (Int.negOfNat 41980189067697867676447117), (Int.negOfNat 6862979040429167526194678), (Int.ofNat 288097220570219308486300), (Int.ofNat 44840555335192141612592), (Int.negOfNat 1365435468004599693486), (Int.negOfNat 207744712530455176160), (Int.ofNat 4551541916705423288), (Int.ofNat 608842862877515883), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-3573625488794923190804988062236309/11258999068426240000000000000000000), (-352035041914016812268182971181299/5629499534213120000000000000000000), (-6093171176892794620071969627857/1125899906842624000000000000000000), (1238378712302400724469798262023/2251799813685248000000000000000000), (109205043376248640740936316757/703687441776640000000000000000000), (-49743011282708725371987615297/2814749767106560000000000000000000), (-43873304410843335017004880289/11258999068426240000000000000000000), (3866625075040541343842849009/11258999068426240000000000000000000), (174903617012881755193624781/2814749767106560000000000000000000), (-41980189067697867676447117/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial157.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial157.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial157.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial157 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 5156529593794274719370307418340117), (Int.negOfNat 839601619489156936544222923676981), (Int.negOfNat 4702542401667423469025291479619), (Int.ofNat 8296123919651800284191877672593), (Int.negOfNat 1252960824140016278244928752169), (Int.negOfNat 214781447221483909022492487034), (Int.ofNat 43814565786830360615724222499), (Int.ofNat 4854705750185737687214587809), (Int.negOfNat 646139487836251107231826814), (Int.negOfNat 63445053043483456985007877), (Int.ofNat 5628554569276163799790178), (Int.ofNat 519280473701515297626600), (Int.negOfNat 32691261657385669742082), (Int.negOfNat 2899724319575225357256), (Int.ofNat 135588414639429408460), (Int.ofNat 11874258665964176438), (Int.negOfNat 535430083385792583), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-5156529593794274719370307418340117/11258999068426240000000000000000000), (-839601619489156936544222923676981/11258999068426240000000000000000000), (-4702542401667423469025291479619/11258999068426240000000000000000000), (8296123919651800284191877672593/11258999068426240000000000000000000), (-1252960824140016278244928752169/11258999068426240000000000000000000), (-107390723610741954511246243517/5629499534213120000000000000000000), (43814565786830360615724222499/11258999068426240000000000000000000), (4854705750185737687214587809/11258999068426240000000000000000000), (-323069743918125553615913407/5629499534213120000000000000000000), (-63445053043483456985007877/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial157.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial157.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial157.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial157 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 6811860079498323112064359121268286), (Int.negOfNat 806322355863849489825429821143733), (Int.ofNat 10225097917658184872496064354310), (Int.negOfNat 1984839025123364858188524822916), (Int.negOfNat 299524043788980114892730135952), (Int.ofNat 358056983734355515443764231378), (Int.ofNat 20926866691480689403380889869), (Int.negOfNat 7545458553134451597498874289), (Int.negOfNat 433894683701731595942226104), (Int.ofNat 84312703046946134419913687), (Int.ofNat 4800265544991257316010158), (Int.negOfNat 600151144259638675160440), (Int.negOfNat 33694251797309195068352), (Int.ofNat 2966549908408306556436), (Int.ofNat 164575481696070414880), (Int.negOfNat 10596373347541827278), (Int.negOfNat 519811267157764983), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-3405930039749161556032179560634143/5629499534213120000000000000000000), (-806322355863849489825429821143733/11258999068426240000000000000000000), (1022509791765818487249606435431/1125899906842624000000000000000000), (-496209756280841214547131205729/2814749767106560000000000000000000), (-18720252736811257180795633497/703687441776640000000000000000000), (179028491867177757721882115689/5629499534213120000000000000000000), (20926866691480689403380889869/11258999068426240000000000000000000), (-7545458553134451597498874289/11258999068426240000000000000000000), (-54236835462716449492778263/1407374883553280000000000000000000), (84312703046946134419913687/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial157.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial157.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial157.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial157 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 8392508506188887068807566585727128), (Int.negOfNat 769775538886101302295362369781128), (Int.ofNat 19371565250505686860668635529229), (Int.ofNat 8785370628943393413057327917578), (Int.ofNat 2314031789975198775515354208036), (Int.negOfNat 30393371397276625081010740386), (Int.negOfNat 70637853339090832742916099019), (Int.negOfNat 1383928793823756758232588699), (Int.ofNat 1032026586321172050131553354), (Int.ofNat 29329900487966081473965947), (Int.negOfNat 9132829687402390540777458), (Int.negOfNat 294496862281093785290290), (Int.ofNat 54131592301984304374972), (Int.ofNat 1844383866776682782356), (Int.negOfNat 229737188540984035930), (Int.negOfNat 8187935538506683038), (Int.ofNat 899021047818199563), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-1049063563273610883600945823215891/1407374883553280000000000000000000), (-96221942360762662786920296222641/1407374883553280000000000000000000), (19371565250505686860668635529229/11258999068426240000000000000000000), (4392685314471696706528663958789/5629499534213120000000000000000000), (578507947493799693878838552009/2814749767106560000000000000000000), (-15196685698638312540505370193/5629499534213120000000000000000000), (-70637853339090832742916099019/11258999068426240000000000000000000), (-1383928793823756758232588699/11258999068426240000000000000000000), (516013293160586025065776677/5629499534213120000000000000000000), (29329900487966081473965947/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial157.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial157.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial157.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial157 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 9752666909238875398083907959081312), (Int.negOfNat 528354056008031049480124308063296), (Int.ofNat 109180900116378346341720933245777), (Int.ofNat 15865637962071393442562657121210), (Int.negOfNat 1469447052126229707261713402505), (Int.negOfNat 549332986398502447404074495048), (Int.ofNat 13659410221627099923246359931), (Int.ofNat 10494634987269096413845846609), (Int.negOfNat 16079724654640468911495616), (Int.negOfNat 117837725782135592912078767), (Int.negOfNat 1131729679238651507283118), (Int.ofNat 850914459803188073213730), (Int.ofNat 13319357761866909575672), (Int.negOfNat 4257442493523696546506), (Int.negOfNat 80768060725210374890), (Int.ofNat 15704987254681354808), (Int.ofNat 309582683293878423), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-304770840913714856190122123721291/351843720888320000000000000000000), (-8255532125125485148126942313489/175921860444160000000000000000000), (109180900116378346341720933245777/11258999068426240000000000000000000), (1586563796207139344256265712121/1125899906842624000000000000000000), (-293889410425245941452342680501/2251799813685248000000000000000000), (-68666623299812805925509311881/1407374883553280000000000000000000), (13659410221627099923246359931/11258999068426240000000000000000000), (10494634987269096413845846609/11258999068426240000000000000000000), (-251245697728757326742119/175921860444160000000000000000000), (-117837725782135592912078767/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial157.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial157.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial157.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial157 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 10284662456630003740949468294946540), (Int.ofNat 14828380409876515707139759016367), (Int.ofNat 134931329647550223302632036894978), (Int.negOfNat 10444284954611440880801080968612), (Int.negOfNat 3677022128882820161696738874856), (Int.ofNat 267312388381196601105449942686), (Int.ofNat 88205389394438134936178808649), (Int.negOfNat 3463815252225411745195507571), (Int.negOfNat 1289725829422060312511495484), (Int.ofNat 21469064581691306058285513), (Int.ofNat 11619958333930669962424998), (Int.negOfNat 43296397327411488744150), (Int.negOfNat 69610661696860646705192), (Int.negOfNat 252082541038286641086), (Int.ofNat 296994154424275637170), (Int.ofNat 2356938463677465968), (Int.negOfNat 1082060626959970283), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-514233122831500187047473414747327/562949953421312000000000000000000), (14828380409876515707139759016367/11258999068426240000000000000000000), (67465664823775111651316018447489/5629499534213120000000000000000000), (-2611071238652860220200270242153/2814749767106560000000000000000000), (-459627766110352520212092359357/1407374883553280000000000000000000), (133656194190598300552724971343/5629499534213120000000000000000000), (88205389394438134936178808649/11258999068426240000000000000000000), (-3463815252225411745195507571/11258999068426240000000000000000000), (-322431457355515078127873871/2814749767106560000000000000000000), (21469064581691306058285513/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial157.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial157.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial157.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial157 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 9844218887706445998102434809793650), (Int.ofNat 347112310017557104086809832606545), (Int.ofNat 22159439131231141064834964853616), (Int.negOfNat 19021651059613816990674010701321), (Int.ofNat 2106361440616637503342223066705), (Int.ofNat 585887681459953290679981336798), (Int.negOfNat 55852310832491801251614661361), (Int.negOfNat 11744382863332487836411992619), (Int.ofNat 625372354270055576256872866), (Int.ofNat 137342959519130013246663427), (Int.negOfNat 3786314111242151766437182), (Int.negOfNat 1007039783609055189136310), (Int.ofNat 13702405908806719625768), (Int.ofNat 5060568483890363961116), (Int.negOfNat 28180589439142242550), (Int.negOfNat 18884402126919249618), (Int.negOfNat 7834309859106503), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-196884377754128919962048696195873/225179981368524800000000000000000), (69422462003511420817361966521309/2251799813685248000000000000000000), (1384964945701946316552185303351/703687441776640000000000000000000), (-19021651059613816990674010701321/11258999068426240000000000000000000), (421272288123327500668444613341/2251799813685248000000000000000000), (292943840729976645339990668399/5629499534213120000000000000000000), (-55852310832491801251614661361/11258999068426240000000000000000000), (-11744382863332487836411992619/11258999068426240000000000000000000), (312686177135027788128436433/5629499534213120000000000000000000), (137342959519130013246663427/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial157.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial157.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial157.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial157 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 9165932787841067800086817135540415), (Int.ofNat 306706395914588406328164284544434), (Int.negOfNat 14160282926669818280828699158398), (Int.ofNat 7512821592908160468442198980923), (Int.ofNat 2489939546959589875126688418143), (Int.negOfNat 571155682677156486700708865976), (Int.negOfNat 83694008262381642263800097709), (Int.ofNat 9947848971981052254591125151), (Int.ofNat 1383506974377341039617239224), (Int.negOfNat 85380254364014361235835553), (Int.negOfNat 12858569069684404695120558), (Int.ofNat 452715925468374749756420), (Int.ofNat 77346186662218201038052), (Int.negOfNat 1652755828078856401884), (Int.negOfNat 329007683156687208180), (Int.ofNat 4453587291709374222), (Int.ofNat 1114226019384355043), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-1833186557568213560017363427108083/2251799813685248000000000000000000), (153353197957294203164082142272217/5629499534213120000000000000000000), (-7080141463334909140414349579199/5629499534213120000000000000000000), (7512821592908160468442198980923/11258999068426240000000000000000000), (2489939546959589875126688418143/11258999068426240000000000000000000), (-71394460334644560837588608247/1407374883553280000000000000000000), (-83694008262381642263800097709/11258999068426240000000000000000000), (9947848971981052254591125151/11258999068426240000000000000000000), (172938371797167629952154903/1407374883553280000000000000000000), (-85380254364014361235835553/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial157.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial157.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial157.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial157 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 8531281074759306059481099128193025), (Int.ofNat 363753156218974131286713413346156), (Int.ofNat 33536410070875628723433795184664), (Int.negOfNat 1384284392993636084594033254378), (Int.negOfNat 4397403519101611307585977473152), (Int.negOfNat 375504244111890432287411213988), (Int.ofNat 120618370429930724932011955801), (Int.ofNat 11482385143783009111422308729), (Int.negOfNat 1382238016131825969315763446), (Int.negOfNat 144006251615896538961623677), (Int.ofNat 9375332546701220699896522), (Int.ofNat 1060433919274492735096480), (Int.negOfNat 43443593245544044933398), (Int.negOfNat 5290099140018780746256), (Int.ofNat 147975766197091916320), (Int.ofNat 19603005397051713018), (Int.negOfNat 355756654573300477), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-341251242990372242379243965127721/450359962737049600000000000000000), (90938289054743532821678353336539/2814749767106560000000000000000000), (4192051258859453590429224398083/1407374883553280000000000000000000), (-692142196496818042297016627189/5629499534213120000000000000000000), (-34354714992981338340515449009/87960930222080000000000000000000), (-93876061027972608071852803497/2814749767106560000000000000000000), (120618370429930724932011955801/11258999068426240000000000000000000), (11482385143783009111422308729/11258999068426240000000000000000000), (-691119008065912984657881723/5629499534213120000000000000000000), (-144006251615896538961623677/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial157.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial157.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial157.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial157 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 7754304698563833434249185218799343), (Int.ofNat 337144383782884651061925156598535), (Int.negOfNat 76689144368890854908514454496495), (Int.negOfNat 28923255967249074255195916418824), (Int.ofNat 334542226112678784880372747907), (Int.ofNat 1227894839004734141030766421706), (Int.ofNat 73395741633812025452297502729), (Int.negOfNat 18359087431390876600138002271), (Int.negOfNat 1406384721758129902972034964), (Int.ofNat 154647957068226795759229283), (Int.ofNat 13047679814433928050934578), (Int.negOfNat 870326035411500283396400), (Int.negOfNat 77072552706105804118072), (Int.ofNat 3568651799731503748934), (Int.ofNat 323201077899913243540), (Int.negOfNat 11013242627863078872), (Int.negOfNat 1025194423664604143), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-7754304698563833434249185218799343/11258999068426240000000000000000000), (67428876756576930212385031319707/2251799813685248000000000000000000), (-15337828873778170981702890899299/2251799813685248000000000000000000), (-3615406995906134281899489552353/1407374883553280000000000000000000), (334542226112678784880372747907/11258999068426240000000000000000000), (613947419502367070515383210853/5629499534213120000000000000000000), (73395741633812025452297502729/11258999068426240000000000000000000), (-18359087431390876600138002271/11258999068426240000000000000000000), (-351596180439532475743008741/2814749767106560000000000000000000), (154647957068226795759229283/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial157.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial157.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial157.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial157 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 7571435439403344738527648999680277), (Int.negOfNat 202915714328699220124051793198567), (Int.negOfNat 140376761013726874633368459370061), (Int.ofNat 22798480215985857812959508328567), (Int.ofNat 11055511224562338456213934713922), (Int.ofNat 321323924058969027930298560785), (Int.negOfNat 209811582858487495139594066301), (Int.negOfNat 12104696771832489317499213999), (Int.ofNat 2163533866959741393270150866), (Int.ofNat 145148711157309300142348377), (Int.negOfNat 14613775900889414932364232), (Int.negOfNat 1022603963934637455876460), (Int.ofNat 70766839796275323055678), (Int.ofNat 4944172999108545272606), (Int.negOfNat 259323587777359147850), (Int.negOfNat 17838314507154962618), (Int.ofNat 719347619005707457), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-7571435439403344738527648999680277/11258999068426240000000000000000000), (-202915714328699220124051793198567/11258999068426240000000000000000000), (-140376761013726874633368459370061/11258999068426240000000000000000000), (22798480215985857812959508328567/11258999068426240000000000000000000), (5527755612281169228106967356961/5629499534213120000000000000000000), (64264784811793805586059712157/2251799813685248000000000000000000), (-209811582858487495139594066301/11258999068426240000000000000000000), (-12104696771832489317499213999/11258999068426240000000000000000000), (1081766933479870696635075433/5629499534213120000000000000000000), (145148711157309300142348377/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial157.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial157.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial157.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial157 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 8183581420121228820889982099832189), (Int.negOfNat 154599941838516980512264989310754), (Int.ofNat 233317380366231112882673268999238), (Int.ofNat 88145949837370039510885407602235), (Int.ofNat 1070002410239216541715759401900), (Int.negOfNat 2090918096107460500139400845196), (Int.negOfNat 98608840409434015934341103829), (Int.ofNat 26183288916455635929338298021), (Int.ofNat 1498538543831945620874439324), (Int.negOfNat 211925120689027008785678103), (Int.negOfNat 12488924293623321038290318), (Int.ofNat 1211303300542970197397700), (Int.ofNat 69361867751502634267062), (Int.negOfNat 5157157036716605925944), (Int.negOfNat 279721732440823962410), (Int.ofNat 16736960016263506202), (Int.ofNat 936162827944853243), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-8183581420121228820889982099832189/11258999068426240000000000000000000), (-77299970919258490256132494655377/5629499534213120000000000000000000), (116658690183115556441336634499619/5629499534213120000000000000000000), (17629189967474007902177081520447/2251799813685248000000000000000000), (10700024102392165417157594019/112589990684262400000000000000000), (-522729524026865125034850211299/2814749767106560000000000000000000), (-98608840409434015934341103829/11258999068426240000000000000000000), (26183288916455635929338298021/11258999068426240000000000000000000), (374634635957986405218609831/2814749767106560000000000000000000), (-211925120689027008785678103/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial157.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial157.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial157.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial157 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 6906827978780241377222348140962168), (Int.ofNat 1697182154484934080458956820209348), (Int.ofNat 616131581646288220995823574720578), (Int.ofNat 13366008722182023344777182233597), (Int.negOfNat 17710525082324109309006027679509), (Int.negOfNat 890514305061759235394701423295), (Int.ofNat 272128133898251336361581935521), (Int.ofNat 15149599885310633295906166449), (Int.negOfNat 2665840801830299146968085046), (Int.negOfNat 143685121424867070152381127), (Int.ofNat 18133779471095041902771212), (Int.ofNat 901694285534421499482700), (Int.negOfNat 90258805086475466536418), (Int.negOfNat 4070335857496458169316), (Int.ofNat 341544879484018167140), (Int.ofNat 13936773005607399648), (Int.negOfNat 1053261384864864137), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-863353497347530172152793517620271/1407374883553280000000000000000000), (424295538621233520114739205052337/2814749767106560000000000000000000), (308065790823144110497911787360289/5629499534213120000000000000000000), (13366008722182023344777182233597/11258999068426240000000000000000000), (-17710525082324109309006027679509/11258999068426240000000000000000000), (-178102861012351847078940284659/2251799813685248000000000000000000), (272128133898251336361581935521/11258999068426240000000000000000000), (15149599885310633295906166449/11258999068426240000000000000000000), (-1332920400915149573484042523/5629499534213120000000000000000000), (-143685121424867070152381127/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial157.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial157.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial157.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial157.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial157 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial157 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial157 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 9694626792958848016740241120698691), (Int.negOfNat 2113176084116231165177624043948649), (Int.ofNat 698720077205846180924969408400798), (Int.negOfNat 9834097957141060068444188104839), (Int.negOfNat 18151319323296199627057987018886), (Int.ofNat 880347947484357289321776236381), (Int.ofNat 273112894548616378052556630421), (Int.negOfNat 15134377770861909658184717949), (Int.negOfNat 2667048063363311935055931446), (Int.ofNat 143671095275962320771587427), (Int.ofNat 18134710441461844552232312), (Int.negOfNat 901685103994675471629100), (Int.negOfNat 90258805086475466536418), (Int.ofNat 4070335857496458169316), (Int.ofNat 341544879484018167140), (Int.negOfNat 13936773005607399648), (Int.negOfNat 1053261384864864137), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-9694626792958848016740241120698691/11258999068426240000000000000000000), (-2113176084116231165177624043948649/11258999068426240000000000000000000), (349360038602923090462484704200399/5629499534213120000000000000000000), (-9834097957141060068444188104839/11258999068426240000000000000000000), (-9075659661648099813528993509443/5629499534213120000000000000000000), (880347947484357289321776236381/11258999068426240000000000000000000), (273112894548616378052556630421/11258999068426240000000000000000000), (-15134377770861909658184717949/11258999068426240000000000000000000), (-1333524031681655967527965723/5629499534213120000000000000000000), (143671095275962320771587427/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial157.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial157.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial157.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 11452072198659912435514389096068649), (Int.ofNat 96618829165998320969117535881280), (Int.ofNat 325949324845914596061767300909398), (Int.negOfNat 88383185405618206418659616781200), (Int.ofNat 589496568623605072882242595247), (Int.ofNat 2093286116413330739898299175639), (Int.negOfNat 97552378449080874121687644429), (Int.negOfNat 26188474831641542459635116021), (Int.ofNat 1497254050688609299331994324), (Int.ofNat 211930752930739047722270703), (Int.negOfNat 12487936990438049430324718), (Int.negOfNat 1211306743620374957842800), (Int.ofNat 69361867751502634267062), (Int.ofNat 5157157036716605925944), (Int.negOfNat 279721732440823962410), (Int.negOfNat 16736960016263506202), (Int.ofNat 936162827944853243), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-11452072198659912435514389096068649/11258999068426240000000000000000000), (301933841143744753028492299629/35184372088832000000000000000000), (162974662422957298030883650454699/5629499534213120000000000000000000), (-220957963514045516046649041953/28147497671065600000000000000000), (589496568623605072882242595247/11258999068426240000000000000000000), (2093286116413330739898299175639/11258999068426240000000000000000000), (-97552378449080874121687644429/11258999068426240000000000000000000), (-26188474831641542459635116021/11258999068426240000000000000000000), (374313512672152324832998581/2814749767106560000000000000000000), (211930752930739047722270703/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial157.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial157.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial157.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 10594804241907673774951282291410027), (Int.ofNat 497628027509859492616950307838258), (Int.negOfNat 60263127209061492254174862221281), (Int.negOfNat 26621168489447591775475276310552), (Int.ofNat 10659218369368566538834372731976), (Int.negOfNat 307270276800720672901885198281), (Int.negOfNat 208964570358463572860009404901), (Int.ofNat 12080685143085265009697571999), (Int.ofNat 2162519510403427708859913566), (Int.negOfNat 145125042752871043770563877), (Int.negOfNat 14613001239449909944406232), (Int.ofNat 1022589043932550160614360), (Int.ofNat 70766839796275323055678), (Int.negOfNat 4944172999108545272606), (Int.negOfNat 259323587777359147850), (Int.ofNat 17838314507154962618), (Int.ofNat 719347619005707457), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-10594804241907673774951282291410027/11258999068426240000000000000000000), (248814013754929746308475153919129/5629499534213120000000000000000000), (-60263127209061492254174862221281/11258999068426240000000000000000000), (-3327646061180948971934409538819/1407374883553280000000000000000000), (1332402296171070817354296591497/1407374883553280000000000000000000), (-307270276800720672901885198281/11258999068426240000000000000000000), (-208964570358463572860009404901/11258999068426240000000000000000000), (12080685143085265009697571999/11258999068426240000000000000000000), (1081259755201713854429956783/5629499534213120000000000000000000), (-145125042752871043770563877/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial157.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial157.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial157.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 9904215926130969130682353510508166), (Int.ofNat 220744014554938567282935416671249), (Int.negOfNat 27712929960931684750045268070035), (Int.ofNat 22612766951415709884976354009809), (Int.ofNat 121852403261997631582080453663), (Int.negOfNat 1206094980358806747397258257719), (Int.ofNat 73811242416128363525871503929), (Int.ofNat 18322907716535388297742993471), (Int.negOfNat 1406856692315092645751875164), (Int.negOfNat 154612780000496600528755283), (Int.ofNat 13048029829660179250663578), (Int.ofNat 870304229254603467244100), (Int.negOfNat 77072552706105804118072), (Int.negOfNat 3568651799731503748934), (Int.ofNat 323201077899913243540), (Int.ofNat 11013242627863078872), (Int.negOfNat 1025194423664604143), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-4952107963065484565341176755254083/5629499534213120000000000000000000), (220744014554938567282935416671249/11258999068426240000000000000000000), (-5542585992186336950009053614007/2251799813685248000000000000000000), (22612766951415709884976354009809/11258999068426240000000000000000000), (121852403261997631582080453663/11258999068426240000000000000000000), (-1206094980358806747397258257719/11258999068426240000000000000000000), (73811242416128363525871503929/11258999068426240000000000000000000), (18322907716535388297742993471/11258999068426240000000000000000000), (-351714173078773161437968791/2814749767106560000000000000000000), (-154612780000496600528755283/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial157.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial157.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial157.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 9422678143289722087277446898731928), (Int.ofNat 309315312845781166408400972434203), (Int.ofNat 41363850463081090027403820447174), (Int.negOfNat 5710161620655119228316220846297), (Int.negOfNat 4377678062545308435382889531339), (Int.ofNat 399112635484167302895512749951), (Int.ofNat 120498969818717695650194556561), (Int.negOfNat 11520836679498062550069585029), (Int.negOfNat 1382044400084323530339470946), (Int.ofNat 144043296027996105927009277), (Int.ofNat 9375164123570961051790222), (Int.negOfNat 1060458020816326058212180), (Int.negOfNat 43443593245544044933398), (Int.ofNat 5290099140018780746256), (Int.ofNat 147975766197091916320), (Int.negOfNat 19603005397051713018), (Int.negOfNat 355756654573300477), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-1177834767911215260909680862341491/1407374883553280000000000000000000), (309315312845781166408400972434203/11258999068426240000000000000000000), (20681925231540545013701910223587/5629499534213120000000000000000000), (-5710161620655119228316220846297/11258999068426240000000000000000000), (-4377678062545308435382889531339/11258999068426240000000000000000000), (399112635484167302895512749951/11258999068426240000000000000000000), (120498969818717695650194556561/11258999068426240000000000000000000), (-11520836679498062550069585029/11258999068426240000000000000000000), (-691022200042161765169735473/5629499534213120000000000000000000), (144043296027996105927009277/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial157.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial157.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial157.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 8735580144076405318500718596084632), (Int.ofNat 315018499761277621188755529343312), (Int.negOfNat 46591416854327784597899072052538), (Int.negOfNat 13545222702493853824080444595345), (Int.ofNat 2728181431980906602906016697140), (Int.ofNat 590260724684637454579256182149), (Int.negOfNat 84306054672900673343493652809), (Int.negOfNat 9978149823099482331753724851), (Int.ofNat 1384307347132812404716881224), (Int.ofNat 85409055998685104276603553), (Int.negOfNat 12859206580395040291349058), (Int.negOfNat 452734288547866805463620), (Int.ofNat 77346186662218201038052), (Int.ofNat 1652755828078856401884), (Int.negOfNat 329007683156687208180), (Int.negOfNat 4453587291709374222), (Int.ofNat 1114226019384355043), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-1091947518009550664812589824510579/1407374883553280000000000000000000), (19688656235079851324297220583957/703687441776640000000000000000000), (-23295708427163892298949536026269/5629499534213120000000000000000000), (-2709044540498770764816088919069/2251799813685248000000000000000000), (136409071599045330145300834857/562949953421312000000000000000000), (590260724684637454579256182149/11258999068426240000000000000000000), (-84306054672900673343493652809/11258999068426240000000000000000000), (-9978149823099482331753724851/11258999068426240000000000000000000), (173038418391601550589610153/1407374883553280000000000000000000), (85409055998685104276603553/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial157.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial157.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial157.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 8344019796198193679866784820610270), (Int.ofNat 81521175105237732524044839659836), (Int.negOfNat 39385587002783091997587651113374), (Int.ofNat 15546069402931140341331406721233), (Int.ofNat 2491449985967137078181575824209), (Int.negOfNat 576261473540713766425263287301), (Int.negOfNat 56781959737745886517357410761), (Int.ofNat 11730337460226004417041855619), (Int.ofNat 626555532188119021792744366), (Int.negOfNat 137330208769280980807266127), (Int.negOfNat 3787244379419716538400382), (Int.ofNat 1007032897454245668246110), (Int.ofNat 13702405908806719625768), (Int.negOfNat 5060568483890363961116), (Int.negOfNat 28180589439142242550), (Int.ofNat 18884402126919249618), (Int.negOfNat 7834309859106503), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-834401979619819367986678482061027/1125899906842624000000000000000000), (20380293776309433131011209914959/2814749767106560000000000000000000), (-19692793501391545998793825556687/5629499534213120000000000000000000), (15546069402931140341331406721233/11258999068426240000000000000000000), (2491449985967137078181575824209/11258999068426240000000000000000000), (-576261473540713766425263287301/11258999068426240000000000000000000), (-56781959737745886517357410761/11258999068426240000000000000000000), (11730337460226004417041855619/11258999068426240000000000000000000), (313277766094059510896372183/5629499534213120000000000000000000), (-137330208769280980807266127/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial157.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial157.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial157.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 8194772684173097875722321726739523), (Int.ofNat 138827401563340637670796152569057), (Int.ofNat 62314649153500749665270056392338), (Int.ofNat 10280024966635493734903734876044), (Int.negOfNat 3254019350472858368870911598100), (Int.negOfNat 269473693475551667067384834992), (Int.ofNat 87216978003459305710064031949), (Int.ofNat 3469615339145672052097769471), (Int.negOfNat 1288486879867242181773880884), (Int.negOfNat 21475740915182098640192613), (Int.ofNat 11618991976872400530833598), (Int.ofNat 43302135789752756152650), (Int.negOfNat 69610661696860646705192), (Int.ofNat 252082541038286641086), (Int.ofNat 296994154424275637170), (Int.negOfNat 2356938463677465968), (Int.negOfNat 1082060626959970283), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-8194772684173097875722321726739523/11258999068426240000000000000000000), (138827401563340637670796152569057/11258999068426240000000000000000000), (31157324576750374832635028196169/5629499534213120000000000000000000), (2570006241658873433725933719011/2814749767106560000000000000000000), (-32540193504728583688709115981/112589990684262400000000000000000), (-16842105842221979191711552187/703687441776640000000000000000000), (87216978003459305710064031949/11258999068426240000000000000000000), (3469615339145672052097769471/11258999068426240000000000000000000), (-322121719966810545443470221/2814749767106560000000000000000000), (-21475740915182098640192613/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial157.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial157.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial157.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 7640609695168105739000631304328095), (Int.ofNat 402749252516853066245949895851915), (Int.ofNat 45326679347882093099398689826317), (Int.negOfNat 12885055999586799803713949533552), (Int.negOfNat 1124390019813724822053089074992), (Int.ofNat 536331929732100945450065795811), (Int.ofNat 12883324006287485831977731891), (Int.negOfNat 10470864576358044410315534509), (Int.negOfNat 15125021011106753921450716), (Int.ofNat 117813586602593259527275567), (Int.negOfNat 1132468155909927297711718), (Int.negOfNat 850898392108632524469930), (Int.ofNat 13319357761866909575672), (Int.ofNat 4257442493523696546506), (Int.negOfNat 80768060725210374890), (Int.negOfNat 15704987254681354808), (Int.ofNat 309582683293878423), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-1528121939033621147800126260865619/2251799813685248000000000000000000), (80549850503370613249189979170383/2251799813685248000000000000000000), (45326679347882093099398689826317/11258999068426240000000000000000000), (-805315999974174987732121845847/703687441776640000000000000000000), (-70274376238357801378318067187/703687441776640000000000000000000), (536331929732100945450065795811/11258999068426240000000000000000000), (12883324006287485831977731891/11258999068426240000000000000000000), (-10470864576358044410315534509/11258999068426240000000000000000000), (-3781255252776688480362679/2814749767106560000000000000000000), (117813586602593259527275567/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial157.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial157.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial157.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 6758174643354054788999935869676035), (Int.ofNat 434385135365814093622217821395827), (Int.negOfNat 19526574922989242657476378112211), (Int.negOfNat 3673666622458713553305476970563), (Int.ofNat 2490131520178749353734330099353), (Int.ofNat 10449583165485498943118553662), (Int.negOfNat 70992676269158392218174753319), (Int.ofNat 1418881487935128876176441499), (Int.ofNat 1032437379179462970448738554), (Int.negOfNat 29364754087762277591934647), (Int.negOfNat 9133136727593127559988058), (Int.ofNat 294519816130458854924290), (Int.ofNat 54131592301984304374972), (Int.negOfNat 1844383866776682782356), (Int.negOfNat 229737188540984035930), (Int.ofNat 8187935538506683038), (Int.ofNat 899021047818199563), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-1351634928670810957799987173935207/2251799813685248000000000000000000), (434385135365814093622217821395827/11258999068426240000000000000000000), (-19526574922989242657476378112211/11258999068426240000000000000000000), (-3673666622458713553305476970563/11258999068426240000000000000000000), (2490131520178749353734330099353/11258999068426240000000000000000000), (5224791582742749471559276831/5629499534213120000000000000000000), (-70992676269158392218174753319/11258999068426240000000000000000000), (1418881487935128876176441499/11258999068426240000000000000000000), (516218689589731485224369277/5629499534213120000000000000000000), (-29364754087762277591934647/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial157.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial157.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial157.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 5960844705559553544765420286968493), (Int.ofNat 380667399869865597126913732508144), (Int.ofNat 4566975588797601925127158709063), (Int.ofNat 7670936188890264718080006434311), (Int.negOfNat 334048429527506810929814860365), (Int.negOfNat 379210654915792654398470810011), (Int.ofNat 21083274037388811606162179469), (Int.ofNat 7581791152487187787167512189), (Int.negOfNat 434136142454346605351724404), (Int.negOfNat 84348603579814123907848187), (Int.ofNat 4800470279753836811736558), (Int.ofNat 600174098109003744794440), (Int.negOfNat 33694251797309195068352), (Int.negOfNat 2966549908408306556436), (Int.ofNat 164575481696070414880), (Int.ofNat 10596373347541827278), (Int.negOfNat 519811267157764983), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-5960844705559553544765420286968493/11258999068426240000000000000000000), (23791712491866599820432108281759/703687441776640000000000000000000), (4566975588797601925127158709063/11258999068426240000000000000000000), (7670936188890264718080006434311/11258999068426240000000000000000000), (-66809685905501362185962972073/2251799813685248000000000000000000), (-379210654915792654398470810011/11258999068426240000000000000000000), (21083274037388811606162179469/11258999068426240000000000000000000), (7581791152487187787167512189/11258999068426240000000000000000000), (-108534035613586651337931101/2814749767106560000000000000000000), (-84348603579814123907848187/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial157.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial157.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial157.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 5135182570792865295365830172301440), (Int.ofNat 456796244662077166731825992494692), (Int.ofNat 21296397453956993508192687386751), (Int.negOfNat 3687618838085424680506326098448), (Int.negOfNat 1479875819772325215186929206646), (Int.ofNat 198378377661453707770628434118), (Int.ofNat 44429483377094898354457209259), (Int.negOfNat 4827091152518647159946250909), (Int.negOfNat 646961049341055187684095014), (Int.ofNat 63418020585706614292082377), (Int.ofNat 5629216085641108181233178), (Int.negOfNat 519263258314491495401100), (Int.negOfNat 32691261657385669742082), (Int.ofNat 2899724319575225357256), (Int.ofNat 135588414639429408460), (Int.negOfNat 11874258665964176438), (Int.negOfNat 535430083385792583), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-8023722766863852024009109644221/17592186044416000000000000000000), (114199061165519291682956498123673/2814749767106560000000000000000000), (21296397453956993508192687386751/11258999068426240000000000000000000), (-230476177380339042531645381153/703687441776640000000000000000000), (-739937909886162607593464603323/5629499534213120000000000000000000), (99189188830726853885314217059/5629499534213120000000000000000000), (44429483377094898354457209259/11258999068426240000000000000000000), (-4827091152518647159946250909/11258999068426240000000000000000000), (-323480524670527593842047507/5629499534213120000000000000000000), (63418020585706614292082377/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial157.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial157.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial157.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 4181138287585207698779820469102582), (Int.ofNat 472118539496700086903921834399367), (Int.negOfNat 13875398392597460454973016038570), (Int.negOfNat 3942586978229382631473097273290), (Int.ofNat 1399942554363881752535466949095), (Int.ofNat 191850850883552835419082639851), (Int.negOfNat 42979512465350068092306480849), (Int.negOfNat 3855332995560419607700546109), (Int.ofNat 698444850286042009273973324), (Int.ofNat 41969458097354000503699117), (Int.negOfNat 6862048230860847840346478), (Int.negOfNat 288090334415409787596100), (Int.ofNat 44840555335192141612592), (Int.ofNat 1365435468004599693486), (Int.negOfNat 207744712530455176160), (Int.negOfNat 4551541916705423288), (Int.ofNat 608842862877515883), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-2090569143792603849389910234551291/5629499534213120000000000000000000), (472118539496700086903921834399367/11258999068426240000000000000000000), (-1387539839259746045497301603857/1125899906842624000000000000000000), (-394258697822938263147309727329/1125899906842624000000000000000000), (279988510872776350507093389819/2251799813685248000000000000000000), (191850850883552835419082639851/11258999068426240000000000000000000), (-42979512465350068092306480849/11258999068426240000000000000000000), (-3855332995560419607700546109/11258999068426240000000000000000000), (174611212571510502318493331/2814749767106560000000000000000000), (41969458097354000503699117/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial157.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial157.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial157.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 3298456496483833811989201986214628), (Int.ofNat 420247552860879945789518145904339), (Int.negOfNat 129084356103185052197142486864), (Int.ofNat 7260239851933297307053291780742), (Int.ofNat 513231906865067856513993785596), (Int.negOfNat 309317381251890952846051346888), (Int.negOfNat 15055207392694388302660533119), (Int.ofNat 6446066398459938392214514619), (Int.ofNat 208300382103327977438000014), (Int.negOfNat 77895651109574590994158717), (Int.negOfNat 1652005663166355712703128), (Int.ofNat 606632671729876156922100), (Int.ofNat 8428888644299452386022), (Int.negOfNat 3279586595931471467026), (Int.negOfNat 30410891372766966150), (Int.ofNat 13195996427685457238), (Int.ofNat 171839118953385603), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-824614124120958452997300496553657/2814749767106560000000000000000000), (420247552860879945789518145904339/11258999068426240000000000000000000), (-8067772256449065762321405429/703687441776640000000000000000000), (3630119925966648653526645890371/5629499534213120000000000000000000), (128307976716266964128498446399/2814749767106560000000000000000000), (-38664672656486369105756418361/1407374883553280000000000000000000), (-15055207392694388302660533119/11258999068426240000000000000000000), (6446066398459938392214514619/11258999068426240000000000000000000), (104150191051663988719000007/5629499534213120000000000000000000), (-77895651109574590994158717/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial157.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial157.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial157.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 2402207691172326605147365688017366), (Int.ofNat 498561597318286868533771668433692), (Int.ofNat 31735465649144587803032460174767), (Int.ofNat 149111635592129558216771719896), (Int.negOfNat 1755839971656726508840769143062), (Int.negOfNat 7830901849683302238585767941), (Int.ofNat 49379481726144585731668313269), (Int.ofNat 40497819111772960636433199), (Int.negOfNat 753965935363236959062957504), (Int.ofNat 1972077292751586993137083), (Int.ofNat 7132192963659876928775578), (Int.negOfNat 36402516140002955673520), (Int.negOfNat 45526635227312652663742), (Int.ofNat 304324609861554515024), (Int.ofNat 208486633997259373210), (Int.negOfNat 1844439509307715382), (Int.negOfNat 697874458597266783), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-1201103845586163302573682844008683/5629499534213120000000000000000000), (124640399329571717133442917108423/2814749767106560000000000000000000), (31735465649144587803032460174767/11258999068426240000000000000000000), (18638954449016194777096464987/1407374883553280000000000000000000), (-877919985828363254420384571531/5629499534213120000000000000000000), (-7830901849683302238585767941/11258999068426240000000000000000000), (49379481726144585731668313269/11258999068426240000000000000000000), (40497819111772960636433199/11258999068426240000000000000000000), (-11780717740050577485358711/175921860444160000000000000000000), (1972077292751586993137083/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial157.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial157.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial157.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 1302313256137391045376934572801604), (Int.ofNat 579245961652453308925109729147310), (Int.ofNat 477959009283850645812346909117), (Int.negOfNat 7524830302682951961960713726473), (Int.ofNat 392334267438769248565816721031), (Int.ofNat 306448913449153909443167060958), (Int.negOfNat 12221350498967098235200424401), (Int.negOfNat 6119703813176183979626832649), (Int.ofNat 205778175762440770203542106), (Int.ofNat 71837411177394126424382287), (Int.negOfNat 2138525095089940106361752), (Int.negOfNat 550148021833262551014120), (Int.ofNat 14829537169019205421818), (Int.ofNat 2947494697163406498356), (Int.negOfNat 72750957489211184360), (Int.negOfNat 11806705275292124208), (Int.ofNat 221429044052271677), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-325578314034347761344233643200401/2814749767106560000000000000000000), (57924596165245330892510972914731/1125899906842624000000000000000000), (477959009283850645812346909117/11258999068426240000000000000000000), (-7524830302682951961960713726473/11258999068426240000000000000000000), (392334267438769248565816721031/11258999068426240000000000000000000), (153224456724576954721583530479/5629499534213120000000000000000000), (-12221350498967098235200424401/11258999068426240000000000000000000), (-6119703813176183979626832649/11258999068426240000000000000000000), (102889087881220385101771053/5629499534213120000000000000000000), (71837411177394126424382287/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial157.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial157.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial157.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 187503687474464201514695731136016), (Int.ofNat 523201911603708382875252424244159), (Int.negOfNat 17123562422481732967372767132197), (Int.ofNat 3190675932026062484853252530845), (Int.ofNat 1481019113093012702169355139042), (Int.negOfNat 148393986739711239253830752369), (Int.negOfNat 40452445455476553041699353679), (Int.ofNat 3210219838297515104072613011), (Int.ofNat 604280119852607058386309314), (Int.negOfNat 39946629804194741996781373), (Int.negOfNat 5653246249905278676110348), (Int.ofNat 320086025152798321051200), (Int.ofNat 35981423718175970862482), (Int.negOfNat 1777029860210408977044), (Int.negOfNat 164996394168827656800), (Int.ofNat 7329006438282445312), (Int.ofNat 514834879455496063), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-11718980467154012594668483196001/703687441776640000000000000000000), (523201911603708382875252424244159/11258999068426240000000000000000000), (-17123562422481732967372767132197/11258999068426240000000000000000000), (638135186405212496970650506169/2251799813685248000000000000000000), (740509556546506351084677569521/5629499534213120000000000000000000), (-148393986739711239253830752369/11258999068426240000000000000000000), (-40452445455476553041699353679/11258999068426240000000000000000000), (3210219838297515104072613011/11258999068426240000000000000000000), (302140059926303529193154657/5629499534213120000000000000000000), (-39946629804194741996781373/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial157.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial157.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial157.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 832830183403911654592860738187839), (Int.ofNat 522690354175184127935468434822161), (Int.ofNat 18986891594590772244098281285643), (Int.ofNat 5226630132666124198097032031464), (Int.negOfNat 1074172162654922802708997705881), (Int.negOfNat 207183391582518558466111952348), (Int.ofNat 32696359097555239768566104011), (Int.ofNat 4048338372356409722310862599), (Int.negOfNat 522255321904549942278758196), (Int.negOfNat 47188436830864776915838677), (Int.ofNat 5094738530403791590297362), (Int.ofNat 363111158838409489989900), (Int.negOfNat 33274528292730471222318), (Int.negOfNat 1967843256309463750376), (Int.ofNat 154538320407648180550), (Int.ofNat 8122135929713617018), (Int.negOfNat 523177417487043597), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(832830183403911654592860738187839/11258999068426240000000000000000000), (522690354175184127935468434822161/11258999068426240000000000000000000), (18986891594590772244098281285643/11258999068426240000000000000000000), (653328766583265524762129003933/1407374883553280000000000000000000), (-1074172162654922802708997705881/11258999068426240000000000000000000), (-51795847895629639616527988087/2814749767106560000000000000000000), (32696359097555239768566104011/11258999068426240000000000000000000), (4048338372356409722310862599/11258999068426240000000000000000000), (-130563830476137485569689549/2814749767106560000000000000000000), (-47188436830864776915838677/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial157.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial157.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial157.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1974613583511827611983431515739091), (Int.ofNat 617886418490206089242055534403360), (Int.ofNat 17472569509426968713266063194614), (Int.negOfNat 5255766609832401675341003151926), (Int.negOfNat 746829264345244420105081450999), (Int.ofNat 244107351227609129514270432336), (Int.ofNat 19390670683699089887505023259), (Int.negOfNat 5276718360950622203448811861), (Int.negOfNat 285638239246854775811130934), (Int.ofNat 65056005606186198129318723), (Int.ofNat 2714900859417450790738268), (Int.negOfNat 514173336872258480552460), (Int.negOfNat 17868026207328318921142), (Int.ofNat 2809697707783865173134), (Int.ofNat 85420103620847156510), (Int.negOfNat 11230547939830008282), (Int.negOfNat 180921113596339383), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(1974613583511827611983431515739091/11258999068426240000000000000000000), (3861790115563788057762847090021/70368744177664000000000000000000), (8736284754713484356633031597307/5629499534213120000000000000000000), (-2627883304916200837670501575963/5629499534213120000000000000000000), (-746829264345244420105081450999/11258999068426240000000000000000000), (15256709451725570594641902021/703687441776640000000000000000000), (19390670683699089887505023259/11258999068426240000000000000000000), (-5276718360950622203448811861/11258999068426240000000000000000000), (-142819119623427387905565467/5629499534213120000000000000000000), (65056005606186198129318723/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial157.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial157.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial157.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3234620178803263425412701780528149), (Int.ofNat 621561809351560532633031413214618), (Int.negOfNat 11545564232607560385727342041990), (Int.negOfNat 1461850032218799071710765108055), (Int.ofNat 1336182949506980291466424238428), (Int.ofNat 42593519143377677144229555028), (Int.negOfNat 41640870843109185010641021151), (Int.negOfNat 713704856220472400746320449), (Int.ofNat 676156329692391334025489736), (Int.ofNat 8584770632380765590681357), (Int.negOfNat 6662696761340552839463322), (Int.negOfNat 76783018785356247442300), (Int.ofNat 43711334248613729535528), (Int.ofNat 496183448541039827366), (Int.negOfNat 203567108615019856680), (Int.negOfNat 2398418541313189688), (Int.ofNat 612209013206794497), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(3234620178803263425412701780528149/11258999068426240000000000000000000), (310780904675780266316515706607309/5629499534213120000000000000000000), (-1154556423260756038572734204199/1125899906842624000000000000000000), (-292370006443759814342153021611/2251799813685248000000000000000000), (334045737376745072866606059607/2814749767106560000000000000000000), (10648379785844419286057388757/2814749767106560000000000000000000), (-41640870843109185010641021151/11258999068426240000000000000000000), (-713704856220472400746320449/11258999068426240000000000000000000), (84519541211548916753186217/1407374883553280000000000000000000), (8584770632380765590681357/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial157.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial157.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial157.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4440022981488699341090351475176117), (Int.ofNat 596366163663998351595429401774321), (Int.ofNat 5861060678532198482921452144839), (Int.ofNat 5026298288063838746475077054847), (Int.negOfNat 231541233004269412841874737591), (Int.negOfNat 248435821963818733194902574206), (Int.ofNat 8881441788027223663847320081), (Int.ofNat 5612742646829646994762708991), (Int.negOfNat 141984203425050111275165286), (Int.negOfNat 71691291390003484514623823), (Int.ofNat 1202122077206473582002542), (Int.ofNat 581121984370068608039380), (Int.negOfNat 6030314896147260797338), (Int.negOfNat 3225425533725526745184), (Int.ofNat 18760178556698386420), (Int.ofNat 12995238829726758682), (Int.negOfNat 182669850836067597), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(4440022981488699341090351475176117/11258999068426240000000000000000000), (596366163663998351595429401774321/11258999068426240000000000000000000), (5861060678532198482921452144839/11258999068426240000000000000000000), (5026298288063838746475077054847/11258999068426240000000000000000000), (-231541233004269412841874737591/11258999068426240000000000000000000), (-124217910981909366597451287103/5629499534213120000000000000000000), (8881441788027223663847320081/11258999068426240000000000000000000), (5612742646829646994762708991/11258999068426240000000000000000000), (-70992101712525055637582643/5629499534213120000000000000000000), (-71691291390003484514623823/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial157.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial157.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial157.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 5685971491949697661602035903712426), (Int.ofNat 656763363523861084114138455449213), (Int.ofNat 15934822887368323208233675930930), (Int.negOfNat 2797721151086758494859104539924), (Int.negOfNat 1020714024804997780370024414268), (Int.ofNat 146733555583578702736855037002), (Int.ofNat 34992781196195800453316598291), (Int.negOfNat 3238633705995939313664601871), (Int.negOfNat 615869724153344675150636796), (Int.ofNat 37753122633603534197619473), (Int.ofNat 6450131458166402625729702), (Int.negOfNat 266312151235853648912480), (Int.negOfNat 44065647260544336234508), (Int.ofNat 1249596724823069150084), (Int.ofNat 210421410502985935920), (Int.negOfNat 4161236794840514962), (Int.negOfNat 701240608926545397), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(2842985745974848830801017951856213/5629499534213120000000000000000000), (656763363523861084114138455449213/11258999068426240000000000000000000), (1593482288736832320823367593093/1125899906842624000000000000000000), (-699430287771689623714776134981/2814749767106560000000000000000000), (-255178506201249445092506103567/2814749767106560000000000000000000), (73366777791789351368427518501/5629499534213120000000000000000000), (34992781196195800453316598291/11258999068426240000000000000000000), (-3238633705995939313664601871/11258999068426240000000000000000000), (-153967431038336168787659199/2814749767106560000000000000000000), (37753122633603534197619473/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial157.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial157.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial157.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 7030912343085295401895090929985328), (Int.ofNat 670758906838500137467971915164648), (Int.negOfNat 8253621624071237292201576262849), (Int.negOfNat 2126185588669734648382421663858), (Int.ofNat 1172330338808657709254769387644), (Int.ofNat 135082897997041066886579818946), (Int.negOfNat 38406224208341746435418399281), (Int.negOfNat 3768187062457889960459134781), (Int.ofNat 610381314565169678918527566), (Int.ofNat 56063246611094023012739473), (Int.negOfNat 5550719264074828142075182), (Int.negOfNat 500990486100982765884310), (Int.ofNat 32357862633307342819168), (Int.ofNat 2938988080298321054844), (Int.negOfNat 131781944012059750390), (Int.negOfNat 12276635559594295282), (Int.ofNat 546260815268474577), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(439432021442830962618443183124083/703687441776640000000000000000000), (83844863354812517183496489395581/1407374883553280000000000000000000), (-8253621624071237292201576262849/11258999068426240000000000000000000), (-1063092794334867324191210831929/5629499534213120000000000000000000), (293082584702164427313692346911/2814749767106560000000000000000000), (67541448998520533443289909473/5629499534213120000000000000000000), (-38406224208341746435418399281/11258999068426240000000000000000000), (-3768187062457889960459134781/11258999068426240000000000000000000), (305190657282584839459263783/5629499534213120000000000000000000), (56063246611094023012739473/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial157.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial157.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial157.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 8342724203527477201091592941879912), (Int.ofNat 652210324243777772277166170760276), (Int.ofNat 7458797381869085336309749292983), (Int.ofNat 5693757316014897598453863412950), (Int.negOfNat 17385513983840714240544895675), (Int.negOfNat 311339274839808068263191494692), (Int.negOfNat 8750259833356436295707423091), (Int.ofNat 7164876674830000031767536051), (Int.ofNat 302712963581920942956519256), (Int.negOfNat 86170033374622971538677013), (Int.negOfNat 4306588765989876812561842), (Int.ofNat 622448814779002296497650), (Int.ofNat 33878540738893296737848), (Int.negOfNat 3032272136412047801854), (Int.negOfNat 173709071603417395110), (Int.ofNat 10971762550227355152), (Int.ofNat 669075216502160637), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(1042840525440934650136449117734989/1407374883553280000000000000000000), (163052581060944443069291542690069/2814749767106560000000000000000000), (7458797381869085336309749292983/11258999068426240000000000000000000), (113875146320297951969077268259/225179981368524800000000000000000), (-695420559353628569621795827/450359962737049600000000000000000), (-77834818709952017065797873673/2814749767106560000000000000000000), (-8750259833356436295707423091/11258999068426240000000000000000000), (7164876674830000031767536051/11258999068426240000000000000000000), (37839120447740117869564907/1407374883553280000000000000000000), (-86170033374622971538677013/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial157.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial157.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial157.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 9712676514397244180267185130276000), (Int.ofNat 726533996002457292907928475265413), (Int.ofNat 19126739017362811766426157015202), (Int.negOfNat 4244432569416122641980282565968), (Int.negOfNat 1686576348179483067768227965924), (Int.ofNat 133375697765156578882802197374), (Int.ofNat 63523800868962650614848451951), (Int.negOfNat 777776031169362042967259329), (Int.negOfNat 1081249398374685752290629316), (Int.negOfNat 17370462893512112327675013), (Int.ofNat 9888258050475606343267882), (Int.ofNat 279627037648635135594330), (Int.negOfNat 57801772266983229741608), (Int.negOfNat 1985963698193510992634), (Int.ofNat 238044008763828070430), (Int.ofNat 9097220687356400472), (Int.negOfNat 848009188703246497), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(2428169128599311045066796282569/2814749767106560000000000000000), (726533996002457292907928475265413/11258999068426240000000000000000000), (9563369508681405883213078507601/5629499534213120000000000000000000), (-265277035588507665123767660373/703687441776640000000000000000000), (-421644087044870766942056991481/2814749767106560000000000000000000), (66687848882578289441401098687/5629499534213120000000000000000000), (63523800868962650614848451951/11258999068426240000000000000000000), (-777776031169362042967259329/11258999068426240000000000000000000), (-270312349593671438072657329/2814749767106560000000000000000000), (-17370462893512112327675013/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial157.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial157.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial157.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 11189269526443548724697181166479270), (Int.ofNat 719560559512452922588950130111715), (Int.negOfNat 23324569948198933510484067950876), (Int.negOfNat 4547950953070145084911487778099), (Int.ofNat 2096715883954294939711066153255), (Int.ofNat 392667322459834458951911909282), (Int.negOfNat 46434008574802337160327290499), (Int.negOfNat 11178161520085941848814623821), (Int.ofNat 266044516738980547370780374), (Int.ofNat 134411903141869147654177073), (Int.ofNat 492371483801557825850702), (Int.negOfNat 954425374439182090680690), (Int.negOfNat 14763274556022206729828), (Int.ofNat 4615841539685733979524), (Int.ofNat 98869646090317837270), (Int.negOfNat 16802759625056572222), (Int.negOfNat 486035637360389917), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(1118926952644354872469718116647927/1125899906842624000000000000000000), (143912111902490584517790026022343/2251799813685248000000000000000000), (-5831142487049733377621016987719/2814749767106560000000000000000000), (-4547950953070145084911487778099/11258999068426240000000000000000000), (419343176790858987942213230651/2251799813685248000000000000000000), (196333661229917229475955954641/5629499534213120000000000000000000), (-46434008574802337160327290499/11258999068426240000000000000000000), (-11178161520085941848814623821/11258999068426240000000000000000000), (133022258369490273685390187/5629499534213120000000000000000000), (134411903141869147654177073/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial157.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial157.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial157.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 12540554439496628128931625875985355), (Int.ofNat 656845791283437433223980588076306), (Int.ofNat 13541083544089064023183450745778), (Int.ofNat 15409585423999238257543438703777), (Int.ofNat 913556262392548049094779867597), (Int.negOfNat 737521957583930670915103646244), (Int.negOfNat 95090091934486070755930106411), (Int.ofNat 8014708850004505115748236649), (Int.ofNat 1592080496664216298296950836), (Int.negOfNat 38133320712413709978615367), (Int.negOfNat 13927360164997706958441422), (Int.ofNat 42036665629135700521260), (Int.ofNat 79309766588592123474488), (Int.ofNat 535375215894725734564), (Int.negOfNat 324496430893366629420), (Int.negOfNat 3988606780216872942), (Int.ofNat 1058237772567133057), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(2508110887899325625786325175197071/2251799813685248000000000000000000), (328422895641718716611990294038153/5629499534213120000000000000000000), (6770541772044532011591725372889/5629499534213120000000000000000000), (15409585423999238257543438703777/11258999068426240000000000000000000), (913556262392548049094779867597/11258999068426240000000000000000000), (-184380489395982667728775911561/2814749767106560000000000000000000), (-95090091934486070755930106411/11258999068426240000000000000000000), (8014708850004505115748236649/11258999068426240000000000000000000), (398020124166054074574237709/2814749767106560000000000000000000), (-38133320712413709978615367/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial157.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial157.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial157.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 14018017550730750362611730482053665), (Int.ofNat 852964022998378996254793226619584), (Int.ofNat 54009806118758034377429244454856), (Int.negOfNat 15064319296470228881936325127102), (Int.negOfNat 8469070808758456316726581548948), (Int.negOfNat 672177679867969803808975341492), (Int.ofNat 128185993520565373865453614059), (Int.ofNat 16774682165028606038768657631), (Int.negOfNat 957622232690927459107784014), (Int.negOfNat 182208924017504892307392503), (Int.ofNat 4125153949476535771962478), (Int.ofNat 1226900207309016192891300), (Int.negOfNat 9525544269166269596462), (Int.negOfNat 5779921035545038629224), (Int.ofNat 828570559519185200), (Int.ofNat 20489082752514065622), (Int.ofNat 122444672927982937), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(2803603510146150072522346096410733/2251799813685248000000000000000000), (13327562859349671816481144165931/175921860444160000000000000000000), (6751225764844754297178655556857/1407374883553280000000000000000000), (-7532159648235114440968162563551/5629499534213120000000000000000000), (-2117267702189614079181645387237/2814749767106560000000000000000000), (-168044419966992450952243835373/2814749767106560000000000000000000), (128185993520565373865453614059/11258999068426240000000000000000000), (16774682165028606038768657631/11258999068426240000000000000000000), (-478811116345463729553892007/5629499534213120000000000000000000), (-182208924017504892307392503/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial157.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial157.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial157.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 15672474719937089615295442148492203), (Int.ofNat 594207693268061231050713440521945), (Int.negOfNat 253845954504269248489857101268025), (Int.negOfNat 82383567119355672731724224370056), (Int.negOfNat 4505979903708860018901953479307), (Int.ofNat 1545514329949452039000671662734), (Int.ofNat 163551461020422333681946062791), (Int.negOfNat 15190226232795970470282352329), (Int.negOfNat 2172382692775990249945038256), (Int.ofNat 93654176324063567810403237), (Int.ofNat 17247063361433599726495542), (Int.negOfNat 390781029683043536610600), (Int.negOfNat 93808789485298533352928), (Int.ofNat 1143647295696323405986), (Int.ofNat 374833201130473079300), (Int.negOfNat 2056224650619531048), (Int.negOfNat 1147269368286883957), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(15672474719937089615295442148492203/11258999068426240000000000000000000), (118841538653612246210142688104389/2251799813685248000000000000000000), (-10153838180170769939594284050721/450359962737049600000000000000000), (-10297945889919459091465528046257/1407374883553280000000000000000000), (-4505979903708860018901953479307/11258999068426240000000000000000000), (772757164974726019500335831367/5629499534213120000000000000000000), (163551461020422333681946062791/11258999068426240000000000000000000), (-15190226232795970470282352329/11258999068426240000000000000000000), (-135773918298499390621564891/703687441776640000000000000000000), (93654176324063567810403237/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial157.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial157.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial157.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 15171829788908426123512345916985197), (Int.negOfNat 1407659521720946888898228245454793), (Int.negOfNat 706884901291184982455521815175239), (Int.negOfNat 42100104569949085758300312538727), (Int.ofNat 14657727080642303378824540859798), (Int.ofNat 1566491665227566974325491985515), (Int.negOfNat 182333476017542497523293905299), (Int.negOfNat 24065914965692341528681998841), (Int.ofNat 1472633122912176500814532914), (Int.ofNat 222264673779689921139682943), (Int.negOfNat 8273124648881639334921428), (Int.negOfNat 1392532437743441529339400), (Int.ofNat 34093299241927951825922), (Int.ofNat 6330764301411849283794), (Int.negOfNat 107053790457373742110), (Int.negOfNat 21810820514235346422), (Int.ofNat 241146291504424043), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(15171829788908426123512345916985197/11258999068426240000000000000000000), (-1407659521720946888898228245454793/11258999068426240000000000000000000), (-706884901291184982455521815175239/11258999068426240000000000000000000), (-42100104569949085758300312538727/11258999068426240000000000000000000), (7328863540321151689412270429899/5629499534213120000000000000000000), (313298333045513394865098397103/2251799813685248000000000000000000), (-182333476017542497523293905299/11258999068426240000000000000000000), (-24065914965692341528681998841/11258999068426240000000000000000000), (736316561456088250407266457/5629499534213120000000000000000000), (222264673779689921139682943/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial157.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial157.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial157.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 9462551549813064699334136811266069), (Int.negOfNat 4189860151421446092056807881750566), (Int.negOfNat 538781182977336302715816783679618), (Int.ofNat 98824643572357371621560679117165), (Int.ofNat 15026158104749787215357663802640), (Int.negOfNat 1637741592755038766667403061884), (Int.negOfNat 250072437837314353315834908711), (Int.ofNat 17686503314723965813338290039), (Int.ofNat 2639809693687890191342090036), (Int.negOfNat 130262241657691090575978037), (Int.negOfNat 18969163679720506172571942), (Int.ofNat 690791957062933932578220), (Int.ofNat 98153976470182170989078), (Int.negOfNat 2755635385041662534096), (Int.negOfNat 382348533899865586150), (Int.ofNat 8452206076632669718), (Int.ofNat 1236300964006634857), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(9462551549813064699334136811266069/11258999068426240000000000000000000), (-2094930075710723046028403940875283/5629499534213120000000000000000000), (-269390591488668151357908391839809/5629499534213120000000000000000000), (19764928714471474324312135823433/2251799813685248000000000000000000), (187826976309372340191970797533/140737488355328000000000000000000), (-409435398188759691666850765471/2814749767106560000000000000000000), (-250072437837314353315834908711/11258999068426240000000000000000000), (17686503314723965813338290039/11258999068426240000000000000000000), (659952423421972547835522509/2814749767106560000000000000000000), (-130262241657691090575978037/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial157.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial157.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial157.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 106834840350122601573078939533592), (Int.negOfNat 4847045858811117132889046441613948), (Int.ofNat 239580369879692587744106902740482), (Int.ofNat 127195143753122929484363301608163), (Int.negOfNat 9186710247434219205684130332851), (Int.negOfNat 2356773403277224892652756043625), (Int.ofNat 157073629843123537522518860819), (Int.ofNat 28640188201210869700195946371), (Int.negOfNat 1606535913687335873617849634), (Int.negOfNat 236670029311032754378262313), (Int.ofNat 11053805542224963274665908), (Int.ofNat 1396271340686622816212420), (Int.negOfNat 54777776319643371238762), (Int.negOfNat 6128941746327864885524), (Int.ofNat 205516829152194922820), (Int.ofNat 20421529361842013392), (Int.negOfNat 634414454510081323), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-13354355043765325196634867441699/1407374883553280000000000000000000), (-1211761464702779283222261610403487/2814749767106560000000000000000000), (119790184939846293872053451370241/5629499534213120000000000000000000), (127195143753122929484363301608163/11258999068426240000000000000000000), (-9186710247434219205684130332851/11258999068426240000000000000000000), (-18854187226217799141222048349/90071992547409920000000000000000), (157073629843123537522518860819/11258999068426240000000000000000000), (28640188201210869700195946371/11258999068426240000000000000000000), (-803267956843667936808924817/5629499534213120000000000000000000), (-236670029311032754378262313/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial157.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial157.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial157.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial157.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial157.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial157.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial157.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial157.reflect := by
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

end Bin157
end
end ErdosOverlap.OuterNumerics
