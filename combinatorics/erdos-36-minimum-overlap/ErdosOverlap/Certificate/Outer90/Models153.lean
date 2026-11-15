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

/-! # Exact integer weighted outer models for source bin 153

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin153

def weightDenominator : ℤ := (Int.ofNat 2000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 396393608055145280)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 392335300411969460)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 374446459927555320)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 283824070250054300)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 191774247491110200)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 122827203082826450)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 66722984595818948)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 25595564231768158)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial153.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial153.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 1909041126952351800)⟩, ⟨(314159265359/50000000000), (Int.ofNat 546243378720967500)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 322659316347215240)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 190752833054986000)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 111937877472658960)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 50661816953296434)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 16424882249875292)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 6310096123460015)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 4995746668289958)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial153.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial153.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 1909041126952351800)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 546243378720967500)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 322659316347215240)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 190752833054986000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 111937877472658960)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 50661816953296434)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 16424882249875292)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 6310096123460015)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 4995746668289958)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial153.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial153.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial153.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 1260204298059379383427898627801389), (Int.ofNat 990448476382248180219051406077757), (Int.ofNat 136666171118962656148030405269998), (Int.negOfNat 30886348970189127547689427244987), (Int.negOfNat 3696779534298222155095264226826), (Int.ofNat 590761643159193377715771492617), (Int.ofNat 53576594410576837005097334407), (Int.negOfNat 7044462896250648480617381165), (Int.negOfNat 495017191926871109955211034), (Int.ofNat 56584639072728392998579537), (Int.ofNat 3176030522135813508778910), (Int.negOfNat 324722389204246754429660), (Int.negOfNat 14961320043990022605796), (Int.ofNat 1391062442673101163072), (Int.ofNat 54077220722936763952), (Int.negOfNat 4533610609082401754), (Int.negOfNat 158416229621459975), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1260204298059379383427898627801389/2251799813685248000000000000000000), (990448476382248180219051406077757/2251799813685248000000000000000000), (68333085559481328074015202634999/1125899906842624000000000000000000), (-30886348970189127547689427244987/2251799813685248000000000000000000), (-1848389767149111077547632113413/1125899906842624000000000000000000), (590761643159193377715771492617/2251799813685248000000000000000000), (53576594410576837005097334407/2251799813685248000000000000000000), (-1408892579250129696123476233/450359962737049600000000000000000), (-247508595963435554977605517/1125899906842624000000000000000000), (56584639072728392998579537/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial153.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial153.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial153.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial153 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 982454443240626425134103329848857), (Int.ofNat 1102207534704268048746009167194706), (Int.negOfNat 82588854594994404128592782420222), (Int.negOfNat 32751814617598383295212032019398), (Int.ofNat 3154337438596970510656716991753), (Int.ofNat 549244648269901442225292276119), (Int.negOfNat 57142628114228773088152588691), (Int.negOfNat 5693031013621559079281737995), (Int.ofNat 611583798868515677045935140), (Int.ofNat 40084738481953517045143019), (Int.negOfNat 4359677877850157327854048), (Int.negOfNat 204306440953277550263724), (Int.ofNat 22238576752776452898908), (Int.ofNat 788448874808335733772), (Int.negOfNat 85356293578329990144), (Int.negOfNat 2336689635631235938), (Int.ofNat 272185017014815901), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(982454443240626425134103329848857/2251799813685248000000000000000000), (551103767352134024373004583597353/1125899906842624000000000000000000), (-41294427297497202064296391210111/1125899906842624000000000000000000), (-16375907308799191647606016009699/1125899906842624000000000000000000), (3154337438596970510656716991753/2251799813685248000000000000000000), (549244648269901442225292276119/2251799813685248000000000000000000), (-57142628114228773088152588691/2251799813685248000000000000000000), (-1138606202724311815856347599/450359962737049600000000000000000), (30579189943425783852296757/112589990684262400000000000000000), (40084738481953517045143019/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial153.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial153.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial153.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial153 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 2658331271122876883561200590675297), (Int.ofNat 510881420813741107649431381592226), (Int.negOfNat 175769731960738178675050001137793), (Int.ofNat 3360281282040829437317905902370), (Int.ofNat 4406563835728855540533833222604), (Int.negOfNat 298656506601657676845938325835), (Int.negOfNat 57660831684022552724879493605), (Int.ofNat 5210909111953074636935741461), (Int.ofNat 469830707025921415809194980), (Int.negOfNat 49724901421401128637034913), (Int.negOfNat 2635398219241402371157002), (Int.ofNat 312779625053024027481284), (Int.ofNat 10839023091568703955894), (Int.negOfNat 1413509762745521291124), (Int.negOfNat 34072936211101687632), (Int.ofNat 4837293047302316478), (Int.ofNat 76633790257865543), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(2658331271122876883561200590675297/2251799813685248000000000000000000), (255440710406870553824715690796113/1125899906842624000000000000000000), (-175769731960738178675050001137793/2251799813685248000000000000000000), (336028128204082943731790590237/225179981368524800000000000000000), (1101640958932213885133458305651/562949953421312000000000000000000), (-59731301320331535369187665167/450359962737049600000000000000000), (-11532166336804510544975898721/450359962737049600000000000000000), (5210909111953074636935741461/2251799813685248000000000000000000), (23491535351296070790459749/112589990684262400000000000000000), (-49724901421401128637034913/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial153.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial153.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial153.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial153 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 3061914943318035981161512701336876), (Int.negOfNat 43136243040750844256795841261133), (Int.negOfNat 83488150791037385191412389584991), (Int.ofNat 20907046082611867616601805755099), (Int.negOfNat 276250037610169278550378596615), (Int.negOfNat 454021609506545659507417892301), (Int.ofNat 30583960566373464061011975387), (Int.ofNat 4801954459131603714608161699), (Int.negOfNat 461561367683053141943002786), (Int.negOfNat 31313879499006730037808269), (Int.ofNat 3801212075096355615242366), (Int.ofNat 139484183943476791898994), (Int.negOfNat 20856725569322128896304), (Int.negOfNat 449861041800162627884), (Int.ofNat 83176393402030693750), (Int.ofNat 998400106268353960), (Int.negOfNat 257197777009946027), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(765478735829508995290378175334219/562949953421312000000000000000000), (-43136243040750844256795841261133/2251799813685248000000000000000000), (-83488150791037385191412389584991/2251799813685248000000000000000000), (20907046082611867616601805755099/2251799813685248000000000000000000), (-55250007522033855710075719323/450359962737049600000000000000000), (-454021609506545659507417892301/2251799813685248000000000000000000), (30583960566373464061011975387/2251799813685248000000000000000000), (4801954459131603714608161699/2251799813685248000000000000000000), (-230780683841526570971501393/1125899906842624000000000000000000), (-31313879499006730037808269/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial153.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial153.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial153.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial153 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 2792439452232799357873241947122006), (Int.negOfNat 163866906651628494276386916051951), (Int.ofNat 8644315534620126866411428965520), (Int.ofNat 7185108549501470457584684901929), (Int.negOfNat 2225828562874893724204254680315), (Int.ofNat 79042912626432337169109368893), (Int.ofNat 38640256186480592396723359251), (Int.negOfNat 3247702993388700112882759969), (Int.negOfNat 324524752672337460683261604), (Int.ofNat 38854298239818704619787117), (Int.ofNat 1643476699938521010290270), (Int.negOfNat 270000636444151316421132), (Int.negOfNat 5392770254271974111072), (Int.ofNat 1283569175216199051566), (Int.ofNat 11222316976569091254), (Int.negOfNat 4582664838627253002), (Int.ofNat 152902437438931), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(1396219726116399678936620973561003/1125899906842624000000000000000000), (-163866906651628494276386916051951/2251799813685248000000000000000000), (108053944182751585830142862069/28147497671065600000000000000000), (7185108549501470457584684901929/2251799813685248000000000000000000), (-445165712574978744840850936063/450359962737049600000000000000000), (79042912626432337169109368893/2251799813685248000000000000000000), (38640256186480592396723359251/2251799813685248000000000000000000), (-3247702993388700112882759969/2251799813685248000000000000000000), (-81131188168084365170815401/562949953421312000000000000000000), (38854298239818704619787117/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial153.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial153.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial153.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial153 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 2525675089560622306736130708431166), (Int.negOfNat 102244948404382270499813708059602), (Int.ofNat 11358382200107544282275938223300), (Int.negOfNat 3455136296701292236254404650063), (Int.negOfNat 222679030311185126874460455200), (Int.ofNat 208005774543731485265463105745), (Int.negOfNat 15573564502167384426834491037), (Int.negOfNat 2690978335160930457961276697), (Int.ofNat 322983591710802900824761726), (Int.ofNat 16848235349685699437016757), (Int.negOfNat 3013569856314449856410920), (Int.negOfNat 57152292302060021415110), (Int.ofNat 17576399928852292209486), (Int.ofNat 74398414059734462022), (Int.negOfNat 72432585766876737854), (Int.ofNat 291165618192265174), (Int.ofNat 242210537005076153), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(1262837544780311153368065354215583/1125899906842624000000000000000000), (-51122474202191135249906854029801/1125899906842624000000000000000000), (113583822001075442822759382233/22517998136852480000000000000000), (-3455136296701292236254404650063/2251799813685248000000000000000000), (-278348787888981408593075569/2814749767106560000000000000000), (41601154908746297053092621149/450359962737049600000000000000000), (-15573564502167384426834491037/2251799813685248000000000000000000), (-2690978335160930457961276697/2251799813685248000000000000000000), (161491795855401450412380863/1125899906842624000000000000000000), (16848235349685699437016757/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial153.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial153.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial153.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial153 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 2340817976716040305409435615026626), (Int.negOfNat 92600096762404434186252711835146), (Int.negOfNat 3000992295859706422491764813744), (Int.negOfNat 292446470645223550866083779337), (Int.ofNat 558430783724204564158327864033), (Int.negOfNat 50512930086034248176091925119), (Int.negOfNat 15719105429116509904592046543), (Int.ofNat 2131616272953866619476127039), (Int.ofNat 137634133342872872395281134), (Int.negOfNat 28460132416267743457304215), (Int.negOfNat 489917925236871927488714), (Int.ofNat 210711923027345295374090), (Int.negOfNat 291721523255298141926), (Int.negOfNat 1036672711416377836764), (Int.ofNat 11236119342859261116), (Int.ofNat 3826116838653406282), (Int.negOfNat 76939595132743405), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(1170408988358020152704717807513313/1125899906842624000000000000000000), (-46300048381202217093126355917573/1125899906842624000000000000000000), (-187562018491231651405735300859/140737488355328000000000000000000), (-292446470645223550866083779337/2251799813685248000000000000000000), (558430783724204564158327864033/2251799813685248000000000000000000), (-50512930086034248176091925119/2251799813685248000000000000000000), (-15719105429116509904592046543/2251799813685248000000000000000000), (2131616272953866619476127039/2251799813685248000000000000000000), (68817066671436436197640567/1125899906842624000000000000000000), (-5692026483253548691460843/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial153.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial153.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial153.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial153 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 2147880128377712731571172885478003), (Int.negOfNat 96272607016121105475860692796335), (Int.ofNat 2381101832742781533475609153634), (Int.ofNat 927823211895477923543449789210), (Int.negOfNat 251672685628937480662122861822), (Int.negOfNat 53871440641158397694820495320), (Int.ofNat 11654741244924817880098683701), (Int.ofNat 766952055366606228328342923), (Int.negOfNat 224819384822504686448291068), (Int.negOfNat 2518868928022872910022117), (Int.ofNat 2178447847959536925381984), (Int.negOfNat 21575417545393600278720), (Int.negOfNat 13089235997664532719528), (Int.ofNat 264761598304826419218), (Int.ofNat 54498103983071779954), (Int.negOfNat 1450070226979302650), (Int.negOfNat 201627732768438121), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(2147880128377712731571172885478003/2251799813685248000000000000000000), (-19254521403224221095172138559267/450359962737049600000000000000000), (1190550916371390766737804576817/1125899906842624000000000000000000), (92782321189547792354344978921/225179981368524800000000000000000), (-125836342814468740331061430911/1125899906842624000000000000000000), (-1346786016028959942370512383/56294995342131200000000000000000), (11654741244924817880098683701/2251799813685248000000000000000000), (766952055366606228328342923/2251799813685248000000000000000000), (-56204846205626171612072767/562949953421312000000000000000000), (-2518868928022872910022117/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial153.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial153.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial153.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial153 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 1967318624119670808833991980609199), (Int.negOfNat 85621667127916364225333055391985), (Int.ofNat 519892492836851037143582361207), (Int.negOfNat 1331391694232762629832900172116), (Int.negOfNat 111453585666295501508496453282), (Int.ofNat 60352046086927344185489348377), (Int.ofNat 1841553031404390541961611615), (Int.negOfNat 1497301555089093169112111993), (Int.ofNat 9589037933992990117953648), (Int.ofNat 19138147326688784908264951), (Int.negOfNat 476716662123246207151404), (Int.negOfNat 143224656331956628800852), (Int.ofNat 4958234545623873756208), (Int.ofNat 711059597603406745054), (Int.negOfNat 28798063350865580914), (Int.negOfNat 2611789956040698890), (Int.ofNat 118139230259699805), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(1967318624119670808833991980609199/2251799813685248000000000000000000), (-17124333425583272845066611078397/450359962737049600000000000000000), (519892492836851037143582361207/2251799813685248000000000000000000), (-332847923558190657458225043029/562949953421312000000000000000000), (-55726792833147750754248226641/1125899906842624000000000000000000), (60352046086927344185489348377/2251799813685248000000000000000000), (368310606280878108392322323/450359962737049600000000000000000), (-1497301555089093169112111993/2251799813685248000000000000000000), (599314870874561882372103/140737488355328000000000000000000), (19138147326688784908264951/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial153.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial153.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial153.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial153 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 1787589436812898436189208539961875), (Int.negOfNat 98524346191421941057741979441133), (Int.negOfNat 5783110738353551305910407103117), (Int.negOfNat 245339645488572034787006194479), (Int.ofNat 259616549763356428367819186739), (Int.negOfNat 7822493310686880695715977608), (Int.negOfNat 8483159363709919396119312917), (Int.ofNat 385880141544153745336200191), (Int.ofNat 140596217076102647442097294), (Int.negOfNat 7498815066945527812388847), (Int.negOfNat 1325183165556123795855910), (Int.ofNat 78120088128481318716434), (Int.ofNat 7918502325168204635610), (Int.negOfNat 501732070099543840464), (Int.negOfNat 32775589179759215856), (Int.ofNat 2221896118292482902), (Int.ofNat 140445110968321889), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(2860143098900637497902733663939/3602879701896396800000000000000), (-98524346191421941057741979441133/2251799813685248000000000000000000), (-5783110738353551305910407103117/2251799813685248000000000000000000), (-245339645488572034787006194479/2251799813685248000000000000000000), (259616549763356428367819186739/2251799813685248000000000000000000), (-977811663835860086964497201/281474976710656000000000000000000), (-8483159363709919396119312917/2251799813685248000000000000000000), (385880141544153745336200191/2251799813685248000000000000000000), (70298108538051323721048647/1125899906842624000000000000000000), (-7498815066945527812388847/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial153.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial153.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial153.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial153 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 1568886583885996002629606844246991), (Int.negOfNat 118253874087825805094330951215922), (Int.negOfNat 3222025214129181291356439995507), (Int.ofNat 572785158905697501459291386317), (Int.negOfNat 106036799299068635763676031097), (Int.negOfNat 37102166843000065185961242833), (Int.ofNat 4668123274028431293974933529), (Int.ofNat 831101643511066705299613439), (Int.negOfNat 92011408616214071358683714), (Int.negOfNat 9919649838818655112405363), (Int.ofNat 1053626984850459110386300), (Int.ofNat 71928638052328216222838), (Int.negOfNat 7694950405257187658134), (Int.negOfNat 346640529159832720706), (Int.ofNat 38621848666995449642), (Int.ofNat 1170248249339412930), (Int.negOfNat 128747554486598089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(1568886583885996002629606844246991/2251799813685248000000000000000000), (-59126937043912902547165475607961/1125899906842624000000000000000000), (-3222025214129181291356439995507/2251799813685248000000000000000000), (572785158905697501459291386317/2251799813685248000000000000000000), (-106036799299068635763676031097/2251799813685248000000000000000000), (-37102166843000065185961242833/2251799813685248000000000000000000), (4668123274028431293974933529/2251799813685248000000000000000000), (831101643511066705299613439/2251799813685248000000000000000000), (-46005704308107035679341857/1125899906842624000000000000000000), (-9919649838818655112405363/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial153.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial153.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial153.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial153 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 1321566857640608081278920687270554), (Int.negOfNat 129472363484132253888038789530914), (Int.negOfNat 3816512163897448534832645341283), (Int.negOfNat 747207842681850707698108691200), (Int.negOfNat 91172760396161612948260728566), (Int.ofNat 37279432997200717207626367302), (Int.ofNat 3436070291601118032875676931), (Int.negOfNat 893335929791423557461782593), (Int.negOfNat 53295077439962039227066500), (Int.ofNat 12100381580306896304741661), (Int.ofNat 467299162736633782768342), (Int.negOfNat 103179362318132713480984), (Int.negOfNat 2569110334084312007988), (Int.ofNat 596265436129546963466), (Int.ofNat 9433278698501540962), (Int.negOfNat 2478869451437333822), (Int.negOfNat 63658418273017415), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(660783428820304040639460343635277/1125899906842624000000000000000000), (-64736181742066126944019394765457/1125899906842624000000000000000000), (-3816512163897448534832645341283/2251799813685248000000000000000000), (-116751225419039173077829483/351843720888320000000000000000), (-45586380198080806474130364283/1125899906842624000000000000000000), (18639716498600358603813183651/1125899906842624000000000000000000), (3436070291601118032875676931/2251799813685248000000000000000000), (-893335929791423557461782593/2251799813685248000000000000000000), (-106590154879924078454133/4503599627370496000000000000000), (12100381580306896304741661/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial153.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial153.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial153.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial153 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 1041210971962105151018506124968374), (Int.negOfNat 153406064356670583047112394375701), (Int.negOfNat 7318561094705626955467927547414), (Int.ofNat 36344591042955921552843576482), (Int.ofNat 228567803461578412868980931781), (Int.ofNat 4645926901535922905844175631), (Int.negOfNat 6883451613697161197758029741), (Int.negOfNat 99279161380764664768213445), (Int.ofNat 116447931208110426376257146), (Int.ofNat 875743243954710193941299), (Int.negOfNat 1195771064667087969908618), (Int.negOfNat 2663899916562204602002), (Int.ofNat 8130504982704416019792), (Int.negOfNat 12490531013377365580), (Int.negOfNat 38903308203674637278), (Int.ofNat 202124706303856368), (Int.ofNat 113760314481728215), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(520605485981052575509253062484187/1125899906842624000000000000000000), (-153406064356670583047112394375701/2251799813685248000000000000000000), (-3659280547352813477733963773707/1125899906842624000000000000000000), (18172295521477960776421788241/1125899906842624000000000000000000), (228567803461578412868980931781/2251799813685248000000000000000000), (4645926901535922905844175631/2251799813685248000000000000000000), (-6883451613697161197758029741/2251799813685248000000000000000000), (-19855832276152932953642689/450359962737049600000000000000000), (58223965604055213188128573/1125899906842624000000000000000000), (875743243954710193941299/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial153.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial153.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial153.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial153 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 708796923175798341636549298019036), (Int.negOfNat 175809126749826460421659489925809), (Int.negOfNat 2762542978740695938406846734848), (Int.ofNat 1089562523524879188719045994020), (Int.negOfNat 47022124695685968685865630986), (Int.negOfNat 41300503850875409898646033522), (Int.ofNat 1749651003545109759705347485), (Int.ofNat 916552681137443007504858609), (Int.negOfNat 29606780299168907482403716), (Int.negOfNat 11719184571014981499767581), (Int.ofNat 319009528002764464557522), (Int.ofNat 95786175222367644160592), (Int.negOfNat 2339330312558141678494), (Int.negOfNat 538693395693046224236), (Int.ofNat 12124706032258304812), (Int.ofNat 2213940006610241666), (Int.negOfNat 13128274422287059), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(177199230793949585409137324504759/562949953421312000000000000000000), (-175809126749826460421659489925809/2251799813685248000000000000000000), (-5395591755352921754700872529/4398046511104000000000000000000), (54478126176243959435952299701/112589990684262400000000000000000), (-23511062347842984342932815493/1125899906842624000000000000000000), (-20650251925437704949323016761/1125899906842624000000000000000000), (349930200709021951941069497/450359962737049600000000000000000), (916552681137443007504858609/2251799813685248000000000000000000), (-7401695074792226870600929/562949953421312000000000000000000), (-11719184571014981499767581/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial153.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial153.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial153.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial153 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 352987253788755960380074932823328), (Int.negOfNat 177901438436946829994268435788364), (Int.ofNat 277177638296689598097558029641), (Int.negOfNat 252941027105169331633041233818), (Int.negOfNat 170966680753963104041753291846), (Int.ofNat 24804756592044246816892660231), (Int.ofNat 5635911015527925623389551519), (Int.negOfNat 542589676147482077836699031), (Int.negOfNat 93482811142818774081155296), (Int.ofNat 6833160842416342821668775), (Int.ofNat 944033989353256000016200), (Int.negOfNat 55991554093600387942416), (Int.negOfNat 6356471360530406199736), (Int.ofNat 319314278578758813736), (Int.ofNat 30275237683867459008), (Int.negOfNat 1423391600117790190), (Int.negOfNat 98773074476858341), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(11030851680898623761877341650729/70368744177664000000000000000000), (-44475359609236707498567108947091/562949953421312000000000000000000), (277177638296689598097558029641/2251799813685248000000000000000000), (-126470513552584665816520616909/1125899906842624000000000000000000), (-85483340376981552020876645923/1125899906842624000000000000000000), (24804756592044246816892660231/2251799813685248000000000000000000), (5635911015527925623389551519/2251799813685248000000000000000000), (-542589676147482077836699031/2251799813685248000000000000000000), (-2921337848213086690036103/70368744177664000000000000000000), (273326433696653712866751/90071992547409920000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial153.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial153.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial153.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial153 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 5400512577100854170020447532228), (Int.negOfNat 182551474863372917639747536930640), (Int.negOfNat 2498393991754805894510999808393), (Int.negOfNat 149842254195084792531066852237), (Int.ofNat 195821852146219742001657602687), (Int.ofNat 24197672346557718855176431358), (Int.negOfNat 5780924323815169687327343771), (Int.negOfNat 559105869344909253370280921), (Int.ofNat 92791057971513595941556866), (Int.ofNat 7255897467432468031905881), (Int.negOfNat 918719340105188126096730), (Int.negOfNat 60324005860728807667988), (Int.ofNat 6115015170318366837984), (Int.ofNat 345683063246378397404), (Int.negOfNat 29071656421206300244), (Int.negOfNat 1483498639407401390), (Int.ofNat 84919220449301575), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1350128144275213542505111883057/562949953421312000000000000000000), (-2281893435792161470496844211633/28147497671065600000000000000000), (-2498393991754805894510999808393/2251799813685248000000000000000000), (-149842254195084792531066852237/2251799813685248000000000000000000), (195821852146219742001657602687/2251799813685248000000000000000000), (12098836173278859427588215679/1125899906842624000000000000000000), (-5780924323815169687327343771/2251799813685248000000000000000000), (-559105869344909253370280921/2251799813685248000000000000000000), (46395528985756797970778433/1125899906842624000000000000000000), (7255897467432468031905881/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial153.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial153.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial153.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial153 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 378203413284158211787828500920426), (Int.negOfNat 187394944378310831219673237204343), (Int.ofNat 1662840727683391978671815537539), (Int.ofNat 1335988073060957156926548588493), (Int.ofNat 53547946490344718743386418208), (Int.negOfNat 44431708170718992930345930193), (Int.negOfNat 1906166595529652874517513509), (Int.ofNat 948376246831809048799337363), (Int.ofNat 34671234056249323273861106), (Int.negOfNat 11825991109246843451287455), (Int.negOfNat 384008488296322715018362), (Int.ofNat 94912334320270854297488), (Int.ofNat 2803521422430168740584), (Int.negOfNat 527432273690198148700), (Int.negOfNat 14341684940825054164), (Int.ofNat 2196552026065474938), (Int.ofNat 37590452676742109), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-189101706642079105893914250460213/1125899906842624000000000000000000), (-187394944378310831219673237204343/2251799813685248000000000000000000), (1662840727683391978671815537539/2251799813685248000000000000000000), (1335988073060957156926548588493/2251799813685248000000000000000000), (1673373327823272460730825569/70368744177664000000000000000000), (-44431708170718992930345930193/2251799813685248000000000000000000), (-1906166595529652874517513509/2251799813685248000000000000000000), (948376246831809048799337363/2251799813685248000000000000000000), (17335617028124661636930553/1125899906842624000000000000000000), (-2365198221849368690257491/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial153.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial153.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial153.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial153 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 736217055481559326271048340699415), (Int.negOfNat 166486439440858019929977227160755), (Int.ofNat 7595199507571340611433450123275), (Int.ofNat 210027201632106689880352382364), (Int.negOfNat 249442635135188176234534482845), (Int.ofNat 3861774249537329038255041950), (Int.ofNat 7464809183085769240509200321), (Int.negOfNat 56796409191146641861086775), (Int.negOfNat 122449124483821282931885640), (Int.ofNat 78974707980557169532659), (Int.ofNat 1224050028927527712407824), (Int.ofNat 4678937958908374119940), (Int.negOfNat 8147634022345407674360), (Int.negOfNat 53133608564174618868), (Int.ofNat 38498097471159849340), (Int.ofNat 403477204515750082), (Int.negOfNat 126118855576257975), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-147243411096311865254209668139883/450359962737049600000000000000000), (-33297287888171603985995445432151/450359962737049600000000000000000), (303807980302853624457338004931/90071992547409920000000000000000), (52506800408026672470088095591/562949953421312000000000000000000), (-49888527027037635246906896569/450359962737049600000000000000000), (77235484990746580765100839/45035996273704960000000000000000), (7464809183085769240509200321/2251799813685248000000000000000000), (-2271856367645865674443471/90071992547409920000000000000000), (-3061228112095532073297141/56294995342131200000000000000000), (78974707980557169532659/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial153.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial153.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial153.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial153 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 1040556022964759713468741540838297), (Int.negOfNat 139969823549178506844682270172918), (Int.ofNat 4725691555962252206316798327582), (Int.negOfNat 669389281451113361323780708040), (Int.ofNat 99972360251812798418478969593), (Int.ofNat 43175416969015497338967776652), (Int.negOfNat 3273787257594509505420822877), (Int.negOfNat 1000508935862905183592063051), (Int.ofNat 45973059171181047107915004), (Int.ofNat 13011725526809155072356539), (Int.negOfNat 367209709549665622058418), (Int.negOfNat 106909197306202845039796), (Int.ofNat 1868393230391640205810), (Int.ofNat 601587495035633987556), (Int.negOfNat 6654089869431799764), (Int.negOfNat 2500234464285389662), (Int.ofNat 44191986686852323), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-1040556022964759713468741540838297/2251799813685248000000000000000000), (-69984911774589253422341135086459/1125899906842624000000000000000000), (2362845777981126103158399163791/1125899906842624000000000000000000), (-16734732036277834033094517701/56294995342131200000000000000000), (99972360251812798418478969593/2251799813685248000000000000000000), (10793854242253874334741944163/562949953421312000000000000000000), (-3273787257594509505420822877/2251799813685248000000000000000000), (-1000508935862905183592063051/2251799813685248000000000000000000), (11493264792795261776978751/562949953421312000000000000000000), (13011725526809155072356539/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial153.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial153.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial153.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial153 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 1304286585980673708553346424509969), (Int.negOfNat 123449327256310210029960903549148), (Int.ofNat 5239993791937469979738804344056), (Int.ofNat 915871318500405155515228525891), (Int.ofNat 150102557889838095374536149052), (Int.negOfNat 39073676592151766999566727170), (Int.negOfNat 5970714891809972384426160183), (Int.ofNat 798533493022342991791724087), (Int.ofNat 109421754897499128695517358), (Int.negOfNat 8813436438567503588187941), (Int.negOfNat 1162953988868167302359314), (Int.ofNat 60967086445022675169838), (Int.ofNat 8037111630840220851452), (Int.negOfNat 288815012938749806232), (Int.negOfNat 38720811898660468214), (Int.ofNat 934812324847131896), (Int.ofNat 111131615571388101), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-1304286585980673708553346424509969/2251799813685248000000000000000000), (-30862331814077552507490225887287/562949953421312000000000000000000), (654999223992183747467350543007/281474976710656000000000000000000), (915871318500405155515228525891/2251799813685248000000000000000000), (37525639472459523843634037263/562949953421312000000000000000000), (-3907367659215176699956672717/225179981368524800000000000000000), (-5970714891809972384426160183/2251799813685248000000000000000000), (798533493022342991791724087/2251799813685248000000000000000000), (54710877448749564347758679/1125899906842624000000000000000000), (-8813436438567503588187941/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial153.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial153.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial153.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial153 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 1522004461523138905276648116093159), (Int.negOfNat 90523490663930275134231356601171), (Int.ofNat 10459706659003748433748708181617), (Int.ofNat 179818344127071432925639908379), (Int.negOfNat 300449307904140633214354436353), (Int.negOfNat 19283754839781426736123065840), (Int.ofNat 8920751604142366591059136495), (Int.ofNat 642901466819816622063129363), (Int.negOfNat 132555147586499398584864624), (Int.negOfNat 9811194745985269104436647), (Int.ofNat 1173145947433399102719622), (Int.ofNat 88216569034181397747500), (Int.negOfNat 6873103294531562591140), (Int.negOfNat 524926358234071673530), (Int.ofNat 28477133293568478882), (Int.ofNat 2245606255610326186), (Int.negOfNat 120978679382156797), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-1522004461523138905276648116093159/2251799813685248000000000000000000), (-90523490663930275134231356601171/2251799813685248000000000000000000), (10459706659003748433748708181617/2251799813685248000000000000000000), (179818344127071432925639908379/2251799813685248000000000000000000), (-300449307904140633214354436353/2251799813685248000000000000000000), (-241046935497267834201538323/28147497671065600000000000000000), (1784150320828473318211827299/450359962737049600000000000000000), (642901466819816622063129363/2251799813685248000000000000000000), (-8284696724156212411554039/140737488355328000000000000000000), (-9811194745985269104436647/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial153.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial153.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial153.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial153 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 1664582726451003416048578916350902), (Int.negOfNat 55834652351900891637136192578231), (Int.ofNat 5090857122528475662016988969216), (Int.negOfNat 1477222208670144351405529328538), (Int.ofNat 52415080981447141986133047582), (Int.ofNat 73838991328774210359449212134), (Int.ofNat 1233056313797285446554111735), (Int.negOfNat 1515065626399612965278895453), (Int.negOfNat 50646320510162444771763422), (Int.ofNat 17332180549527678985608797), (Int.ofNat 709482477595901442697860), (Int.negOfNat 125629738475357851727978), (Int.negOfNat 5666031560359300508342), (Int.ofNat 625509538268949498426), (Int.ofNat 30017816412968358258), (Int.negOfNat 2224378049307751030), (Int.negOfNat 96144375566518227), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-832291363225501708024289458175451/1125899906842624000000000000000000), (-55834652351900891637136192578231/2251799813685248000000000000000000), (19886160634876858054753863161/8796093022208000000000000000000), (-738611104335072175702764664269/1125899906842624000000000000000000), (26207540490723570993066523791/1125899906842624000000000000000000), (36919495664387105179724606067/1125899906842624000000000000000000), (246611262759457089310822347/450359962737049600000000000000000), (-1515065626399612965278895453/2251799813685248000000000000000000), (-25323160255081222385881711/1125899906842624000000000000000000), (17332180549527678985608797/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial153.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial153.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial153.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial153 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 1764623543948723846486226606989620), (Int.negOfNat 46065305213717446933836717142510), (Int.ofNat 2663884495959911635454601184187), (Int.ofNat 1252083554683466262395968911930), (Int.ofNat 457492855631299164308134826888), (Int.negOfNat 24716596170548011646095182390), (Int.negOfNat 13657762088204460884674016767), (Int.ofNat 122155935165112937435899831), (Int.ofNat 207679172589801838153046606), (Int.ofNat 2132011393618934954971077), (Int.negOfNat 1898565921496668341798590), (Int.negOfNat 38923637228540964775106), (Int.ofNat 11435748767286441096634), (Int.ofNat 301339290325821735540), (Int.negOfNat 48735602277010101720), (Int.negOfNat 1489058255636479466), (Int.ofNat 197765372077461271), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-88231177197436192324311330349481/112589990684262400000000000000000), (-4606530521371744693383671714251/225179981368524800000000000000000), (2663884495959911635454601184187/2251799813685248000000000000000000), (125208355468346626239596891193/225179981368524800000000000000000), (57186606953912395538516853361/281474976710656000000000000000000), (-2471659617054801164609518239/225179981368524800000000000000000), (-13657762088204460884674016767/2251799813685248000000000000000000), (122155935165112937435899831/2251799813685248000000000000000000), (103839586294900919076523303/1125899906842624000000000000000000), (2132011393618934954971077/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial153.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial153.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial153.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial153 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 1830359172069048836540682194448690), (Int.negOfNat 10082177572393988074773705337726), (Int.ofNat 16342932323730067428050409852045), (Int.ofNat 2160682757435901634814593926802), (Int.negOfNat 359392349131491848192470452663), (Int.negOfNat 96265455152196566409059816376), (Int.ofNat 6493237159283930865442376019), (Int.ofNat 2024008134007373537290039739), (Int.negOfNat 54087888790785838378219820), (Int.negOfNat 24167019236530415993589465), (Int.ofNat 120735322312071565237964), (Int.ofNat 179781094740705646779692), (Int.ofNat 1227738507092775841276), (Int.negOfNat 908987958969248875270), (Int.negOfNat 12307727937620737166), (Int.ofNat 3383282658094788506), (Int.ofNat 55561571329880195), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-183035917206904883654068219444869/225179981368524800000000000000000), (-5041088786196994037386852668863/1125899906842624000000000000000000), (3268586464746013485610081970409/450359962737049600000000000000000), (1080341378717950817407296963401/1125899906842624000000000000000000), (-359392349131491848192470452663/2251799813685248000000000000000000), (-12033181894024570801132477047/281474976710656000000000000000000), (6493237159283930865442376019/2251799813685248000000000000000000), (2024008134007373537290039739/2251799813685248000000000000000000), (-2704394439539291918910991/112589990684262400000000000000000), (-4833403847306083198717893/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial153.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial153.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial153.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial153 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 1776048198490177517436530223361206), (Int.ofNat 64060967994958810035964291908663), (Int.ofNat 15696988915049053194495231223548), (Int.negOfNat 2610241498444810050976690176984), (Int.negOfNat 514713958969170556160555548372), (Int.ofNat 84830161433924311688475692592), (Int.ofNat 15467027451331274263063965483), (Int.negOfNat 1324803403431910206464649681), (Int.negOfNat 257318866526204032780984296), (Int.ofNat 9864377183246518806757755), (Int.ofNat 2449132421731949307827968), (Int.negOfNat 36893958369517739880576), (Int.negOfNat 14961298457761270344964), (Int.ofNat 42149254902115077838), (Int.ofNat 63974509274478948046), (Int.ofNat 274731373023772074), (Int.negOfNat 238965007204417671), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-888024099245088758718265111680603/1125899906842624000000000000000000), (64060967994958810035964291908663/2251799813685248000000000000000000), (3924247228762263298623807805887/562949953421312000000000000000000), (-326280187305601256372086272123/281474976710656000000000000000000), (-128678489742292639040138887093/562949953421312000000000000000000), (5301885089620269480529730787/140737488355328000000000000000000), (15467027451331274263063965483/2251799813685248000000000000000000), (-1324803403431910206464649681/2251799813685248000000000000000000), (-32164858315775504097623037/281474976710656000000000000000000), (1972875436649303761351551/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial153.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial153.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial153.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial153 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 1610779232688772421655517715490060), (Int.ofNat 87988748113223902375128562811511), (Int.negOfNat 3098829426508659639762151977928), (Int.negOfNat 1975561979592351285777240018151), (Int.ofNat 671782834770947865541031485775), (Int.ofNat 80979565276446257210477978652), (Int.negOfNat 18414610865045559424667333869), (Int.negOfNat 2212204358925588668629872697), (Int.ofNat 207498161531588618308150902), (Int.ofNat 28776498623920143138737197), (Int.negOfNat 1266761789445046425092338), (Int.negOfNat 218182945973215338523690), (Int.ofNat 4743512854878841733010), (Int.ofNat 1104730985811451416264), (Int.negOfNat 10927234804976557460), (Int.negOfNat 4155108549407968758), (Int.ofNat 5621050470236037), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-80538961634438621082775885774503/112589990684262400000000000000000), (87988748113223902375128562811511/2251799813685248000000000000000000), (-387353678313582454970268997241/281474976710656000000000000000000), (-1975561979592351285777240018151/2251799813685248000000000000000000), (26871313390837914621641259431/90071992547409920000000000000000), (20244891319111564302619494663/562949953421312000000000000000000), (-18414610865045559424667333869/2251799813685248000000000000000000), (-2212204358925588668629872697/2251799813685248000000000000000000), (103749080765794309154075451/1125899906842624000000000000000000), (28776498623920143138737197/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial153.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial153.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial153.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial153 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 1451057238552293693301836194832251), (Int.ofNat 75605438636509054513892539638364), (Int.ofNat 2227035209878455259721736934202), (Int.ofNat 2951418981320761311775818556761), (Int.ofNat 80451189959565175550196394291), (Int.negOfNat 190693329052175942232288786046), (Int.negOfNat 13785181770527856517004642403), (Int.ofNat 3113769033536139944322560027), (Int.ofNat 287228494933629781335320706), (Int.negOfNat 25495065180766625458868651), (Int.negOfNat 2820500360345545491260952), (Int.ofNat 129838845343995829960634), (Int.ofNat 17154217722340037892638), (Int.negOfNat 456015427446774647710), (Int.negOfNat 72806804292187039166), (Int.ofNat 1166810333677513886), (Int.ofNat 249573331431315955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-1451057238552293693301836194832251/2251799813685248000000000000000000), (18901359659127263628473134909591/562949953421312000000000000000000), (1113517604939227629860868467101/1125899906842624000000000000000000), (2951418981320761311775818556761/2251799813685248000000000000000000), (80451189959565175550196394291/2251799813685248000000000000000000), (-95346664526087971116144393023/1125899906842624000000000000000000), (-13785181770527856517004642403/2251799813685248000000000000000000), (3113769033536139944322560027/2251799813685248000000000000000000), (143614247466814890667660353/1125899906842624000000000000000000), (-25495065180766625458868651/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial153.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial153.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial153.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial153 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 1272567605149387129623600608386521), (Int.ofNat 106220584876770181460059541112764), (Int.ofNat 5764377591869679339710528104402), (Int.negOfNat 4153062010220765597102739711188), (Int.negOfNat 1593323941223178105837446229682), (Int.negOfNat 34664403202632079864613245508), (Int.ofNat 38150170711078809824595525701), (Int.ofNat 2371855481139158158408755683), (Int.negOfNat 403242573192263006351592168), (Int.negOfNat 32350316355814350201388199), (Int.ofNat 2573101104088688769508358), (Int.ofNat 240925804179933463598552), (Int.negOfNat 11307487814015780074568), (Int.negOfNat 1195168788839212942774), (Int.ofNat 36672159890034147622), (Int.ofNat 4412081882552819678), (Int.negOfNat 82407743165540511), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-1272567605149387129623600608386521/2251799813685248000000000000000000), (26555146219192545365014885278191/562949953421312000000000000000000), (2882188795934839669855264052201/1125899906842624000000000000000000), (-1038265502555191399275684927797/562949953421312000000000000000000), (-796661970611589052918723114841/1125899906842624000000000000000000), (-8666100800658019966153311377/562949953421312000000000000000000), (38150170711078809824595525701/2251799813685248000000000000000000), (2371855481139158158408755683/2251799813685248000000000000000000), (-50405321649032875793949021/281474976710656000000000000000000), (-32350316355814350201388199/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial153.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial153.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial153.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial153 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 1094267377204059736783936170319105), (Int.ofNat 33597353006433591146556775250443), (Int.negOfNat 50253185743457109904138520012259), (Int.negOfNat 11702378501883382783051274131408), (Int.ofNat 474031311138847936276051161211), (Int.ofNat 402885595002337763020530709648), (Int.ofNat 15768164980129687762403024151), (Int.negOfNat 5391515312208225061758765265), (Int.negOfNat 332952869213211852956836614), (Int.ofNat 42080775136277549754457899), (Int.ofNat 3084494639143854361004318), (Int.negOfNat 223009602498187761806766), (Int.negOfNat 17956934660868215593308), (Int.ofNat 869160712855234936808), (Int.ofNat 74115839639262144062), (Int.negOfNat 2539183289320783184), (Int.negOfNat 234586091426446081), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-218853475440811947356787234063821/450359962737049600000000000000000), (33597353006433591146556775250443/2251799813685248000000000000000000), (-50253185743457109904138520012259/2251799813685248000000000000000000), (-731398656367711423940704633213/140737488355328000000000000000000), (474031311138847936276051161211/2251799813685248000000000000000000), (25180349687646110188783169353/140737488355328000000000000000000), (15768164980129687762403024151/2251799813685248000000000000000000), (-1078303062441645012351753053/450359962737049600000000000000000), (-166476434606605926478418307/1125899906842624000000000000000000), (42080775136277549754457899/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial153.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial153.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial153.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial153 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 1300969607659308841444961251244385), (Int.negOfNat 260063089903511515472431487585413), (Int.negOfNat 77073136094708023433799077252617), (Int.ofNat 7374767490459789261406626708039), (Int.ofNat 3766260773062118797738036175424), (Int.ofNat 91699663671604989525553695919), (Int.negOfNat 62480986432152667611292454109), (Int.negOfNat 3208102194921040509469785335), (Int.ofNat 590341527145476596142157508), (Int.ofNat 36670530271620153930767335), (Int.negOfNat 3735366982854472626228694), (Int.negOfNat 249454831388487753202464), (Int.ofNat 17173612057427530129238), (Int.ofNat 1174104053641010511932), (Int.negOfNat 60270956770255839336), (Int.negOfNat 4147152437725727522), (Int.ofNat 159194435860844985), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-260193921531861768288992250248877/450359962737049600000000000000000), (-260063089903511515472431487585413/2251799813685248000000000000000000), (-77073136094708023433799077252617/2251799813685248000000000000000000), (7374767490459789261406626708039/2251799813685248000000000000000000), (58847824579095606214656815241/35184372088832000000000000000000), (91699663671604989525553695919/2251799813685248000000000000000000), (-62480986432152667611292454109/2251799813685248000000000000000000), (-641620438984208101893957067/450359962737049600000000000000000), (147585381786369149035539377/562949953421312000000000000000000), (7334106054324030786153467/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial153.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial153.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial153.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial153 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 2011439404835652213594227225697977), (Int.negOfNat 364768145319751940110052629929380), (Int.ofNat 48928555359698411708082501886700), (Int.ofNat 30568692225972767360309826681223), (Int.ofNat 786961508074624457184305894980), (Int.negOfNat 624594788765551032515630547550), (Int.negOfNat 31654186724145795846191647645), (Int.ofNat 7146930250335001283042481477), (Int.ofNat 418822488032172659658913412), (Int.negOfNat 54137755362502610770584985), (Int.negOfNat 3255858006747346472070168), (Int.ofNat 293951596561820982614472), (Int.ofNat 17298926238120655578516), (Int.negOfNat 1201554653484117827056), (Int.negOfNat 67687736455441695324), (Int.ofNat 3760450183134717006), (Int.ofNat 219598851421576207), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-2011439404835652213594227225697977/2251799813685248000000000000000000), (-18238407265987597005502631496469/112589990684262400000000000000000), (489285553596984117080825018867/22517998136852480000000000000000), (30568692225972767360309826681223/2251799813685248000000000000000000), (39348075403731222859215294749/112589990684262400000000000000000), (-12491895775311020650312610951/45035996273704960000000000000000), (-6330837344829159169238329529/450359962737049600000000000000000), (7146930250335001283042481477/2251799813685248000000000000000000), (104705622008043164914728353/562949953421312000000000000000000), (-10827551072500522154116997/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial153.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial153.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial153.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial153 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 2309141818136694325540577799753582), (Int.ofNat 170400925234715891195846427793446), (Int.ofNat 198938723040679401893312850731880), (Int.ofNat 11241649819234602449966221541433), (Int.negOfNat 5135946676571178951341724904415), (Int.negOfNat 341874034794796353737288850721), (Int.ofNat 73054733675517666374091033167), (Int.ofNat 4762712745639632064065641935), (Int.negOfNat 675491950288003960833202874), (Int.negOfNat 40765836865015904860954327), (Int.ofNat 4388890301157220465207094), (Int.ofNat 240061664197757722116616), (Int.negOfNat 21054913617005081577380), (Int.negOfNat 1037510087366094466776), (Int.ofNat 77442300467661171576), (Int.ofNat 3416711070522887246), (Int.negOfNat 230985381887859501), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-1154570909068347162770288899876791/1125899906842624000000000000000000), (85200462617357945597923213896723/1125899906842624000000000000000000), (4973468076016985047332821268297/56294995342131200000000000000000), (11241649819234602449966221541433/2251799813685248000000000000000000), (-1027189335314235790268344980883/450359962737049600000000000000000), (-341874034794796353737288850721/2251799813685248000000000000000000), (73054733675517666374091033167/2251799813685248000000000000000000), (952542549127926412813128387/450359962737049600000000000000000), (-337745975144001980416601437/1125899906842624000000000000000000), (-40765836865015904860954327/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial153.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial153.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial153.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial153.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial153 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial153 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial153 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 2521219876528921393215127068502295), (Int.negOfNat 225880639522183525704047696918997), (Int.ofNat 202489595932952381791406888393706), (Int.negOfNat 10932013177223797423637141531117), (Int.negOfNat 5145855526794147900106396520342), (Int.ofNat 341355602870688517124061158407), (Int.ofNat 73065794089782758164388197609), (Int.negOfNat 4762299401448109264663178575), (Int.negOfNat 675498564115354360932199674), (Int.ofNat 40765644614115998115493527), (Int.ofNat 4388892679518868796078774), (Int.negOfNat 240061664197757722116616), (Int.negOfNat 21054913617005081577380), (Int.ofNat 1037510087366094466776), (Int.ofNat 77442300467661171576), (Int.negOfNat 3416711070522887246), (Int.negOfNat 230985381887859501), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-504243975305784278643025413700459/450359962737049600000000000000000), (-225880639522183525704047696918997/2251799813685248000000000000000000), (101244797966476190895703444196853/1125899906842624000000000000000000), (-10932013177223797423637141531117/2251799813685248000000000000000000), (-2572927763397073950053198260171/1125899906842624000000000000000000), (341355602870688517124061158407/2251799813685248000000000000000000), (73065794089782758164388197609/2251799813685248000000000000000000), (-190491976057924370586527143/90071992547409920000000000000000), (-337749282057677180466099837/1125899906842624000000000000000000), (40765644614115998115493527/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial153.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial153.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial153.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 2317970679537135717676170261426761), (Int.ofNat 326851306119936955253706519070290), (Int.ofNat 54060880703602025407189037538242), (Int.negOfNat 30357075368957408753281728555078), (Int.ofNat 772639552693931507411169882527), (Int.ofNat 624240473676464307854961427193), (Int.negOfNat 31638200332454311139658812445), (Int.negOfNat 7146647756069891095152091397), (Int.ofNat 418812928603920801775340932), (Int.ofNat 54137624156218344517497305), (Int.negOfNat 3255854439204873975762648), (Int.negOfNat 293951596561820982614472), (Int.ofNat 17298926238120655578516), (Int.ofNat 1201554653484117827056), (Int.negOfNat 67687736455441695324), (Int.negOfNat 3760450183134717006), (Int.ofNat 219598851421576207), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-2317970679537135717676170261426761/2251799813685248000000000000000000), (32685130611993695525370651907029/225179981368524800000000000000000), (27030440351801012703594518769121/1125899906842624000000000000000000), (-15178537684478704376640864277539/1125899906842624000000000000000000), (772639552693931507411169882527/2251799813685248000000000000000000), (624240473676464307854961427193/2251799813685248000000000000000000), (-6327640066490862227931762489/450359962737049600000000000000000), (-7146647756069891095152091397/2251799813685248000000000000000000), (104703232150980200443835233/562949953421312000000000000000000), (10827524831243668903499461/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial153.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial153.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial153.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 1661351757120062404695098001440993), (Int.ofNat 244731492455898973422126198436798), (Int.negOfNat 71039172868681628465200995688979), (Int.negOfNat 7289200641175387253472905162922), (Int.ofNat 3749422761770433509723030026988), (Int.negOfNat 91842930263307480268952167917), (Int.negOfNat 62462191579337083147658488779), (Int.ofNat 3208216420892318504299105975), (Int.ofNat 590330288197507408608033668), (Int.negOfNat 36670583388363633320234855), (Int.negOfNat 3735362622524784019630614), (Int.ofNat 249454831388487753202464), (Int.ofNat 17173612057427530129238), (Int.negOfNat 1174104053641010511932), (Int.negOfNat 60270956770255839336), (Int.ofNat 4147152437725727522), (Int.ofNat 159194435860844985), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-1661351757120062404695098001440993/2251799813685248000000000000000000), (122365746227949486711063099218399/1125899906842624000000000000000000), (-71039172868681628465200995688979/2251799813685248000000000000000000), (-3644600320587693626736452581461/1125899906842624000000000000000000), (937355690442608377430757506747/562949953421312000000000000000000), (-91842930263307480268952167917/2251799813685248000000000000000000), (-62462191579337083147658488779/2251799813685248000000000000000000), (128328656835692740171964239/90071992547409920000000000000000), (147582572049376852152008417/562949953421312000000000000000000), (-7334116677672726664046971/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial153.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial153.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial153.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 1460765111981782131038998610047912), (Int.negOfNat 24312924871611264821898954496279), (Int.negOfNat 44116827831733840681768815711553), (Int.ofNat 11650561379404068246255889220749), (Int.ofNat 456907563454662927039228584527), (Int.negOfNat 402798836373480921121620785311), (Int.ofNat 15787278776267607350895049713), (Int.ofNat 5391446139938045006686824145), (Int.negOfNat 332964298826506515015840134), (Int.negOfNat 42080743028395297287690219), (Int.ofNat 3084498999473542967602398), (Int.ofNat 223009602498187761806766), (Int.negOfNat 17956934660868215593308), (Int.negOfNat 869160712855234936808), (Int.ofNat 74115839639262144062), (Int.ofNat 2539183289320783184), (Int.negOfNat 234586091426446081), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-182595638997722766379874826255989/281474976710656000000000000000000), (-24312924871611264821898954496279/2251799813685248000000000000000000), (-44116827831733840681768815711553/2251799813685248000000000000000000), (11650561379404068246255889220749/2251799813685248000000000000000000), (456907563454662927039228584527/2251799813685248000000000000000000), (-402798836373480921121620785311/2251799813685248000000000000000000), (15787278776267607350895049713/2251799813685248000000000000000000), (1078289227987609001337364829/450359962737049600000000000000000), (-166482149413253257507920067/1125899906842624000000000000000000), (-42080743028395297287690219/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial153.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial153.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial153.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 1596635581153506434320932023235926), (Int.negOfNat 73549922548855597510118849662481), (Int.ofNat 11190324056992040046313273070928), (Int.ofNat 3970724478281730751676886962923), (Int.negOfNat 1608465257873059411413828737105), (Int.ofNat 34969695227992955038989635159), (Int.ofNat 38167071686709794372637442377), (Int.negOfNat 2372098889805333284809101923), (Int.negOfNat 403252679643693980335651048), (Int.ofNat 32350429724386253972938279), (Int.ofNat 2573104671631161265815878), (Int.negOfNat 240925804179933463598552), (Int.negOfNat 11307487814015780074568), (Int.ofNat 1195168788839212942774), (Int.ofNat 36672159890034147622), (Int.negOfNat 4412081882552819678), (Int.negOfNat 82407743165540511), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-798317790576753217160466011617963/1125899906842624000000000000000000), (-73549922548855597510118849662481/2251799813685248000000000000000000), (699395253562002502894579566933/140737488355328000000000000000000), (3970724478281730751676886962923/2251799813685248000000000000000000), (-321693051574611882282765747421/450359962737049600000000000000000), (34969695227992955038989635159/2251799813685248000000000000000000), (38167071686709794372637442377/2251799813685248000000000000000000), (-2372098889805333284809101923/2251799813685248000000000000000000), (-50406584955461747541956381/281474976710656000000000000000000), (32350429724386253972938279/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial153.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial153.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial153.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 1689770248036530967419956240167230), (Int.negOfNat 23876013731037237634601063703282), (Int.ofNat 6223863362864880187561087248188), (Int.negOfNat 3240124963810171644186173017269), (Int.ofNat 69297884072593590366831926228), (Int.ofNat 191176716279773512504618518187), (Int.negOfNat 13772732275326242158599919843), (Int.negOfNat 3114154436338624544589381467), (Int.ofNat 287221050265276897651817026), (Int.ofNat 25495244350677466384535211), (Int.negOfNat 2820497585590289105243992), (Int.negOfNat 129838845343995829960634), (Int.ofNat 17154217722340037892638), (Int.ofNat 456015427446774647710), (Int.negOfNat 72806804292187039166), (Int.negOfNat 1166810333677513886), (Int.ofNat 249573331431315955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-168977024803653096741995624016723/225179981368524800000000000000000), (-11938006865518618817300531851641/1125899906842624000000000000000000), (1555965840716220046890271812047/562949953421312000000000000000000), (-3240124963810171644186173017269/2251799813685248000000000000000000), (17324471018148397591707981557/562949953421312000000000000000000), (191176716279773512504618518187/2251799813685248000000000000000000), (-13772732275326242158599919843/2251799813685248000000000000000000), (-3114154436338624544589381467/2251799813685248000000000000000000), (143610525132638448825908513/1125899906842624000000000000000000), (25495244350677466384535211/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial153.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial153.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial153.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 1732517966488139589369474874656950), (Int.negOfNat 24052506749965102617833491706634), (Int.negOfNat 1060529127761570054069157565380), (Int.ofNat 1618728795916448333546987842809), (Int.ofNat 666094877759569448600014804199), (Int.negOfNat 80382111070812334213709133077), (Int.negOfNat 18408261878174541169610733869), (Int.ofNat 2211728010744820760271170297), (Int.ofNat 207494365270004274181804342), (Int.negOfNat 28776277039893240312525677), (Int.negOfNat 1266760203870614204511218), (Int.ofNat 218182945973215338523690), (Int.ofNat 4743512854878841733010), (Int.negOfNat 1104730985811451416264), (Int.negOfNat 10927234804976557460), (Int.ofNat 4155108549407968758), (Int.ofNat 5621050470236037), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-34650359329762791787389497493139/45035996273704960000000000000000), (-12026253374982551308916745853317/1125899906842624000000000000000000), (-53026456388078502703457878269/112589990684262400000000000000000), (1618728795916448333546987842809/2251799813685248000000000000000000), (666094877759569448600014804199/2251799813685248000000000000000000), (-80382111070812334213709133077/2251799813685248000000000000000000), (-18408261878174541169610733869/2251799813685248000000000000000000), (2211728010744820760271170297/2251799813685248000000000000000000), (103747182635002137090902171/1125899906842624000000000000000000), (-28776277039893240312525677/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial153.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial153.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial153.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 1764687458109659941548836202709047), (Int.ofNat 3613260301922025837179739141323), (Int.ofNat 15506773362510901634744352642066), (Int.ofNat 2232546316174396050342890385626), (Int.negOfNat 514183155000831072537054493998), (Int.negOfNat 84197777492672337912472678728), (Int.ofNat 15466434959426952589083077803), (Int.ofNat 1324299205825421167764010321), (Int.negOfNat 257318512546712039536249256), (Int.negOfNat 9864142518230550160751995), (Int.ofNat 2449132421731949307827968), (Int.ofNat 36893958369517739880576), (Int.negOfNat 14961298457761270344964), (Int.negOfNat 42149254902115077838), (Int.ofNat 63974509274478948046), (Int.negOfNat 274731373023772074), (Int.negOfNat 238965007204417671), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-1764687458109659941548836202709047/2251799813685248000000000000000000), (3613260301922025837179739141323/2251799813685248000000000000000000), (7753386681255450817372176321033/1125899906842624000000000000000000), (1116273158087198025171445192813/1125899906842624000000000000000000), (-257091577500415536268527246999/1125899906842624000000000000000000), (-10524722186584042239059084841/281474976710656000000000000000000), (15466434959426952589083077803/2251799813685248000000000000000000), (1324299205825421167764010321/2251799813685248000000000000000000), (-32164814068339004942031157/281474976710656000000000000000000), (-1972828503646110032150399/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial153.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial153.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial153.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 1687403771859788323604129585455435), (Int.ofNat 72530439176725732238501260276141), (Int.ofNat 13949396381102906678418453456129), (Int.negOfNat 2509211409229632265621156823516), (Int.negOfNat 352713093108517151295965857842), (Int.ofNat 96849004884452219890583458223), (Int.ofNat 6485781668618355624594029617), (Int.negOfNat 2024473396248104967400696379), (Int.negOfNat 54083430551876042159255660), (Int.ofNat 24167235667440414102912345), (Int.ofNat 120733736737639344656844), (Int.negOfNat 179781094740705646779692), (Int.ofNat 1227738507092775841276), (Int.ofNat 908987958969248875270), (Int.negOfNat 12307727937620737166), (Int.negOfNat 3383282658094788506), (Int.ofNat 55561571329880195), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-337480754371957664720825917091087/450359962737049600000000000000000), (72530439176725732238501260276141/2251799813685248000000000000000000), (13949396381102906678418453456129/2251799813685248000000000000000000), (-627302852307408066405289205879/562949953421312000000000000000000), (-176356546554258575647982928921/1125899906842624000000000000000000), (96849004884452219890583458223/2251799813685248000000000000000000), (6485781668618355624594029617/2251799813685248000000000000000000), (-2024473396248104967400696379/2251799813685248000000000000000000), (-2704171527593802107962783/112589990684262400000000000000000), (4833447133488082820582469/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial153.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial153.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial153.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 1509008987282586707395088180321247), (Int.ofNat 95015864560109433208829439020313), (Int.negOfNat 1615930243105456427247451961775), (Int.negOfNat 1525280470272507790273580727917), (Int.ofNat 469435846696881566159004185073), (Int.ofNat 25174016202312260705756189120), (Int.negOfNat 13671093042286733037417294207), (Int.negOfNat 122520634725842425519892151), (Int.ofNat 207687144065259827124627406), (Int.negOfNat 2131841737154687352791237), (Int.negOfNat 1898568696251924727815550), (Int.ofNat 38923637228540964775106), (Int.ofNat 11435748767286441096634), (Int.negOfNat 301339290325821735540), (Int.negOfNat 48735602277010101720), (Int.ofNat 1489058255636479466), (Int.ofNat 197765372077461271), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-1509008987282586707395088180321247/2251799813685248000000000000000000), (95015864560109433208829439020313/2251799813685248000000000000000000), (-64637209724218257089898078471/90071992547409920000000000000000), (-1525280470272507790273580727917/2251799813685248000000000000000000), (469435846696881566159004185073/2251799813685248000000000000000000), (78668800632225814705488091/7036874417766400000000000000000), (-13671093042286733037417294207/2251799813685248000000000000000000), (-122520634725842425519892151/2251799813685248000000000000000000), (103843572032629913562313703/1125899906842624000000000000000000), (-2131841737154687352791237/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial153.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial153.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial153.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 1330167057813164388889099049795047), (Int.ofNat 84803644680935354139049068726218), (Int.negOfNat 508343198015726232175259608753), (Int.ofNat 1315543987673129703922927374531), (Int.ofNat 68039869317467185388642329333), (Int.negOfNat 73568289674457874375665476919), (Int.ofNat 1215615679614620165470010295), (Int.ofNat 1514849796818718275611405213), (Int.negOfNat 50635891394334513899446622), (Int.negOfNat 17332080261944841033852957), (Int.ofNat 709478513659820891245060), (Int.ofNat 125629738475357851727978), (Int.negOfNat 5666031560359300508342), (Int.negOfNat 625509538268949498426), (Int.ofNat 30017816412968358258), (Int.ofNat 2224378049307751030), (Int.negOfNat 96144375566518227), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-1330167057813164388889099049795047/2251799813685248000000000000000000), (42401822340467677069524534363109/1125899906842624000000000000000000), (-508343198015726232175259608753/2251799813685248000000000000000000), (1315543987673129703922927374531/2251799813685248000000000000000000), (68039869317467185388642329333/2251799813685248000000000000000000), (-73568289674457874375665476919/2251799813685248000000000000000000), (243123135922924033094002059/450359962737049600000000000000000), (1514849796818718275611405213/2251799813685248000000000000000000), (-25317945697167256949723311/1125899906842624000000000000000000), (-17332080261944841033852957/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial153.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial153.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial153.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 1153083517320653230305440394473938), (Int.ofNat 95673758014908978114232479965814), (Int.ofNat 4282776381061767074687643118191), (Int.negOfNat 208562390633633942788747135232), (Int.negOfNat 283212341439532785709621842838), (Int.ofNat 19331881673582988776173213786), (Int.ofNat 8901511431400501110933000653), (Int.negOfNat 642939838117469968181378643), (Int.negOfNat 132543642262025597993112624), (Int.ofNat 9811212583697631585974247), (Int.ofNat 1173141983497318551266822), (Int.negOfNat 88216569034181397747500), (Int.negOfNat 6873103294531562591140), (Int.ofNat 524926358234071673530), (Int.ofNat 28477133293568478882), (Int.negOfNat 2245606255610326186), (Int.negOfNat 120978679382156797), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-576541758660326615152720197236969/1125899906842624000000000000000000), (47836879007454489057116239982907/1125899906842624000000000000000000), (4282776381061767074687643118191/2251799813685248000000000000000000), (-814696838412632589018543497/8796093022208000000000000000000), (-141606170719766392854810921419/1125899906842624000000000000000000), (9665940836791494388086606893/1125899906842624000000000000000000), (8901511431400501110933000653/2251799813685248000000000000000000), (-642939838117469968181378643/2251799813685248000000000000000000), (-8283977641376599874569539/140737488355328000000000000000000), (9811212583697631585974247/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial153.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial153.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial153.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 949726682370465021566494742034350), (Int.ofNat 104098678507888180275443200907785), (Int.negOfNat 696486200201619377865599723462), (Int.negOfNat 807873828310549810449445638254), (Int.ofNat 166668538389924406323746656819), (Int.ofNat 38892853849851769435943573965), (Int.negOfNat 5989206099488080668208536943), (Int.negOfNat 798389323874306119343097527), (Int.ofNat 109432812297195826973102958), (Int.ofNat 8813369448047742268635621), (Int.negOfNat 1162958349197855908957394), (Int.negOfNat 60967086445022675169838), (Int.ofNat 8037111630840220851452), (Int.ofNat 288815012938749806232), (Int.negOfNat 38720811898660468214), (Int.negOfNat 934812324847131896), (Int.ofNat 111131615571388101), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-18994533647409300431329894840687/45035996273704960000000000000000), (20819735701577636055088640181557/450359962737049600000000000000000), (-348243100100809688932799861731/1125899906842624000000000000000000), (-403936914155274905224722819127/1125899906842624000000000000000000), (166668538389924406323746656819/2251799813685248000000000000000000), (7778570769970353887188714793/450359962737049600000000000000000), (-5989206099488080668208536943/2251799813685248000000000000000000), (-798389323874306119343097527/2251799813685248000000000000000000), (54716406148597913486551479/1125899906842624000000000000000000), (8813369448047742268635621/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial153.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial153.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial153.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 747321249729629050400420601733896), (Int.ofNat 98681395694453792587976791273381), (Int.negOfNat 184007331541865906907529697648), (Int.ofNat 899823239499328525719491021128), (Int.ofNat 113673067764863252159969720402), (Int.negOfNat 43561237973505135626388181286), (Int.negOfNat 3289080202668392229407424157), (Int.ofNat 1000816549590957826038846731), (Int.ofNat 45982203971718879309524604), (Int.negOfNat 13011868624901662979802619), (Int.negOfNat 367213277092138118365938), (Int.ofNat 106909197306202845039796), (Int.ofNat 1868393230391640205810), (Int.negOfNat 601587495035633987556), (Int.negOfNat 6654089869431799764), (Int.ofNat 2500234464285389662), (Int.ofNat 44191986686852323), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-93415156216203631300052575216737/281474976710656000000000000000000), (98681395694453792587976791273381/2251799813685248000000000000000000), (-11500458221366619181720606103/140737488355328000000000000000000), (112477904937416065714936377641/281474976710656000000000000000000), (56836533882431626079984860201/1125899906842624000000000000000000), (-21780618986752567813194090643/1125899906842624000000000000000000), (-3289080202668392229407424157/2251799813685248000000000000000000), (1000816549590957826038846731/2251799813685248000000000000000000), (11495550992929719827381151/562949953421312000000000000000000), (-13011868624901662979802619/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial153.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial153.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial153.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 543148533902910822454329233193176), (Int.ofNat 108729191076082694012966196980804), (Int.ofNat 4362607768342071426386080754027), (Int.ofNat 112320536906691181902332299114), (Int.negOfNat 240421960965418545250007136726), (Int.negOfNat 4401488661853898925650793887), (Int.ofNat 7454740164688778336039691841), (Int.ofNat 57226721803849457867551095), (Int.negOfNat 122443103264914925275082440), (Int.negOfNat 79174490359016962753779), (Int.ofNat 1224047650565879381536144), (Int.negOfNat 4678937958908374119940), (Int.negOfNat 8147634022345407674360), (Int.ofNat 53133608564174618868), (Int.ofNat 38498097471159849340), (Int.negOfNat 403477204515750082), (Int.negOfNat 126118855576257975), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-67893566737863852806791154149147/281474976710656000000000000000000), (27182297769020673503241549245201/562949953421312000000000000000000), (4362607768342071426386080754027/2251799813685248000000000000000000), (56160268453345590951166149557/1125899906842624000000000000000000), (-120210980482709272625003568363/1125899906842624000000000000000000), (-4401488661853898925650793887/2251799813685248000000000000000000), (7454740164688778336039691841/2251799813685248000000000000000000), (11445344360769891573510219/450359962737049600000000000000000), (-3061077581622873131877061/56294995342131200000000000000000), (-79174490359016962753779/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial153.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial153.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial153.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 310874501458551245339629678105120), (Int.ofNat 120819251561728005761057409644780), (Int.ofNat 535536895865552756146253103569), (Int.negOfNat 964423903554056257054343043583), (Int.ofNat 56693732095368110386898537985), (Int.ofNat 43809589528527568320611795902), (Int.negOfNat 1909677970613462200171918629), (Int.negOfNat 947880233564145524683294163), (Int.ofNat 34673333753191191378409266), (Int.ofNat 11825760408166955356734495), (Int.negOfNat 384009281083538825308922), (Int.negOfNat 94912334320270854297488), (Int.ofNat 2803521422430168740584), (Int.ofNat 527432273690198148700), (Int.negOfNat 14341684940825054164), (Int.negOfNat 2196552026065474938), (Int.ofNat 37590452676742109), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1942965634115945283372685488157/14073748835532800000000000000000), (6040962578086400288052870482239/112589990684262400000000000000000), (535536895865552756146253103569/2251799813685248000000000000000000), (-964423903554056257054343043583/2251799813685248000000000000000000), (11338746419073622077379707597/450359962737049600000000000000000), (21904794764263784160305897951/1125899906842624000000000000000000), (-1909677970613462200171918629/2251799813685248000000000000000000), (-947880233564145524683294163/2251799813685248000000000000000000), (17336666876595595689204633/1125899906842624000000000000000000), (2365152081633391071346899/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial153.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial153.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial153.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 72729424402325302340835894489730), (Int.ofNat 115975782046834037299595881114371), (Int.negOfNat 1371090159913696969691233829023), (Int.ofNat 521406423702357787255498842019), (Int.ofNat 192676066541701631135979654536), (Int.negOfNat 24819790988784621928320656347), (Int.negOfNat 5777412948731360361672938651), (Int.ofNat 559601882612572777486324121), (Int.ofNat 92788958274571727837008706), (Int.negOfNat 7256128168512356126458841), (Int.negOfNat 918718547317972015806170), (Int.ofNat 60324005860728807667988), (Int.ofNat 6115015170318366837984), (Int.negOfNat 345683063246378397404), (Int.negOfNat 29071656421206300244), (Int.ofNat 1483498639407401390), (Int.ofNat 84919220449301575), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-7272942440232530234083589448973/225179981368524800000000000000000), (115975782046834037299595881114371/2251799813685248000000000000000000), (-1371090159913696969691233829023/2251799813685248000000000000000000), (521406423702357787255498842019/2251799813685248000000000000000000), (24084508317712703891997456817/281474976710656000000000000000000), (-24819790988784621928320656347/2251799813685248000000000000000000), (-5777412948731360361672938651/2251799813685248000000000000000000), (559601882612572777486324121/2251799813685248000000000000000000), (46394479137285863918504353/1125899906842624000000000000000000), (-7256128168512356126458841/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial153.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial153.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial153.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 159918732210663914415857035070219), (Int.ofNat 120144190072300341943010893261523), (Int.ofNat 3509769377547672004417733103765), (Int.ofNat 575288765643761912383675154852), (Int.negOfNat 179987354923806451727239268291), (Int.negOfNat 25344471004304963027128489914), (Int.ofNat 5645980033924916527859059999), (Int.ofNat 543019988760184893843163351), (Int.negOfNat 93488832361725131737958496), (Int.negOfNat 6833360624794802614889895), (Int.ofNat 944036367714904330887880), (Int.ofNat 55991554093600387942416), (Int.negOfNat 6356471360530406199736), (Int.negOfNat 319314278578758813736), (Int.ofNat 30275237683867459008), (Int.ofNat 1423391600117790190), (Int.negOfNat 98773074476858341), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(159918732210663914415857035070219/2251799813685248000000000000000000), (120144190072300341943010893261523/2251799813685248000000000000000000), (701953875509534400883546620753/450359962737049600000000000000000), (143822191410940478095918788713/562949953421312000000000000000000), (-179987354923806451727239268291/2251799813685248000000000000000000), (-12672235502152481513564244957/1125899906842624000000000000000000), (5645980033924916527859059999/2251799813685248000000000000000000), (543019988760184893843163351/2251799813685248000000000000000000), (-2921526011303910366811203/70368744177664000000000000000000), (-1366672124958960522977979/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial153.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial153.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial153.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 415562149941563926118639437039393), (Int.ofNat 134520698895306102900230176308938), (Int.ofNat 2147155908775210573418874137214), (Int.negOfNat 859128565478987713378612253576), (Int.negOfNat 60722832208913030290253491837), (Int.ofNat 40914682846401020502382889032), (Int.ofNat 1764943948618992483691948765), (Int.negOfNat 916245067409390365058074929), (Int.negOfNat 29615925099706739684013316), (Int.ofNat 11719041472922473592321501), (Int.ofNat 319013095545236960865042), (Int.negOfNat 95786175222367644160592), (Int.negOfNat 2339330312558141678494), (Int.ofNat 538693395693046224236), (Int.ofNat 12124706032258304812), (Int.negOfNat 2213940006610241666), (Int.negOfNat 13128274422287059), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(415562149941563926118639437039393/2251799813685248000000000000000000), (67260349447653051450115088154469/1125899906842624000000000000000000), (1073577954387605286709437068607/1125899906842624000000000000000000), (-107391070684873464172326531697/281474976710656000000000000000000), (-60722832208913030290253491837/2251799813685248000000000000000000), (5114335355800127562797861129/281474976710656000000000000000000), (352988789723798496738389753/450359962737049600000000000000000), (-916245067409390365058074929/2251799813685248000000000000000000), (-7403981274926684921003329/562949953421312000000000000000000), (11719041472922473592321501/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial153.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial153.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial153.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 686651068353216455068670970959273), (Int.ofNat 134055415608459050062377097075232), (Int.negOfNat 1382081102576445721839627981680), (Int.ofNat 71652899143595291218036240009), (Int.ofNat 212001822961761248735613001276), (Int.negOfNat 4826749643790450512720658222), (Int.negOfNat 6864960406009061420639073065), (Int.ofNat 99423330528801537216840005), (Int.ofNat 116436873808413728098671546), (Int.negOfNat 875810234474471513493619), (Int.negOfNat 1195766704337399363310538), (Int.ofNat 2663899916562204602002), (Int.ofNat 8130504982704416019792), (Int.ofNat 12490531013377365580), (Int.negOfNat 38903308203674637278), (Int.negOfNat 202124706303856368), (Int.ofNat 113760314481728215), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(686651068353216455068670970959273/2251799813685248000000000000000000), (4189231737764345314449284283601/70368744177664000000000000000000), (-17276013782205571522995349771/28147497671065600000000000000000), (71652899143595291218036240009/2251799813685248000000000000000000), (53000455740440312183903250319/562949953421312000000000000000000), (-2413374821895225256360329111/1125899906842624000000000000000000), (-1372992081201812284127814613/450359962737049600000000000000000), (19884666105760307443368001/450359962737049600000000000000000), (58218436904206864049335773/1125899906842624000000000000000000), (-875810234474471513493619/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial153.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial153.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial153.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 952645913439800868494736682804507), (Int.ofNat 134622630835248615615869305999847), (Int.ofNat 2360418114022266488789127249579), (Int.ofNat 718463796174284955845959155501), (Int.negOfNat 108409726860833068648953271507), (Int.negOfNat 37231306163404412565396899584), (Int.ofNat 3455310464342983513001812773), (Int.ofNat 893297558493770211343533313), (Int.negOfNat 53306582764435839818818500), (Int.negOfNat 12100363742594533823204061), (Int.ofNat 467303126672714334221142), (Int.ofNat 103179362318132713480984), (Int.negOfNat 2569110334084312007988), (Int.negOfNat 596265436129546963466), (Int.ofNat 9433278698501540962), (Int.ofNat 2478869451437333822), (Int.negOfNat 63658418273017415), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(952645913439800868494736682804507/2251799813685248000000000000000000), (134622630835248615615869305999847/2251799813685248000000000000000000), (2360418114022266488789127249579/2251799813685248000000000000000000), (718463796174284955845959155501/2251799813685248000000000000000000), (-108409726860833068648953271507/2251799813685248000000000000000000), (-145434789700798486583581639/8796093022208000000000000000000), (3455310464342983513001812773/2251799813685248000000000000000000), (893297558493770211343533313/2251799813685248000000000000000000), (-106613165528871679637637/4503599627370496000000000000000), (-12100363742594533823204061/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial153.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial153.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial153.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 1234470915250016702921460389795250), (Int.ofNat 147222866416896638150578098634423), (Int.ofNat 2377175106388365606491043709040), (Int.negOfNat 734463379903706369436921346890), (Int.negOfNat 121661587634725273183077380662), (Int.ofNat 37372868497228089955161976934), (Int.ofNat 4685563908211096575059034969), (Int.negOfNat 831317473091961394967103679), (Int.negOfNat 92021837732042002231000514), (Int.ofNat 9919750126401493064161203), (Int.ofNat 1053630948786539661839100), (Int.negOfNat 71928638052328216222838), (Int.negOfNat 7694950405257187658134), (Int.ofNat 346640529159832720706), (Int.ofNat 38621848666995449642), (Int.negOfNat 1170248249339412930), (Int.negOfNat 128747554486598089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(4937883661000066811685841559181/9007199254740992000000000000000), (147222866416896638150578098634423/2251799813685248000000000000000000), (29714688829854570081138046363/28147497671065600000000000000000), (-73446337990370636943692134689/225179981368524800000000000000000), (-60830793817362636591538690331/1125899906842624000000000000000000), (18686434248614044977580988467/1125899906842624000000000000000000), (4685563908211096575059034969/2251799813685248000000000000000000), (-831317473091961394967103679/2251799813685248000000000000000000), (-46010918866021001115500257/1125899906842624000000000000000000), (9919750126401493064161203/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial153.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial153.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial153.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 1531974880148574495431066716972872), (Int.ofNat 147474905537731879415170363382658), (Int.negOfNat 1503295999321511950935824917031), (Int.negOfNat 27857270101698915132377331106), (Int.ofNat 247673558697223507298976880496), (Int.ofNat 8279913342567702280440837350), (Int.negOfNat 8469828409627647243376035477), (Int.negOfNat 386244841104883233420192511), (Int.ofNat 140588245600644658470516494), (Int.ofNat 7498984723409775414568687), (Int.negOfNat 1325180390800867409838950), (Int.negOfNat 78120088128481318716434), (Int.ofNat 7918502325168204635610), (Int.ofNat 501732070099543840464), (Int.negOfNat 32775589179759215856), (Int.negOfNat 2221896118292482902), (Int.ofNat 140445110968321889), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(191496860018571811928883339621609/281474976710656000000000000000000), (73737452768865939707585181691329/1125899906842624000000000000000000), (-1503295999321511950935824917031/2251799813685248000000000000000000), (-13928635050849457566188665553/1125899906842624000000000000000000), (15479597418576469206186055031/140737488355328000000000000000000), (165598266851354045608816747/45035996273704960000000000000000), (-8469828409627647243376035477/2251799813685248000000000000000000), (-386244841104883233420192511/2251799813685248000000000000000000), (70294122800322329235258247/1125899906842624000000000000000000), (7498984723409775414568687/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial153.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial153.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial153.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 1824363223911913626958791488124334), (Int.ofNat 148069928732016471324172842890726), (Int.ofNat 2913428435423158178953724678259), (Int.ofNat 982863042437896118726179098646), (Int.negOfNat 118132841689211016953983565097), (Int.negOfNat 59768496354616229253882456000), (Int.ofNat 1849008522069965782809958017), (Int.ofNat 1496836292848361739001455353), (Int.ofNat 9584579695083193898989488), (Int.negOfNat 19137930895778786798942071), (Int.negOfNat 476715076548813986570284), (Int.ofNat 143224656331956628800852), (Int.ofNat 4958234545623873756208), (Int.negOfNat 711059597603406745054), (Int.negOfNat 28798063350865580914), (Int.ofNat 2611789956040698890), (Int.ofNat 118139230259699805), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(912181611955956813479395744062167/1125899906842624000000000000000000), (74034964366008235662086421445363/1125899906842624000000000000000000), (2913428435423158178953724678259/2251799813685248000000000000000000), (491431521218948059363089549323/1125899906842624000000000000000000), (-118132841689211016953983565097/2251799813685248000000000000000000), (-7471062044327028656735307/281474976710656000000000000000), (1849008522069965782809958017/2251799813685248000000000000000000), (1496836292848361739001455353/2251799813685248000000000000000000), (599036230942699618686843/140737488355328000000000000000000), (-19137930895778786798942071/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial153.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial153.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial153.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 2136519387998067177995791140752530), (Int.ofNat 163946835312601606702232732555473), (Int.ofNat 2571317385243724476738524131984), (Int.negOfNat 1305518394163391556515911451804), (Int.negOfNat 252203489596233478632800822352), (Int.ofNat 54503824582427972344165999624), (Int.ofNat 11655333736829139554079571381), (Int.negOfNat 767456252973095267028982283), (Int.negOfNat 224819738801996679693026108), (Int.ofNat 2519103593038841556027877), (Int.ofNat 2178447847959536925381984), (Int.ofNat 21575417545393600278720), (Int.negOfNat 13089235997664532719528), (Int.negOfNat 264761598304826419218), (Int.ofNat 54498103983071779954), (Int.ofNat 1450070226979302650), (Int.negOfNat 201627732768438121), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(213651938799806717799579114075253/225179981368524800000000000000000), (163946835312601606702232732555473/2251799813685248000000000000000000), (160707336577732779796157758249/140737488355328000000000000000000), (-326379598540847889128977862951/562949953421312000000000000000000), (-15762718099764592414550051397/140737488355328000000000000000000), (6812978072803496543020749953/281474976710656000000000000000000), (11655333736829139554079571381/2251799813685248000000000000000000), (-767456252973095267028982283/2251799813685248000000000000000000), (-56204934700499169923256527/562949953421312000000000000000000), (2519103593038841556027877/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial153.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial153.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial153.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 2462556710515364638353030008275900), (Int.ofNat 156536338125176599740680720464997), (Int.negOfNat 5039292594606621548575424454668), (Int.negOfNat 64386713024500285577056826269), (Int.ofNat 564118740735716309781306667421), (Int.ofNat 51110384291511386088870927296), (Int.negOfNat 15725454415987528159648646543), (Int.negOfNat 2132092621134634527834829439), (Int.ofNat 137637929604457216521627694), (Int.ofNat 28460354000294646283515735), (Int.negOfNat 489919510811304148069834), (Int.negOfNat 210711923027345295374090), (Int.negOfNat 291721523255298141926), (Int.ofNat 1036672711416377836764), (Int.ofNat 11236119342859261116), (Int.negOfNat 3826116838653406282), (Int.negOfNat 76939595132743405), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(24625567105153646383530300082759/22517998136852480000000000000000), (156536338125176599740680720464997/2251799813685248000000000000000000), (-1259823148651655387143856113667/562949953421312000000000000000000), (-64386713024500285577056826269/2251799813685248000000000000000000), (564118740735716309781306667421/2251799813685248000000000000000000), (798599754554865407638608239/35184372088832000000000000000000), (-15725454415987528159648646543/2251799813685248000000000000000000), (-2132092621134634527834829439/2251799813685248000000000000000000), (68818964802228608260813847/1125899906842624000000000000000000), (5692070800058929256703147/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial153.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial153.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial153.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 2764388099043895274033670158639287), (Int.ofNat 153974373309444196316601147283152), (Int.ofNat 7361554047159525831246242907486), (Int.ofNat 3166430314215451816975084849447), (Int.negOfNat 211525724425454894195924367571), (Int.negOfNat 207522387316154144565386204158), (Int.negOfNat 15586013997368998785239213597), (Int.ofNat 2690592932358445857694455257), (Int.ofNat 322991036379155784508265406), (Int.negOfNat 16848056179774858511350197), (Int.negOfNat 3013572631069706242427880), (Int.ofNat 57152292302060021415110), (Int.ofNat 17576399928852292209486), (Int.negOfNat 74398414059734462022), (Int.negOfNat 72432585766876737854), (Int.negOfNat 291165618192265174), (Int.ofNat 242210537005076153), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(2764388099043895274033670158639287/2251799813685248000000000000000000), (9623398331840262269787571705197/140737488355328000000000000000000), (3680777023579762915623121453743/1125899906842624000000000000000000), (3166430314215451816975084849447/2251799813685248000000000000000000), (-211525724425454894195924367571/2251799813685248000000000000000000), (-103761193658077072282693102079/1125899906842624000000000000000000), (-15586013997368998785239213597/2251799813685248000000000000000000), (2690592932358445857694455257/2251799813685248000000000000000000), (161495518189577892254132703/1125899906842624000000000000000000), (-16848056179774858511350197/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial153.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial153.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial153.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 3116507428235311967408495702760829), (Int.ofNat 196537568979312448083644617480012), (Int.ofNat 3218369069544370442655215528914), (Int.negOfNat 7367446081442837410105803326648), (Int.negOfNat 2210687246225338649669890571246), (Int.negOfNat 78737620601038858815812899380), (Int.ofNat 38623355210859599342018022491), (Int.ofNat 3247459584722524986482413729), (Int.negOfNat 324514646220906486699202724), (Int.negOfNat 38854184871246800848237037), (Int.ofNat 1643473132396048513982750), (Int.ofNat 270000636444151316421132), (Int.negOfNat 5392770254271974111072), (Int.negOfNat 1283569175216199051566), (Int.ofNat 11222316976569091254), (Int.ofNat 4582664838627253002), (Int.ofNat 152902437438931), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(3116507428235311967408495702760829/2251799813685248000000000000000000), (49134392244828112020911154370003/562949953421312000000000000000000), (1609184534772185221327607764457/1125899906842624000000000000000000), (-920930760180354676263225415831/281474976710656000000000000000000), (-1105343623112669324834945285623/1125899906842624000000000000000000), (-3936881030051942940790644969/112589990684262400000000000000000), (38623355210859599342018022491/2251799813685248000000000000000000), (3247459584722524986482413729/2251799813685248000000000000000000), (-81128661555226621674800681/562949953421312000000000000000000), (-38854184871246800848237037/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial153.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial153.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial153.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 3428412678093841288055620053420177), (Int.ofNat 52420671175478885827926187809281), (Int.negOfNat 89624508702736200127990297025193), (Int.negOfNat 20958863205095251208667377483140), (Int.negOfNat 259126289926116407625591150079), (Int.ofNat 454108368135422730978580647192), (Int.ofNat 30564846770225552979183369909), (Int.negOfNat 4802023631401783769680102819), (Int.negOfNat 461549938069758479883999266), (Int.ofNat 31313911606888982504575949), (Int.ofNat 3801207714766667008644286), (Int.negOfNat 139484183943476791898994), (Int.negOfNat 20856725569322128896304), (Int.ofNat 449861041800162627884), (Int.ofNat 83176393402030693750), (Int.negOfNat 998400106268353960), (Int.negOfNat 257197777009946027), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(3428412678093841288055620053420177/2251799813685248000000000000000000), (52420671175478885827926187809281/2251799813685248000000000000000000), (-89624508702736200127990297025193/2251799813685248000000000000000000), (-1047943160254762560433368874157/112589990684262400000000000000000), (-259126289926116407625591150079/2251799813685248000000000000000000), (56763546016927841372322580899/281474976710656000000000000000000), (30564846770225552979183369909/2251799813685248000000000000000000), (-4802023631401783769680102819/2251799813685248000000000000000000), (-230774969034879239941999633/1125899906842624000000000000000000), (31313911606888982504575949/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial153.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial153.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial153.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 3018713420581583497646018031038933), (Int.negOfNat 526213018261396903202539482133203), (Int.negOfNat 181803695186760270848237295594523), (Int.negOfNat 3274714432758388205080992903131), (Int.ofNat 4423401847021009511313071804912), (Int.ofNat 298513240009909962731372853945), (Int.negOfNat 57679626536838137188513458935), (Int.negOfNat 5210794885981796642106420821), (Int.ofNat 469841945973890603343318820), (Int.ofNat 49724848304657649247567393), (Int.negOfNat 2635402579571090977755082), (Int.negOfNat 312779625053024027481284), (Int.ofNat 10839023091568703955894), (Int.ofNat 1413509762745521291124), (Int.negOfNat 34072936211101687632), (Int.negOfNat 4837293047302316478), (Int.ofNat 76633790257865543), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(3018713420581583497646018031038933/2251799813685248000000000000000000), (-526213018261396903202539482133203/2251799813685248000000000000000000), (-181803695186760270848237295594523/2251799813685248000000000000000000), (-3274714432758388205080992903131/2251799813685248000000000000000000), (276462615438813094457066987807/140737488355328000000000000000000), (59702648001981992546274570789/450359962737049600000000000000000), (-11535925307367627437702691787/450359962737049600000000000000000), (-5210794885981796642106420821/2251799813685248000000000000000000), (23492097298694530167165941/112589990684262400000000000000000), (49724848304657649247567393/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial153.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial153.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial153.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 1288985717939986972969626306426537), (Int.negOfNat 1140124373904116665641366917984920), (Int.negOfNat 87721179938891269779772174912088), (Int.ofNat 32963431474614259136258467658757), (Int.ofNat 3168659393978094166604290231728), (Int.negOfNat 549598963358998404964877647114), (Int.negOfNat 57158614505920257794685423891), (Int.ofNat 5693313507886669267172128075), (Int.ofNat 611593358296767534929507620), (Int.negOfNat 40084869688237783298230699), (Int.negOfNat 4359681445392629824161568), (Int.ofNat 204306440953277550263724), (Int.ofNat 22238576752776452898908), (Int.negOfNat 788448874808335733772), (Int.negOfNat 85356293578329990144), (Int.ofNat 2336689635631235938), (Int.ofNat 272185017014815901), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(1288985717939986972969626306426537/2251799813685248000000000000000000), (-28503109347602916641034172949623/56294995342131200000000000000000), (-10965147492361408722471521864011/281474976710656000000000000000000), (32963431474614259136258467658757/2251799813685248000000000000000000), (198041212123630885412768139483/140737488355328000000000000000000), (-274799481679499202482438823557/1125899906842624000000000000000000), (-57158614505920257794685423891/2251799813685248000000000000000000), (227732540315466770686885123/90071992547409920000000000000000), (30579667914838376746475381/112589990684262400000000000000000), (-40084869688237783298230699/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial153.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial153.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial153.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 1048126239669331032801814217785198), (Int.negOfNat 1045928190669732408774768319957694), (Int.ofNat 133115298226696532693766085398460), (Int.ofNat 31195985612200558876932823243763), (Int.negOfNat 3686870684075522262752998870873), (Int.negOfNat 591280075083298832215668515539), (Int.ofNat 53565533996301753721463590049), (Int.ofNat 7044876240442171280019844525), (Int.negOfNat 495010578099520709856214234), (Int.negOfNat 56584831323628299744040337), (Int.ofNat 3176028143774165177907230), (Int.ofNat 324722389204246754429660), (Int.negOfNat 14961320043990022605796), (Int.negOfNat 1391062442673101163072), (Int.ofNat 54077220722936763952), (Int.ofNat 4533610609082401754), (Int.negOfNat 158416229621459975), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-524063119834665516400907108892599/1125899906842624000000000000000000), (-522964095334866204387384159978847/1125899906842624000000000000000000), (6655764911334826634688304269923/112589990684262400000000000000000), (31195985612200558876932823243763/2251799813685248000000000000000000), (-3686870684075522262752998870873/2251799813685248000000000000000000), (-591280075083298832215668515539/2251799813685248000000000000000000), (53565533996301753721463590049/2251799813685248000000000000000000), (281795049617686851200793781/90071992547409920000000000000000), (-247505289049760354928107117/1125899906842624000000000000000000), (-56584831323628299744040337/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial153.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial153.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial153.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial153.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial153.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial153.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial153.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial153.reflect := by
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

end Bin153
end
end ErdosOverlap.OuterNumerics
