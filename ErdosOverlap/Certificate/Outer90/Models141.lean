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

/-! # Exact integer weighted outer models for source bin 141

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin141

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 3087770700823758700)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 2982959814889999000)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 2249778974336385500)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 1192199642434572000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 698124735652624000)⟩, ⟨(19494472361809/1000000000000), (Int.negOfNat 260730467348492670)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 606012556689187950)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 402976752274645400)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 547038640253721900)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 152551957460860240)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial141.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial141.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9742165980315394000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1842439275795553000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1587164750465646400)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 614064674786464400)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 209732378717605130)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 26226429356502920)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 31904252797251020)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 117192448105495830)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 13924895737050507)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial141.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial141.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9742165980315394000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1842439275795553000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1587164750465646400)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 614064674786464400)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 209732378717605130)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 26226429356502920)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 31904252797251020)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 117192448105495830)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 13924895737050507)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial141.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial141.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial141.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 10173560966923035887592556803966801), (Int.ofNat 4675666966179240068481793168066189), (Int.ofNat 1012100514200769990950511109578350), (Int.negOfNat 155704978271190496500934339016533), (Int.negOfNat 29425537717210933861088465962019), (Int.ofNat 3273672578553814793975078941353), (Int.ofNat 461800055445766200020509623783), (Int.negOfNat 41353128664492612478774249583), (Int.negOfNat 4461245484167265364210881878), (Int.ofNat 339374391741512346534094814), (Int.ofNat 28975207091568936661028563), (Int.negOfNat 1947178139719944779009198), (Int.negOfNat 135219177658919907297589), (Int.ofNat 8258665812097488162679), (Int.ofNat 475834215389267705485), (Int.negOfNat 26814299416021834715), (Int.negOfNat 1343441501241215888), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-10173560966923035887592556803966801/11258999068426240000000000000000000), (4675666966179240068481793168066189/11258999068426240000000000000000000), (20242010284015399819010222191567/225179981368524800000000000000000), (-155704978271190496500934339016533/11258999068426240000000000000000000), (-29425537717210933861088465962019/11258999068426240000000000000000000), (3273672578553814793975078941353/11258999068426240000000000000000000), (461800055445766200020509623783/11258999068426240000000000000000000), (-41353128664492612478774249583/11258999068426240000000000000000000), (-2230622742083632682105440939/5629499534213120000000000000000000), (169687195870756173267047407/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial141.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial141.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial141.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial141 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 1637803002466562063517893790143147), (Int.ofNat 6242362479361933389504849253874198), (Int.negOfNat 289565163581068726519197555178983), (Int.negOfNat 215251897487303138977531476859957), (Int.ofNat 16105549034118000602161445976275), (Int.ofNat 4192641821003766786290242839070), (Int.negOfNat 326067999388849651485369837547), (Int.negOfNat 48689321380509306345092451079), (Int.ofNat 3627939092966416366465887669), (Int.ofNat 367441157029652551191313029), (Int.negOfNat 26101542197992557793901438), (Int.negOfNat 1937292040894885144701805), (Int.ofNat 132673237558062719793375), (Int.ofNat 7548023683098069245533), (Int.negOfNat 504598128692410779332), (Int.negOfNat 22382425319716208297), (Int.ofNat 1553409477322449778), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(1637803002466562063517893790143147/11258999068426240000000000000000000), (3121181239680966694752424626937099/5629499534213120000000000000000000), (-289565163581068726519197555178983/11258999068426240000000000000000000), (-215251897487303138977531476859957/11258999068426240000000000000000000), (644221961364720024086457839051/450359962737049600000000000000000), (419264182100376678629024283907/1125899906842624000000000000000000), (-326067999388849651485369837547/11258999068426240000000000000000000), (-48689321380509306345092451079/11258999068426240000000000000000000), (3627939092966416366465887669/11258999068426240000000000000000000), (367441157029652551191313029/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial141.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial141.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial141.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial141 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 11608091647774772321353158586509728), (Int.ofNat 3271859830517730157993233909818255), (Int.negOfNat 962258410031193432605775324077428), (Int.ofNat 9871891380368979003167489190389), (Int.ofNat 29966063130479980827546817698060), (Int.negOfNat 1696399172850804833014917427602), (Int.negOfNat 461739738231235830686077603336), (Int.ofNat 30924972269458916167837284643), (Int.ofNat 4237834614845658545231172442), (Int.negOfNat 298081479782904789554371627), (Int.negOfNat 25825396183230104282441348), (Int.ofNat 1873798265613410154907167), (Int.ofNat 112347958079254085972550), (Int.negOfNat 8428716662588825549340), (Int.negOfNat 367160242259381629975), (Int.ofNat 28607491340197789663), (Int.ofNat 871860733121584661), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(362752863992961635042286205828429/351843720888320000000000000000000), (654371966103546031598646781963651/2251799813685248000000000000000000), (-240564602507798358151443831019357/2814749767106560000000000000000000), (9871891380368979003167489190389/11258999068426240000000000000000000), (1498303156523999041377340884903/562949953421312000000000000000000), (-848199586425402416507458713801/5629499534213120000000000000000000), (-57717467278904478835759700417/1407374883553280000000000000000000), (30924972269458916167837284643/11258999068426240000000000000000000), (2118917307422829272615586221/5629499534213120000000000000000000), (-298081479782904789554371627/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial141.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial141.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial141.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial141 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 14782242135866974513299624578410211), (Int.ofNat 293235252057780338388596091130054), (Int.negOfNat 403607402811051281213621558064646), (Int.ofNat 130868209913847044701440533911428), (Int.negOfNat 2755894486562876923576360166989), (Int.negOfNat 3486482103324786101902038339290), (Int.ofNat 191054511081902290890213382087), (Int.ofNat 42719184819710367761236954722), (Int.negOfNat 2805068902962028083407883932), (Int.negOfNat 314542746739892842136238286), (Int.ofNat 22918809127807885623550631), (Int.ofNat 1562416257359525166517827), (Int.negOfNat 125191297269701476428168), (Int.negOfNat 5610537151946724593054), (Int.ofNat 497578490046418886348), (Int.ofNat 14577858263414689712), (Int.negOfNat 1511634790111298257), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(14782242135866974513299624578410211/11258999068426240000000000000000000), (146617626028890169194298045565027/5629499534213120000000000000000000), (-201803701405525640606810779032323/5629499534213120000000000000000000), (32717052478461761175360133477857/2814749767106560000000000000000000), (-2755894486562876923576360166989/11258999068426240000000000000000000), (-348648210332478610190203833929/1125899906842624000000000000000000), (191054511081902290890213382087/11258999068426240000000000000000000), (21359592409855183880618477361/5629499534213120000000000000000000), (-701267225740507020851970983/2814749767106560000000000000000000), (-157271373369946421068119143/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial141.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial141.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial141.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial141 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 14662409488293487859580338047862321), (Int.negOfNat 65527840256666798156680949699372), (Int.ofNat 104924959843034107534411329422023), (Int.ofNat 17538246859886764632755159160754), (Int.negOfNat 18249338399252806110643126371276), (Int.ofNat 720812412413956428064879267955), (Int.ofNat 355461747030648169007702711596), (Int.negOfNat 20758966666941234849783296888), (Int.negOfNat 3398644040829770747259964206), (Int.ofNat 237489656153215090440318902), (Int.ofNat 20026804785386099188669809), (Int.negOfNat 1632307347266532388826025), (Int.negOfNat 80451292776178649901719), (Int.ofNat 7735865125771273316335), (Int.ofNat 232839330659130281546), (Int.negOfNat 27637167240211631149), (Int.negOfNat 414204860739003941), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(14662409488293487859580338047862321/11258999068426240000000000000000000), (-16381960064166699539170237424843/2814749767106560000000000000000000), (104924959843034107534411329422023/11258999068426240000000000000000000), (8769123429943382316377579580377/5629499534213120000000000000000000), (-4562334599813201527660781592819/2814749767106560000000000000000000), (144162482482791285612975853591/2251799813685248000000000000000000), (88865436757662042251925677899/2814749767106560000000000000000000), (-2594870833367654356222912111/1407374883553280000000000000000000), (-1699322020414885373629982103/5629499534213120000000000000000000), (118744828076607545220159451/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial141.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial141.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial141.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial141 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 14841797051962580169687103119137967), (Int.ofNat 94415334146856990231337689005530), (Int.negOfNat 103619307515032383993656244377024), (Int.negOfNat 58956743521938988688838808063173), (Int.ofNat 1818065869273173697417392086133), (Int.ofNat 2306564263034449564136462036095), (Int.negOfNat 116012070949878318792754882053), (Int.negOfNat 31464873476068936424773155284), (Int.ofNat 2029441339730165771265798815), (Int.ofNat 231776595062761780347403582), (Int.negOfNat 18373696296985932489501385), (Int.negOfNat 1075646406229490939218369), (Int.ofNat 106584637727285115861604), (Int.ofNat 3364290753401260566192), (Int.negOfNat 439197156909810005449), (Int.negOfNat 7149661959207106187), (Int.ofNat 1469860102900146736), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(14841797051962580169687103119137967/11258999068426240000000000000000000), (9441533414685699023133768900553/1125899906842624000000000000000000), (-1619051679922380999900878818391/175921860444160000000000000000000), (-58956743521938988688838808063173/11258999068426240000000000000000000), (1818065869273173697417392086133/11258999068426240000000000000000000), (461312852606889912827292407219/2251799813685248000000000000000000), (-116012070949878318792754882053/11258999068426240000000000000000000), (-7866218369017234106193288821/2814749767106560000000000000000000), (405888267946033154253159763/2251799813685248000000000000000000), (115888297531380890173701791/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial141.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial141.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial141.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial141 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 14236561021806751166240885480541936), (Int.negOfNat 818701431269822646319286422785445), (Int.negOfNat 273717934732875663949205910935116), (Int.ofNat 16235884705231072822478929569802), (Int.ofNat 12042217636141077110502527754914), (Int.negOfNat 520695043657541880581599093380), (Int.negOfNat 244409694322225584165033010019), (Int.ofNat 13937921266274144304764041862), (Int.ofNat 2371191099761267781358116197), (Int.negOfNat 174711195735704980535176020), (Int.negOfNat 13236783819442911381047070), (Int.ofNat 1281893731961041826400898), (Int.ofNat 45947803794525221432635), (Int.negOfNat 6325966143905175478963), (Int.negOfNat 95324378718268032819), (Int.ofNat 22979946562859230779), (Int.negOfNat 43451011643576779), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(889785063862921947890055342533871/703687441776640000000000000000000), (-163740286253964529263857284557089/2251799813685248000000000000000000), (-68429483683218915987301477733779/2814749767106560000000000000000000), (8117942352615536411239464784901/5629499534213120000000000000000000), (6021108818070538555251263877457/5629499534213120000000000000000000), (-26034752182877094029079954669/562949953421312000000000000000000), (-244409694322225584165033010019/11258999068426240000000000000000000), (6968960633137072152382020931/5629499534213120000000000000000000), (2371191099761267781358116197/11258999068426240000000000000000000), (-8735559786785249026758801/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial141.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial141.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial141.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial141 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 11796835351440111930692693959378176), (Int.negOfNat 1413756646493744881135844257376473), (Int.ofNat 25092743923237369706948247412351), (Int.ofNat 63609559688644909859442347647679), (Int.negOfNat 2095681762750057936470601490696), (Int.negOfNat 1639043950351127632449194861186), (Int.ofNat 74675924855244805188201237849), (Int.ofNat 21243967654189620580951270641), (Int.negOfNat 1360968272519210068498685895), (Int.negOfNat 148059012311805059800573155), (Int.ofNat 13159708898402841772554509), (Int.ofNat 592154903978865792389003), (Int.negOfNat 79853154101809991845416), (Int.negOfNat 1234201931780905151943), (Int.ofNat 336928035173110716064), (Int.negOfNat 496690746732784508), (Int.negOfNat 1275533458228134975), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(46081388091562937229268335778821/43980465111040000000000000000000), (-1413756646493744881135844257376473/11258999068426240000000000000000000), (25092743923237369706948247412351/11258999068426240000000000000000000), (63609559688644909859442347647679/11258999068426240000000000000000000), (-261960220343757242058825186337/1407374883553280000000000000000000), (-819521975175563816224597430593/5629499534213120000000000000000000), (74675924855244805188201237849/11258999068426240000000000000000000), (21243967654189620580951270641/11258999068426240000000000000000000), (-272193654503842013699737179/2251799813685248000000000000000000), (-29611802462361011960114631/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial141.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial141.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial141.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial141 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 9499677826543589355311800127511153), (Int.negOfNat 726063913663420160462931536332151), (Int.ofNat 254570085582036777053329677824012), (Int.ofNat 2110333477622935188050597081617), (Int.negOfNat 9986866742406904993579285281155), (Int.ofNat 248823265924842758782355635913), (Int.ofNat 168396148175998665311572983709), (Int.negOfNat 8109186035617247234016893131), (Int.negOfNat 1497373000615738840874023595), (Int.ofNat 110907385729587105447724605), (Int.ofNat 7184606591890196219583839), (Int.negOfNat 860154257771229213064633), (Int.negOfNat 15795249870687599558546), (Int.ofNat 4386260990625101399483), (Int.negOfNat 19696367494982202246), (Int.negOfNat 16442096189558320132), (Int.ofNat 320705135091196245), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(9499677826543589355311800127511153/11258999068426240000000000000000000), (-726063913663420160462931536332151/11258999068426240000000000000000000), (63642521395509194263332419456003/2814749767106560000000000000000000), (2110333477622935188050597081617/11258999068426240000000000000000000), (-1997373348481380998715857056231/2251799813685248000000000000000000), (248823265924842758782355635913/11258999068426240000000000000000000), (168396148175998665311572983709/11258999068426240000000000000000000), (-8109186035617247234016893131/11258999068426240000000000000000000), (-299474600123147768174804719/2251799813685248000000000000000000), (22181477145917421089544921/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial141.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial141.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial141.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial141 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 8940303886612738922833538074692064), (Int.ofNat 45314857465725114369176157777631), (Int.ofNat 80304774798107252312262245149491), (Int.negOfNat 47442999295325088030158844558560), (Int.negOfNat 835546091350074616351402895292), (Int.ofNat 1173453336018787087384582766750), (Int.negOfNat 26908114870528625736228175959), (Int.negOfNat 13692026899075109897778017212), (Int.ofNat 696788667509967080973253467), (Int.ofNat 82009662741418100232580060), (Int.negOfNat 7488993798229118642562220), (Int.negOfNat 209766876433346059552038), (Int.ofNat 47819385384973132054465), (Int.negOfNat 399922825834213164417), (Int.negOfNat 207223683056827668859), (Int.ofNat 5686644879074898811), (Int.ofNat 942579751832313481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(279384496456648091338548064834127/351843720888320000000000000000000), (45314857465725114369176157777631/11258999068426240000000000000000000), (80304774798107252312262245149491/11258999068426240000000000000000000), (-296518745595781800188492778491/70368744177664000000000000000000), (-208886522837518654087850723823/2814749767106560000000000000000000), (4693813344075148349538331067/45035996273704960000000000000000), (-26908114870528625736228175959/11258999068426240000000000000000000), (-3423006724768777474444504303/2814749767106560000000000000000000), (696788667509967080973253467/11258999068426240000000000000000000), (4100483137070905011629003/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial141.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial141.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial141.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial141 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 8993528234808358204314393671477097), (Int.negOfNat 146080741778629744755823508529720), (Int.negOfNat 144651587630337788892883160442411), (Int.negOfNat 17591302339843836109540274916932), (Int.ofNat 6458007341956982065685108072105), (Int.ofNat 115850765635190321777075954325), (Int.negOfNat 111110228965806239523852206313), (Int.ofNat 2058414515002201524938230444), (Int.ofNat 876874801404510897850505275), (Int.negOfNat 45044111633783712322088662), (Int.negOfNat 2915667253641855031571705), (Int.ofNat 399101592565569354514829), (Int.negOfNat 4773999312597398271326), (Int.negOfNat 2143264716146461242912), (Int.ofNat 94845970898653351141), (Int.ofNat 7632713438896756647), (Int.negOfNat 431482405340904964), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(8993528234808358204314393671477097/11258999068426240000000000000000000), (-3652018544465743618895587713243/281474976710656000000000000000000), (-144651587630337788892883160442411/11258999068426240000000000000000000), (-4397825584960959027385068729233/2814749767106560000000000000000000), (1291601468391396413137021614421/2251799813685248000000000000000000), (4634030625407612871083038173/450359962737049600000000000000000), (-111110228965806239523852206313/11258999068426240000000000000000000), (514603628750550381234557611/2814749767106560000000000000000000), (35074992056180435914020211/450359962737049600000000000000000), (-22522055816891856161044331/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial141.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial141.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial141.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial141 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 8082416960122342038176809140397726), (Int.negOfNat 739485932001180296804396529005462), (Int.negOfNat 109881542172139675550968912604915), (Int.ofNat 23382055511164050062329312065010), (Int.ofNat 2303135861018010376259763675597), (Int.negOfNat 755319490168138058052597882708), (Int.negOfNat 18913194691550982939084635324), (Int.ofNat 8605163245879926208242586718), (Int.negOfNat 35167083973363785879008376), (Int.negOfNat 40706778975778263106676052), (Int.ofNat 1686911035674194989161019), (Int.negOfNat 14932574792595270750575), (Int.negOfNat 13796621036900081537779), (Int.ofNat 1283282446179928609495), (Int.ofNat 64055383207635645156), (Int.negOfNat 8548399230447603081), (Int.negOfNat 484923879449732761), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(4041208480061171019088404570198863/5629499534213120000000000000000000), (-369742966000590148402198264502731/5629499534213120000000000000000000), (-21976308434427935110193782520983/2251799813685248000000000000000000), (2338205551116405006232931206501/1125899906842624000000000000000000), (2303135861018010376259763675597/11258999068426240000000000000000000), (-188829872542034514513149470677/2814749767106560000000000000000000), (-4728298672887745734771158831/2814749767106560000000000000000000), (4302581622939963104121293359/5629499534213120000000000000000000), (-4395885496670473234876047/1407374883553280000000000000000000), (-10176694743944565776669013/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial141.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial141.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial141.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial141 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 6363518144999175746311999040941993), (Int.negOfNat 885050462618601154050909199019982), (Int.ofNat 26271701032465722853241210157237), (Int.ofNat 13129418044757188058062721222266), (Int.negOfNat 4158117077779373739360135318581), (Int.negOfNat 345038453360387375688719568910), (Int.ofNat 75206025309469373795892859820), (Int.ofNat 3526600940899131821092005268), (Int.negOfNat 535132824935377751204142932), (Int.negOfNat 18498352900517130740886794), (Int.ofNat 857942711885919740300251), (Int.ofNat 56721989270014216536553), (Int.ofNat 13058747547928401464472), (Int.negOfNat 128069607125916962236), (Int.negOfNat 117762996811688024652), (Int.ofNat 804493832825124788), (Int.ofNat 389707718129753443), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(6363518144999175746311999040941993/11258999068426240000000000000000000), (-442525231309300577025454599509991/5629499534213120000000000000000000), (26271701032465722853241210157237/11258999068426240000000000000000000), (6564709022378594029031360611133/5629499534213120000000000000000000), (-4158117077779373739360135318581/11258999068426240000000000000000000), (-34503845336038737568871956891/1125899906842624000000000000000000), (3760301265473468689794642991/562949953421312000000000000000000), (881650235224782955273001317/2814749767106560000000000000000000), (-133783206233844437801035733/2814749767106560000000000000000000), (-9249176450258565370443397/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial141.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial141.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial141.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial141 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 4731087435120566916395057531654576), (Int.negOfNat 767639254378756721633527819357906), (Int.negOfNat 2962253260729514209747808407112), (Int.negOfNat 20970679066857767909757378048890), (Int.negOfNat 2767207636890024515341383476274), (Int.ofNat 586398051889614954143366593165), (Int.ofNat 56592443542873245786259649944), (Int.negOfNat 6307503290368568636965938333), (Int.negOfNat 561335472202713159133093888), (Int.ofNat 25962274188179948929777287), (Int.ofNat 3663380734585070836566452), (Int.ofNat 63160673754427839954583), (Int.negOfNat 18170831275409517250330), (Int.negOfNat 1317179659497038752870), (Int.ofNat 73075937447839832895), (Int.ofNat 8212780458706661597), (Int.ofNat 27268007067152041), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(295692964695035432274691095728411/703687441776640000000000000000000), (-383819627189378360816763909678953/5629499534213120000000000000000000), (-370281657591189276218476050889/1407374883553280000000000000000000), (-2097067906685776790975737804889/1125899906842624000000000000000000), (-1383603818445012257670691738137/5629499534213120000000000000000000), (117279610377922990828673318633/2251799813685248000000000000000000), (7074055442859155723282456243/1407374883553280000000000000000000), (-6307503290368568636965938333/11258999068426240000000000000000000), (-68522396509120258683239/1374389534720000000000000000000), (25962274188179948929777287/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial141.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial141.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial141.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial141 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 2993371839897467086124550540486984), (Int.negOfNat 1065231257794547200676283783542983), (Int.negOfNat 139787625816846681281883304290895), (Int.negOfNat 14939596159767145260678680408066), (Int.ofNat 4251416454912141566715915915977), (Int.ofNat 565768201126673152176332734650), (Int.negOfNat 65182818752718958714075686917), (Int.negOfNat 8261933281383459985416617331), (Int.ofNat 470051140178446848286035359), (Int.ofNat 72777354862498751693721331), (Int.negOfNat 1014618139849566546561508), (Int.negOfNat 451782551967391389097755), (Int.negOfNat 8758482855157243669145), (Int.ofNat 2128577607143067736147), (Int.ofNat 88651107780487126948), (Int.negOfNat 8255122522609630203), (Int.negOfNat 347933030918601922), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(374171479987183385765568817560873/1407374883553280000000000000000000), (-1065231257794547200676283783542983/11258999068426240000000000000000000), (-27957525163369336256376660858179/2251799813685248000000000000000000), (-7469798079883572630339340204033/5629499534213120000000000000000000), (4251416454912141566715915915977/11258999068426240000000000000000000), (11315364022533463043526654693/225179981368524800000000000000000), (-65182818752718958714075686917/11258999068426240000000000000000000), (-8261933281383459985416617331/11258999068426240000000000000000000), (470051140178446848286035359/11258999068426240000000000000000000), (72777354862498751693721331/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial141.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial141.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial141.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial141 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.ofNat 265295683240183188729068723445992), (Int.negOfNat 1637927945763735351014507315834060), (Int.negOfNat 102172594466336283514631588944356), (Int.ofNat 27845131753647385621107892705745), (Int.ofNat 4471699913962956964021714134892), (Int.negOfNat 574788720380627932895236096646), (Int.negOfNat 89390927745603734651083357207), (Int.ofNat 6415388085601917136571769213), (Int.ofNat 1028929641835473257573795572), (Int.negOfNat 35237620883414814889212634), (Int.negOfNat 7874160293809344671004517), (Int.ofNat 52686816820169320214218), (Int.ofNat 43729426888021629522301), (Int.ofNat 548591489661018267831), (Int.negOfNat 183678731387575363305), (Int.negOfNat 4799329880041916645), (Int.ofNat 416462969578378172), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(33161960405022898591133590430749/1407374883553280000000000000000000), (-81896397288186767550725365791703/562949953421312000000000000000000), (-25543148616584070878657897236089/2814749767106560000000000000000000), (5569026350729477124221578541149/2251799813685248000000000000000000), (1117924978490739241005428533723/2814749767106560000000000000000000), (-287394360190313966447618048323/5629499534213120000000000000000000), (-89390927745603734651083357207/11258999068426240000000000000000000), (6415388085601917136571769213/11258999068426240000000000000000000), (257232410458868314393448893/2814749767106560000000000000000000), (-17618810441707407444606317/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial141.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial141.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial141.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial141 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 3147997832690570377958298352763616), (Int.negOfNat 1628720611075877059808398516240558), (Int.ofNat 110688426268540870700994328855097), (Int.ofNat 31457876988749118857941294354621), (Int.negOfNat 3931069587872615450589641826707), (Int.negOfNat 776189020820363815385544740503), (Int.ofNat 68864750474425461487877700537), (Int.ofNat 11606715264817579144836066343), (Int.negOfNat 621313094303016872824517812), (Int.negOfNat 110214587442214462750639484), (Int.ofNat 3029805292371231882553687), (Int.ofNat 729460455229107940084378), (Int.negOfNat 6347016930434437944111), (Int.negOfNat 3567845446974404441869), (Int.negOfNat 14495494762852251345), (Int.ofNat 13865174771827891275), (Int.ofNat 14979324522780428), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-98374932271580324311196823523863/351843720888320000000000000000000), (-814360305537938529904199258120279/5629499534213120000000000000000000), (110688426268540870700994328855097/11258999068426240000000000000000000), (31457876988749118857941294354621/11258999068426240000000000000000000), (-3931069587872615450589641826707/11258999068426240000000000000000000), (-776189020820363815385544740503/11258999068426240000000000000000000), (68864750474425461487877700537/11258999068426240000000000000000000), (11606715264817579144836066343/11258999068426240000000000000000000), (-155328273575754218206129453/2814749767106560000000000000000000), (-27553646860553615687659871/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial141.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial141.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial141.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial141 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 5793075436928229498783378534783823), (Int.negOfNat 978806664142805598866046879168043), (Int.ofNat 165755339668928574272390505318021), (Int.negOfNat 15150421688008526384236458171117), (Int.negOfNat 5382004672835516206375205848846), (Int.ofNat 568820167658820413056840555790), (Int.ofNat 107536554081435037773614745637), (Int.negOfNat 7981834007649833534569657101), (Int.negOfNat 1285835052672704973946350819), (Int.ofNat 62226572007591090581885511), (Int.ofNat 10276340157410744425448188), (Int.negOfNat 295319000455962002917855), (Int.negOfNat 58954061361924354267175), (Int.ofNat 852047436016032223017), (Int.ofNat 253688885282629968142), (Int.negOfNat 484876516877340663), (Int.negOfNat 693717093025997638), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-5793075436928229498783378534783823/11258999068426240000000000000000000), (-978806664142805598866046879168043/11258999068426240000000000000000000), (165755339668928574272390505318021/11258999068426240000000000000000000), (-15150421688008526384236458171117/11258999068426240000000000000000000), (-2691002336417758103187602924423/5629499534213120000000000000000000), (56882016765882041305684055579/1125899906842624000000000000000000), (107536554081435037773614745637/11258999068426240000000000000000000), (-7981834007649833534569657101/11258999068426240000000000000000000), (-1285835052672704973946350819/11258999068426240000000000000000000), (62226572007591090581885511/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial141.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial141.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial141.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial141 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 7271207570783856271430864967873543), (Int.negOfNat 608363156944947669145161141008521), (Int.ofNat 9724125719203108924566795862987), (Int.negOfNat 24548155067175412558011050076658), (Int.ofNat 3452970151129079841371163356713), (Int.ofNat 806868668944658406719241093682), (Int.negOfNat 79358061137834149577062104984), (Int.negOfNat 12584568666157835641249170243), (Int.ofNat 907378361920229813356175448), (Int.ofNat 123443261477524230097166937), (Int.negOfNat 6299409465420577392320912), (Int.negOfNat 841930530364680267174337), (Int.ofNat 28941153923314236580830), (Int.ofNat 4211698012602035106330), (Int.negOfNat 92754133250512362155), (Int.negOfNat 16061343448278491623), (Int.ofNat 456601443596850799), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-7271207570783856271430864967873543/11258999068426240000000000000000000), (-608363156944947669145161141008521/11258999068426240000000000000000000), (9724125719203108924566795862987/11258999068426240000000000000000000), (-12274077533587706279005525038329/5629499534213120000000000000000000), (3452970151129079841371163356713/11258999068426240000000000000000000), (403434334472329203359620546841/5629499534213120000000000000000000), (-9919757642229268697132763123/1407374883553280000000000000000000), (-12584568666157835641249170243/11258999068426240000000000000000000), (113422295240028726669521931/1407374883553280000000000000000000), (123443261477524230097166937/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial141.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial141.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial141.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial141 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 8570757575255224386281769171883529), (Int.negOfNat 708701857701056269832275955543603), (Int.negOfNat 15545640760100193676447325941681), (Int.ofNat 17767431447698260037901626548528), (Int.ofNat 4635325653013681202342068435337), (Int.negOfNat 618676927899642542003033023280), (Int.negOfNat 102047659462264102668639979917), (Int.ofNat 10347629041118019903545215208), (Int.ofNat 1257074245544262572146933062), (Int.negOfNat 99116595840110564249339834), (Int.negOfNat 10346115172008217688031391), (Int.ofNat 611712573042008431147203), (Int.ofNat 61015385899424873722008), (Int.negOfNat 2621309667324136364816), (Int.negOfNat 267628489881099993438), (Int.ofNat 7886466820904213848), (Int.ofNat 651942405814846117), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-8570757575255224386281769171883529/11258999068426240000000000000000000), (-708701857701056269832275955543603/11258999068426240000000000000000000), (-15545640760100193676447325941681/11258999068426240000000000000000000), (1110464465481141252368851659283/703687441776640000000000000000000), (4635325653013681202342068435337/11258999068426240000000000000000000), (-7733461598745531775037912791/140737488355328000000000000000000), (-102047659462264102668639979917/11258999068426240000000000000000000), (1293453630139752487943151901/1407374883553280000000000000000000), (628537122772131286073466531/5629499534213120000000000000000000), (-49558297920055282124669917/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial141.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial141.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial141.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial141 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 9858781460987244507075391194258916), (Int.negOfNat 472782260192485669793998078539814), (Int.ofNat 136972378056790922251876073685059), (Int.ofNat 21162679651612233455369101232612), (Int.negOfNat 3875368019474979698365182292354), (Int.negOfNat 670961658969930691081066032882), (Int.ofNat 94140099924250267276326402664), (Int.ofNat 10644733438530006104480201538), (Int.negOfNat 1248655960668645546633532724), (Int.negOfNat 107446734240614966344560412), (Int.ofNat 10110318881397976616063311), (Int.ofNat 759380384227066530999615), (Int.negOfNat 54839265803841656602331), (Int.negOfNat 3925249504919843557615), (Int.ofNat 212243809939513150644), (Int.ofNat 15493996100566978509), (Int.negOfNat 914257315979431519), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-2464695365246811126768847798564729/2814749767106560000000000000000000), (-236391130096242834896999039269907/5629499534213120000000000000000000), (136972378056790922251876073685059/11258999068426240000000000000000000), (5290669912903058363842275308153/2814749767106560000000000000000000), (-1937684009737489849182591146177/5629499534213120000000000000000000), (-335480829484965345540533016441/5629499534213120000000000000000000), (11767512490531283409540800333/1407374883553280000000000000000000), (5322366719265003052240100769/5629499534213120000000000000000000), (-312163990167161386658383181/2814749767106560000000000000000000), (-26861683560153741586140103/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial141.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial141.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial141.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial141 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 10163607214369918034948853396317747), (Int.ofNat 172747046823656680403744664036470), (Int.ofNat 144410482331162140572602449602990), (Int.negOfNat 18290261518950876496063707756562), (Int.negOfNat 3627945169744396204256018110114), (Int.ofNat 674255380439747854328382086852), (Int.ofNat 72401446637924111011516185553), (Int.negOfNat 12797410011851543585699452716), (Int.negOfNat 905508736595329231282331515), (Int.ofNat 137774913159288294687324598), (Int.ofNat 7821923381483695524148855), (Int.negOfNat 943721579659666775587421), (Int.negOfNat 48728744490048509536044), (Int.ofNat 4461458215502351248008), (Int.ofNat 224667744915420299119), (Int.negOfNat 14911686372837151973), (Int.negOfNat 610167718603694596), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-10163607214369918034948853396317747/11258999068426240000000000000000000), (17274704682365668040374466403647/1125899906842624000000000000000000), (14441048233116214057260244960299/1125899906842624000000000000000000), (-9145130759475438248031853878281/5629499534213120000000000000000000), (-1813972584872198102128009055057/5629499534213120000000000000000000), (168563845109936963582095521713/2814749767106560000000000000000000), (72401446637924111011516185553/11258999068426240000000000000000000), (-3199352502962885896424863179/2814749767106560000000000000000000), (-181101747319065846256466303/2251799813685248000000000000000000), (68887456579644147343662299/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial141.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial141.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial141.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial141 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 9420423962486078039504323337223058), (Int.ofNat 476338533166670214307212574517919), (Int.ofNat 9388364063095416459241994297130), (Int.negOfNat 16731684590920811925477284317564), (Int.ofNat 3477663084355057231675478654860), (Int.ofNat 372055024011672784104814702997), (Int.negOfNat 105039059413547443010825377851), (Int.negOfNat 5595422013244476581818329362), (Int.ofNat 1562840361128829015621180233), (Int.ofNat 60432260184095610513853860), (Int.negOfNat 13771727045599457751331780), (Int.negOfNat 476219667194683547895568), (Int.ofNat 79813701250675383657615), (Int.ofNat 2705094252189586590193), (Int.negOfNat 327722651026508213091), (Int.negOfNat 11500482642837716209), (Int.ofNat 1371913188362012239), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-4710211981243039019752161668611529/5629499534213120000000000000000000), (476338533166670214307212574517919/11258999068426240000000000000000000), (938836406309541645924199429713/1125899906842624000000000000000000), (-4182921147730202981369321079391/2814749767106560000000000000000000), (173883154217752861583773932743/562949953421312000000000000000000), (372055024011672784104814702997/11258999068426240000000000000000000), (-105039059413547443010825377851/11258999068426240000000000000000000), (-2797711006622238290909164681/5629499534213120000000000000000000), (1562840361128829015621180233/11258999068426240000000000000000000), (3021613009204780525692693/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial141.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial141.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial141.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial141 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 8503520966006089379261511604949529), (Int.ofNat 433152921368647956601905844628524), (Int.negOfNat 3830207577243738429678439494410), (Int.ofNat 8935502013298895389517583511628), (Int.ofNat 1128733246854062143741002524067), (Int.negOfNat 652959594169896641429633089974), (Int.negOfNat 15997610301679974668050354489), (Int.ofNat 14540746034958269900795362219), (Int.ofNat 217992413831732406948163195), (Int.negOfNat 171333710955238437901277795), (Int.negOfNat 2747427421847591172385009), (Int.ofNat 1240421508581602832804487), (Int.ofNat 22919619024174435199806), (Int.negOfNat 6097071642777020116577), (Int.negOfNat 126139560597048983984), (Int.ofNat 21752085574227751868), (Int.ofNat 415841073931682835), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-8503520966006089379261511604949529/11258999068426240000000000000000000), (108288230342161989150476461157131/2814749767106560000000000000000000), (-383020757724373842967843949441/1125899906842624000000000000000000), (2233875503324723847379395877907/2814749767106560000000000000000000), (1128733246854062143741002524067/11258999068426240000000000000000000), (-326479797084948320714816544987/5629499534213120000000000000000000), (-15997610301679974668050354489/11258999068426240000000000000000000), (14540746034958269900795362219/11258999068426240000000000000000000), (43598482766346481389632639/2251799813685248000000000000000000), (-34266742191047687580255559/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial141.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial141.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial141.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial141 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 7583081691291980151704011707315590), (Int.ofNat 512212130912180247074032104391965), (Int.ofNat 30172553622952026081799994976837), (Int.negOfNat 3089324419207689532319336680440), (Int.negOfNat 2719900333251235139299426592216), (Int.ofNat 143520088834823848479165905107), (Int.ofNat 105936107886569799553344541691), (Int.negOfNat 2838202569997688669208111409), (Int.negOfNat 1798243399686721289072249565), (Int.ofNat 16424003521180837817813935), (Int.ofNat 16811274839118559577087081), (Int.ofNat 15458347305796932209313), (Int.negOfNat 100442595401394238011474), (Int.negOfNat 690454617555927196133), (Int.ofNat 420516924776818277596), (Int.ofNat 4962632269536805562), (Int.negOfNat 1649167311809631705), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-758308169129198015170401170731559/1125899906842624000000000000000000), (102442426182436049414806420878393/2251799813685248000000000000000000), (30172553622952026081799994976837/11258999068426240000000000000000000), (-77233110480192238307983417011/281474976710656000000000000000000), (-339987541656404392412428324027/1407374883553280000000000000000000), (143520088834823848479165905107/11258999068426240000000000000000000), (105936107886569799553344541691/11258999068426240000000000000000000), (-2838202569997688669208111409/11258999068426240000000000000000000), (-359648679937344257814449913/2251799813685248000000000000000000), (3284800704236167563562787/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial141.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial141.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial141.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial141 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 6495626056759874749500743993636692), (Int.ofNat 537623697803734718806188740215843), (Int.negOfNat 21601409452878099188766723854438), (Int.negOfNat 6633821961022848778112948903822), (Int.ofNat 2543009422852720216843023393328), (Int.ofNat 529889049246354910855653589447), (Int.negOfNat 73217678990654568518996885331), (Int.negOfNat 15461438067736457218123693768), (Int.ofNat 800125881136699312550200663), (Int.ofNat 197838126440088922065850620), (Int.negOfNat 4450305848189217455321340), (Int.negOfNat 1470792341916204571275502), (Int.ofNat 13305660455145677536685), (Int.ofNat 7315624664967969534367), (Int.negOfNat 11656525895080144531), (Int.negOfNat 26942039706569866171), (Int.negOfNat 82887367535861341), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-1623906514189968687375185998409173/2814749767106560000000000000000000), (537623697803734718806188740215843/11258999068426240000000000000000000), (-10800704726439049594383361927219/5629499534213120000000000000000000), (-3316910980511424389056474451911/5629499534213120000000000000000000), (158938088928295013552688962083/703687441776640000000000000000000), (529889049246354910855653589447/11258999068426240000000000000000000), (-73217678990654568518996885331/11258999068426240000000000000000000), (-1932679758467057152265461721/1407374883553280000000000000000000), (800125881136699312550200663/11258999068426240000000000000000000), (9891906322004446103292531/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial141.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial141.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial141.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial141 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 5508576600437077169261377331293667), (Int.ofNat 475631607263989949734574217044750), (Int.ofNat 16311498599726905517653235873175), (Int.ofNat 16903084548582666907342750558807), (Int.ofNat 695800337695773813141127893103), (Int.negOfNat 965895644714952372632183219695), (Int.negOfNat 101496373347612652767237198457), (Int.ofNat 14883698397701743092935441126), (Int.ofNat 2001824196065367958953612475), (Int.negOfNat 116567977524740606181429218), (Int.negOfNat 19156715145831305183820795), (Int.ofNat 563692617220391528859201), (Int.ofNat 114616402842562567563446), (Int.negOfNat 1829899537716432407298), (Int.negOfNat 480315127474516383021), (Int.ofNat 4107480948473250593), (Int.ofNat 1759944582059340424), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-5508576600437077169261377331293667/11258999068426240000000000000000000), (1902526429055959798938296868179/45035996273704960000000000000000), (652459943989076220706129434927/450359962737049600000000000000000), (16903084548582666907342750558807/11258999068426240000000000000000000), (695800337695773813141127893103/11258999068426240000000000000000000), (-193179128942990474526436643939/2251799813685248000000000000000000), (-101496373347612652767237198457/11258999068426240000000000000000000), (7441849198850871546467720563/5629499534213120000000000000000000), (80072967842614718358144499/450359962737049600000000000000000), (-58283988762370303090714609/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial141.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial141.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial141.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial141 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 4380774455852973293374705366600444), (Int.ofNat 677581397134638154113546375048116), (Int.ofNat 45652871302207662985681126421833), (Int.negOfNat 21368693854269409959024337873544), (Int.negOfNat 9333733812067262672609849453357), (Int.negOfNat 399068315315311399476412320009), (Int.ofNat 202742041118914557412244835067), (Int.ofNat 17220898759450494157635043532), (Int.negOfNat 2052399382563590802795350534), (Int.negOfNat 222293793079325097463088578), (Int.ofNat 12731519849568556830737131), (Int.ofNat 1625371698067348552750015), (Int.negOfNat 54373577063296440120921), (Int.negOfNat 7974283672329153703915), (Int.ofNat 170284640741815203644), (Int.ofNat 28737110086044786971), (Int.negOfNat 374768504846719379), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-1095193613963243323343676341650111/2814749767106560000000000000000000), (169395349283659538528386593762029/2814749767106560000000000000000000), (45652871302207662985681126421833/11258999068426240000000000000000000), (-2671086731783676244878042234193/1407374883553280000000000000000000), (-9333733812067262672609849453357/11258999068426240000000000000000000), (-399068315315311399476412320009/11258999068426240000000000000000000), (202742041118914557412244835067/11258999068426240000000000000000000), (4305224689862623539408760883/2814749767106560000000000000000000), (-1026199691281795401397675267/5629499534213120000000000000000000), (-111146896539662548731544289/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial141.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial141.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial141.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial141 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 3161503035804733183266092013115795), (Int.ofNat 317272980429861765814812012564843), (Int.negOfNat 282778488441629660271255529427887), (Int.negOfNat 74535889037392119552921559852230), (Int.ofNat 697188951069564473049500187413), (Int.ofNat 2255615754925036395195595393510), (Int.ofNat 126623782157410733906672781550), (Int.negOfNat 28959364924798060854644605488), (Int.negOfNat 2321561527767495819241372028), (Int.ofNat 222010505102268049814539244), (Int.ofNat 20975932183032672234458119), (Int.negOfNat 1160522871773178383861783), (Int.negOfNat 121230454690870646929552), (Int.ofNat 4449364745025550061516), (Int.ofNat 497416851852876173922), (Int.negOfNat 12947664972469777428), (Int.negOfNat 1718169894848188903), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-632300607160946636653218402623159/2251799813685248000000000000000000), (317272980429861765814812012564843/11258999068426240000000000000000000), (-282778488441629660271255529427887/11258999068426240000000000000000000), (-7453588903739211955292155985223/1125899906842624000000000000000000), (697188951069564473049500187413/11258999068426240000000000000000000), (225561575492503639519559539351/1125899906842624000000000000000000), (2532475643148214678133455631/225179981368524800000000000000000), (-1809960307799878803415287843/703687441776640000000000000000000), (-580390381941873954810343007/2814749767106560000000000000000000), (55502626275567012453634811/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial141.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial141.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial141.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial141 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 4167088290542035305849430891466391), (Int.negOfNat 1495948495786613128006948387839480), (Int.negOfNat 524818575524258398795399777897224), (Int.ofNat 22603261180679978695669544964654), (Int.ofNat 21256773982330494198889482881341), (Int.ofNat 874496788906285263318618139312), (Int.negOfNat 342163602037390404224749637964), (Int.negOfNat 22520496886487715972800875567), (Int.ofNat 3221802526724200934795325128), (Int.ofNat 249448266433484590512078483), (Int.negOfNat 20346126313760499142110182), (Int.negOfNat 1696756296352650700133923), (Int.ofNat 92912540693508905529710), (Int.ofNat 8000564756883820226280), (Int.negOfNat 322291326531019070145), (Int.negOfNat 28259245029377692757), (Int.ofNat 832424377229300099), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-4167088290542035305849430891466391/11258999068426240000000000000000000), (-37398712394665328200173709695987/281474976710656000000000000000000), (-65602321940532299849424972237153/1407374883553280000000000000000000), (11301630590339989347834772482327/5629499534213120000000000000000000), (21256773982330494198889482881341/11258999068426240000000000000000000), (54656049306642828957413633707/703687441776640000000000000000000), (-85540900509347601056187409491/2814749767106560000000000000000000), (-22520496886487715972800875567/11258999068426240000000000000000000), (402725315840525116849415641/1407374883553280000000000000000000), (249448266433484590512078483/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial141.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial141.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial141.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial141 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 8733193678388384037378138291660918), (Int.negOfNat 2645838511076675749391248862687772), (Int.ofNat 100318446819763028877882349521597), (Int.ofNat 167022507640619495865398209683792), (Int.ofNat 7449559942472331860322057051084), (Int.negOfNat 3379525547610211927992081629557), (Int.negOfNat 215486028403465399772234540783), (Int.ofNat 39509987658748385530453371851), (Int.ofNat 2793953318766648608941852781), (Int.negOfNat 303620521828539308520788051), (Int.negOfNat 22080010513098786502211552), (Int.ofNat 1652170468146151773466255), (Int.ofNat 119215577743835484303075), (Int.negOfNat 6710429277859601889697), (Int.negOfNat 470097513981891665348), (Int.ofNat 20801270414528928243), (Int.ofNat 1676395207637037382), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-4366596839194192018689069145830459/5629499534213120000000000000000000), (-661459627769168937347812215671943/2814749767106560000000000000000000), (100318446819763028877882349521597/11258999068426240000000000000000000), (10438906727538718491587388105237/703687441776640000000000000000000), (1862389985618082965080514262771/2814749767106560000000000000000000), (-3379525547610211927992081629557/11258999068426240000000000000000000), (-215486028403465399772234540783/11258999068426240000000000000000000), (39509987658748385530453371851/11258999068426240000000000000000000), (2793953318766648608941852781/11258999068426240000000000000000000), (-303620521828539308520788051/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial141.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial141.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial141.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial141 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 12284561539509838954747897520077942), (Int.negOfNat 293874049333856329390702468768399), (Int.ofNat 989121627395309136910445080285559), (Int.ofNat 82202091048270383976413894064323), (Int.negOfNat 26521761392998416913660309220696), (Int.negOfNat 2126659562755142600059390939354), (Int.ofNat 402059322324052911709908302904), (Int.ofNat 30138359687630345677318150437), (Int.negOfNat 3865979273878502889510669982), (Int.negOfNat 270361348359751273857043016), (Int.ofNat 25452286025665923075594937), (Int.ofNat 1657333275398453844058002), (Int.negOfNat 121801660119897622085671), (Int.negOfNat 7353209898753816516481), (Int.ofNat 442774431253120782955), (Int.ofNat 24442817698438302405), (Int.negOfNat 1276155353874830312), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-6142280769754919477373948760038971/5629499534213120000000000000000000), (-293874049333856329390702468768399/11258999068426240000000000000000000), (989121627395309136910445080285559/11258999068426240000000000000000000), (82202091048270383976413894064323/11258999068426240000000000000000000), (-3315220174124802114207538652587/1407374883553280000000000000000000), (-1063329781377571300029695469677/5629499534213120000000000000000000), (50257415290506613963738537863/1407374883553280000000000000000000), (30138359687630345677318150437/11258999068426240000000000000000000), (-1932989636939251444755334991/5629499534213120000000000000000000), (-33795168544968909232130377/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial141.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial141.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial141.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial141.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial141 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial141 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial141 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 14772853531293005910588902128339439), (Int.ofNat 139691978667589087257405849896071), (Int.ofNat 1107664966003620372752163202035250), (Int.negOfNat 122909437214745695117630164019127), (Int.negOfNat 28788266400923037521281588732481), (Int.ofNat 3334133567858918247230435469907), (Int.ofNat 429781422706168374209146439257), (Int.negOfNat 44888501120167417219521685437), (Int.negOfNat 4086482113521703995536614342), (Int.ofNat 372935172912002303220336946), (Int.ofNat 26633456901008331181495597), (Int.negOfNat 2123182261110864033815802), (Int.negOfNat 126257165159279511610351), (Int.ofNat 8848804118406173705401), (Int.ofNat 454863733821360144955), (Int.negOfNat 28069608468910111005), (Int.negOfNat 1276155353874830312), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-14772853531293005910588902128339439/11258999068426240000000000000000000), (139691978667589087257405849896071/11258999068426240000000000000000000), (4430659864014481491008652808141/45035996273704960000000000000000), (-122909437214745695117630164019127/11258999068426240000000000000000000), (-28788266400923037521281588732481/11258999068426240000000000000000000), (3334133567858918247230435469907/11258999068426240000000000000000000), (429781422706168374209146439257/11258999068426240000000000000000000), (-44888501120167417219521685437/11258999068426240000000000000000000), (-2043241056760851997768307171/5629499534213120000000000000000000), (186467586456001151610168473/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial141.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial141.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial141.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 11379077623415943642745058175690507), (Int.ofNat 2500137287107973050317727831623082), (Int.ofNat 13638665070989208501159516377563), (Int.negOfNat 181232776701236906960396782585063), (Int.ofNat 14953879294591904296850008725385), (Int.ofNat 3784450216437870304822531493470), (Int.negOfNat 352885450656388076102828143513), (Int.negOfNat 44292346876022631273284750961), (Int.ofNat 4043239045424362596948090411), (Int.ofNat 336257016486558541129873651), (Int.negOfNat 29043074384866498883959802), (Int.negOfNat 1798758342972362661303135), (Int.ofNat 145660029424034682305525), (Int.ofNat 7178590931282047525267), (Int.negOfNat 543462718668284216928), (Int.negOfNat 22010200671352864443), (Int.ofNat 1676395207637037382), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-11379077623415943642745058175690507/11258999068426240000000000000000000), (1250068643553986525158863915811541/5629499534213120000000000000000000), (13638665070989208501159516377563/11258999068426240000000000000000000), (-181232776701236906960396782585063/11258999068426240000000000000000000), (2990775858918380859370001745077/2251799813685248000000000000000000), (378445021643787030482253149347/1125899906842624000000000000000000), (-352885450656388076102828143513/11258999068426240000000000000000000), (-44292346876022631273284750961/11258999068426240000000000000000000), (4043239045424362596948090411/11258999068426240000000000000000000), (336257016486558541129873651/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial141.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial141.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial141.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 7440825761394784548396596806959668), (Int.ofNat 1078331750076998249502110027721785), (Int.negOfNat 518145339881350436772530120468452), (Int.ofNat 17060071590269211213077546137171), (Int.ofNat 24661774273646406646756773101120), (Int.negOfNat 1952334750049348902954655997878), (Int.negOfNat 408618632264143822360889522324), (Int.ofNat 35656374213568629023609174017), (Int.ofNat 3825950523061500759585183398), (Int.negOfNat 341238023921119599534553073), (Int.negOfNat 23679316516275618443931672), (Int.ofNat 2115671276325838557199233), (Int.ofNat 105433863937537762019150), (Int.negOfNat 9352841057509931904200), (Int.negOfNat 356733794634200983445), (Int.ofNat 31080082295300210557), (Int.ofNat 832424377229300099), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-1860206440348696137099149201739917/2814749767106560000000000000000000), (215666350015399649900422005544357/2251799813685248000000000000000000), (-129536334970337609193132530117113/2814749767106560000000000000000000), (17060071590269211213077546137171/11258999068426240000000000000000000), (77068044605145020771114915941/35184372088832000000000000000000), (-976167375024674451477327998939/5629499534213120000000000000000000), (-102154658066035955590222380581/2814749767106560000000000000000000), (35656374213568629023609174017/11258999068426240000000000000000000), (1912975261530750379792591699/5629499534213120000000000000000000), (-341238023921119599534553073/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial141.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial141.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial141.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 6908951783017019476597351298175011), (Int.negOfNat 215983261282233473587330972284074), (Int.negOfNat 49120498878945528133846100679414), (Int.ofNat 95605656344537647383101858401012), (Int.negOfNat 6704933653813500395347337583531), (Int.negOfNat 2955582984626446598104910625710), (Int.ofNat 245472748318170052156092188353), (Int.ofNat 37715455041503133229711794418), (Int.negOfNat 3376860482813009981628433748), (Int.negOfNat 282811017835569332001769934), (Int.ofNat 26857225215007271314188789), (Int.ofNat 1434449430982595242231833), (Int.negOfNat 143684166117968367723672), (Int.negOfNat 5322114462068932905606), (Int.ofNat 560091454717787078012), (Int.ofNat 14559571981568359028), (Int.negOfNat 1718169894848188903), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-6908951783017019476597351298175011/11258999068426240000000000000000000), (-107991630641116736793665486142037/5629499534213120000000000000000000), (-24560249439472764066923050339707/5629499534213120000000000000000000), (23901414086134411845775464600253/2814749767106560000000000000000000), (-6704933653813500395347337583531/11258999068426240000000000000000000), (-295558298462644659810491062571/1125899906842624000000000000000000), (245472748318170052156092188353/11258999068426240000000000000000000), (18857727520751566614855897209/5629499534213120000000000000000000), (-844215120703252495407108437/2814749767106560000000000000000000), (-141405508917784666000884967/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial141.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial141.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial141.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 6954854268714217873710938297206701), (Int.ofNat 343865812582121475565891089914512), (Int.ofNat 204391557800424493700291240535577), (Int.negOfNat 22976750927345044275998239659154), (Int.negOfNat 15492448995280408724830027102024), (Int.ofNat 1318483885627084789718327491925), (Int.ofNat 307468290669672672193446245344), (Int.negOfNat 27647419481112196778676020032), (Int.negOfNat 2982438433868255526486590814), (Int.ofNat 294332109628756726832729278), (Int.ofNat 17839193680006195220133571), (Int.negOfNat 1956037384751479330510175), (Int.negOfNat 73556762862622099939341), (Int.ofNat 9052392710294699056825), (Int.ofNat 222955784777274687094), (Int.negOfNat 31557947351967304771), (Int.negOfNat 374768504846719379), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-6954854268714217873710938297206701/11258999068426240000000000000000000), (21491613286382592222868193119657/703687441776640000000000000000000), (204391557800424493700291240535577/11258999068426240000000000000000000), (-11488375463672522137999119829577/5629499534213120000000000000000000), (-1936556124410051090603753387753/1407374883553280000000000000000000), (52739355425083391588733099677/450359962737049600000000000000000), (9608384083427271006045195167/351843720888320000000000000000000), (-431990929392378074666812813/175921860444160000000000000000000), (-1491219216934127763243295407/5629499534213120000000000000000000), (147166054814378363416364639/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial141.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial141.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial141.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 5823517787806047035745002442572947), (Int.ofNat 539771363585632353647704912068150), (Int.negOfNat 148436980451893421467638043701216), (Int.negOfNat 64040956984647870862587506964007), (Int.ofNat 6396893386861408546868821667067), (Int.ofNat 2024636120580612022958069284905), (Int.negOfNat 187087963071541724803177756387), (Int.negOfNat 27009633705055614622663187156), (Int.ofNat 2751418808504148810609491505), (Int.ofNat 198965734174504939535596578), (Int.negOfNat 23377323060565636973703735), (Int.negOfNat 933823762820761567036951), (Int.ofNat 130982625949821051712076), (Int.ofNat 3011075095362766135688), (Int.negOfNat 526278239336329771411), (Int.negOfNat 6928318214395768393), (Int.ofNat 1759944582059340424), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-5823517787806047035745002442572947/11258999068426240000000000000000000), (10795427271712647072954098241363/225179981368524800000000000000000), (-4638655639121669420863688865663/351843720888320000000000000000000), (-64040956984647870862587506964007/11258999068426240000000000000000000), (6396893386861408546868821667067/11258999068426240000000000000000000), (404927224116122404591613856981/2251799813685248000000000000000000), (-187087963071541724803177756387/11258999068426240000000000000000000), (-6752408426263903655665796789/2814749767106560000000000000000000), (550283761700829762121898301/2251799813685248000000000000000000), (99482867087252469767798289/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial141.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial141.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial141.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 5697561915765792014506731420695816), (Int.negOfNat 500668791200120872205443310862255), (Int.negOfNat 274677068532638219504854989416984), (Int.ofNat 28677065972616482405548578707618), (Int.ofNat 11402616223345982725240207680646), (Int.negOfNat 1057879720562266848604170447080), (Int.negOfNat 207714271848721597378437388141), (Int.ofNat 21708467718626041412055950818), (Int.ofNat 1952053918772162781124130483), (Int.negOfNat 242650303667478841584710420), (Int.negOfNat 10738739241090286134334470), (Int.ofNat 1683251414551849343678162), (Int.ofNat 37004430476060644181185), (Int.negOfNat 8025101639329093615337), (Int.negOfNat 77104441820905940841), (Int.ofNat 28293216248319955101), (Int.negOfNat 82887367535861341), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-712195239470724001813341427586977/1407374883553280000000000000000000), (-100133758240024174441088662172451/2251799813685248000000000000000000), (-34334633566579777438106873677123/1407374883553280000000000000000000), (14338532986308241202774289353809/5629499534213120000000000000000000), (5701308111672991362620103840323/5629499534213120000000000000000000), (-26446993014056671215104261177/281474976710656000000000000000000), (-207714271848721597378437388141/11258999068426240000000000000000000), (10854233859313020706027975409/5629499534213120000000000000000000), (1952053918772162781124130483/11258999068426240000000000000000000), (-12132515183373942079235521/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial141.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial141.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial141.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 7429748540379150327557591595227676), (Int.negOfNat 1003750384043077326048354339575347), (Int.ofNat 53459256166641291958163072478529), (Int.ofNat 58606823329854775346271709274841), (Int.negOfNat 4424210716805538702579947555264), (Int.negOfNat 1377316533191712821907092686614), (Int.ofNat 141012912044337935467576407671), (Int.ofNat 16645660480976580324673759079), (Int.negOfNat 2156630661600598280186517005), (Int.negOfNat 110115583656192432652502865), (Int.ofNat 19012877883877761071960171), (Int.ofNat 408344694765631750650897), (Int.negOfNat 109463418690561763237684), (Int.negOfNat 673174303463418972357), (Int.ofNat 446805462084685479756), (Int.negOfNat 1478087783991149692), (Int.negOfNat 1649167311809631705), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-1857437135094787581889397898806919/2814749767106560000000000000000000), (-1003750384043077326048354339575347/11258999068426240000000000000000000), (53459256166641291958163072478529/11258999068426240000000000000000000), (58606823329854775346271709274841/11258999068426240000000000000000000), (-69128292450086542227811680551/175921860444160000000000000000000), (-688658266595856410953546343307/5629499534213120000000000000000000), (141012912044337935467576407671/11258999068426240000000000000000000), (16645660480976580324673759079/11258999068426240000000000000000000), (-431326132320119656037303401/2251799813685248000000000000000000), (-22023116731238486530500573/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial141.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial141.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial141.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 8858852344608400764666585877157313), (Int.negOfNat 306222636297398556279921631052949), (Int.ofNat 229613889180298338271300799553628), (Int.negOfNat 4155467078745042346565988852097), (Int.negOfNat 7676119394405326410325883013605), (Int.ofNat 679428612475929083619726959187), (Int.ofNat 122141250442802817006362450771), (Int.negOfNat 15969798141468169195922096489), (Int.negOfNat 991263681258223195353268945), (Int.ofNat 186046575477740405156144115), (Int.ofNat 3969100413750385905066061), (Int.negOfNat 1322670804796970719655007), (Int.negOfNat 2751632420516521148254), (Int.ofNat 6399751209085849278137), (Int.negOfNat 54717953364518221034), (Int.negOfNat 22961015831051688068), (Int.ofNat 415841073931682835), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-8858852344608400764666585877157313/11258999068426240000000000000000000), (-306222636297398556279921631052949/11258999068426240000000000000000000), (57403472295074584567825199888407/2814749767106560000000000000000000), (-4155467078745042346565988852097/11258999068426240000000000000000000), (-1535223878881065282065176602721/2251799813685248000000000000000000), (679428612475929083619726959187/11258999068426240000000000000000000), (122141250442802817006362450771/11258999068426240000000000000000000), (-15969798141468169195922096489/11258999068426240000000000000000000), (-198252736251644639070653789/2251799813685248000000000000000000), (37209315095548081031228823/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial141.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial141.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial141.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 8681546198540887239337075674012824), (Int.ofNat 386801716432733733543543903700089), (Int.ofNat 92480939084273585162154105674129), (Int.negOfNat 28557343510829701057978199365460), (Int.ofNat 1614376231401123916095294592892), (Int.ofNat 729250841284869882402042771270), (Int.negOfNat 92505168463999997752016588521), (Int.negOfNat 7637737246090237801218391888), (Int.ofNat 1540538528594489053676258793), (Int.ofNat 32904132277536133926325940), (Int.negOfNat 13954118606258169347369060), (Int.ofNat 43883023287406212755338), (Int.ofNat 81305182136354960656455), (Int.negOfNat 1290245216261370333803), (Int.negOfNat 333483136070872312641), (Int.ofNat 7873691872365907609), (Int.ofNat 1371913188362012239), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-1085193274817610904917134459251603/1407374883553280000000000000000000), (386801716432733733543543903700089/11258999068426240000000000000000000), (92480939084273585162154105674129/11258999068426240000000000000000000), (-1427867175541485052898909968273/562949953421312000000000000000000), (403594057850280979023823648223/2814749767106560000000000000000000), (72925084128486988240204277127/1125899906842624000000000000000000), (-92505168463999997752016588521/11258999068426240000000000000000000), (-477358577880639862576149493/703687441776640000000000000000000), (1540538528594489053676258793/11258999068426240000000000000000000), (1645206613876806696316297/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial141.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial141.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial141.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 7723812329015239254002562779609017), (Int.ofNat 504439024061025588275973214310200), (Int.negOfNat 6353900503682286787996470225429), (Int.negOfNat 2816653566561838006098321056588), (Int.ofNat 2899908121255669415055714499515), (Int.negOfNat 369606293515481574193267290645), (Int.negOfNat 46723178292198005392524680447), (Int.ofNat 10375207402010858758233341556), (Int.ofNat 214990621028538975809040845), (Int.negOfNat 125801692907621933630351138), (Int.ofNat 1358910882564087011120105), (Int.ofNat 903581420059144466455331), (Int.negOfNat 23453604439603982347734), (Int.negOfNat 4364190709214844412888), (Int.ofNat 153293335557800437739), (Int.ofNat 14911686372837151973), (Int.negOfNat 610167718603694596), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-7723812329015239254002562779609017/11258999068426240000000000000000000), (2522195120305127941379866071551/56294995342131200000000000000000), (-6353900503682286787996470225429/11258999068426240000000000000000000), (-704163391640459501524580264147/2814749767106560000000000000000000), (579981624251133883011142899903/2251799813685248000000000000000000), (-73921258703096314838653458129/2251799813685248000000000000000000), (-46723178292198005392524680447/11258999068426240000000000000000000), (2593801850502714689558335389/2814749767106560000000000000000000), (42998124205707795161808169/2251799813685248000000000000000000), (-62900846453810966815175569/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial141.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial141.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial141.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 6729980499428681807695682116362026), (Int.ofNat 504076029283370822512366607900822), (Int.ofNat 12378500948385907006270640066715), (Int.ofNat 3696979666763566285393581257330), (Int.negOfNat 908875354904244495516540078837), (Int.negOfNat 182010776618498734510507332992), (Int.ofNat 53799273397212080722912437504), (Int.ofNat 789203312949671673852590622), (Int.negOfNat 938173138343038153109863144), (Int.ofNat 22507733345156636564874412), (Int.ofNat 8573456022714979884043741), (Int.negOfNat 354075058950125410815545), (Int.negOfNat 49496170098919636738601), (Int.ofNat 2573250900928939655885), (Int.ofNat 198756132954612798144), (Int.negOfNat 12127935797443662579), (Int.negOfNat 914257315979431519), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-3364990249714340903847841058181013/5629499534213120000000000000000000), (252038014641685411256183303950411/5629499534213120000000000000000000), (2475700189677181401254128013343/2251799813685248000000000000000000), (369697966676356628539358125733/1125899906842624000000000000000000), (-908875354904244495516540078837/11258999068426240000000000000000000), (-1421959192332021363363338539/87960930222080000000000000000000), (210153411707859690323876709/43980465111040000000000000000000), (394601656474835836926295311/5629499534213120000000000000000000), (-117271642292879769138732893/1407374883553280000000000000000000), (5626933336289159141218603/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial141.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial141.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial141.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 5659781551854468451896606351151053), (Int.ofNat 564121955721076629123664849908982), (Int.ofNat 10137112260323585997449795769703), (Int.negOfNat 3252786848331115517600050567666), (Int.negOfNat 144944372281150352268572705539), (Int.ofNat 209607950850748655640644146430), (Int.negOfNat 3772989290005128656142697740), (Int.negOfNat 5526094389781735963685973508), (Int.ofNat 283788703763233901413833012), (Int.ofNat 66735093649598832458728574), (Int.negOfNat 4550402884590724840216871), (Int.negOfNat 468443419943962608461933), (Int.ofNat 37875624479517867013128), (Int.ofNat 2168393164478969731116), (Int.negOfNat 201303007813116743948), (Int.negOfNat 6677536564080277648), (Int.ofNat 651942405814846117), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-5659781551854468451896606351151053/11258999068426240000000000000000000), (282060977860538314561832424954491/5629499534213120000000000000000000), (10137112260323585997449795769703/11258999068426240000000000000000000), (-1626393424165557758800025283833/5629499534213120000000000000000000), (-144944372281150352268572705539/11258999068426240000000000000000000), (20960795085074865564064414643/1125899906842624000000000000000000), (-188649464500256432807134887/562949953421312000000000000000000), (-1381523597445433990921493377/2814749767106560000000000000000000), (70947175940808475353458253/2814749767106560000000000000000000), (33367546824799416229364287/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial141.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial141.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial141.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 4513470584382213023535211758254476), (Int.ofNat 574984078970203017487716329764366), (Int.ofNat 44588397403935735445960915912), (Int.ofNat 1056062150237824264221426383530), (Int.ofNat 688796468215191578769481377254), (Int.negOfNat 84397686015601306446039798565), (Int.negOfNat 24173717702101656604003824764), (Int.ofNat 2884886480361822562176103373), (Int.ofNat 394830774171912946408901068), (Int.negOfNat 49911949760565623796563547), (Int.negOfNat 3405196292069498101707952), (Int.ofNat 484785439899036348276597), (Int.ofNat 17824818784535060035150), (Int.negOfNat 3005382596825878250010), (Int.negOfNat 61606439142942326415), (Int.ofNat 13240506182355973823), (Int.ofNat 456601443596850799), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-1128367646095553255883802939563619/2814749767106560000000000000000000), (287492039485101508743858164882183/5629499534213120000000000000000000), (5573549675491966930745114489/1407374883553280000000000000000000), (105606215023782426422142638353/1125899906842624000000000000000000), (344398234107595789384740688627/5629499534213120000000000000000000), (-16879537203120261289207959713/2251799813685248000000000000000000), (-6043429425525414151000956191/2814749767106560000000000000000000), (2884886480361822562176103373/11258999068426240000000000000000000), (98707693542978236602225267/2814749767106560000000000000000000), (-49911949760565623796563547/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial141.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial141.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial141.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 3347660335071332246388485323907144), (Int.ofNat 600053535674629593880684152826383), (Int.ofNat 12749892412026513547979013453295), (Int.ofNat 1346758171293119488726460311546), (Int.negOfNat 581025793692258330795100840917), (Int.negOfNat 68221217014399057203062367910), (Int.ofNat 23000834597399759383483998997), (Int.ofNat 1421737370655589665244041791), (Int.negOfNat 460320523045062262771924779), (Int.negOfNat 14183967598770296062413731), (Int.ofNat 5327906185340135372108528), (Int.ofNat 68111678432603601902935), (Int.negOfNat 39044932461441376987715), (Int.negOfNat 99000738546658690307), (Int.ofNat 195944399194836611992), (Int.negOfNat 1127030492221240937), (Int.negOfNat 693717093025997638), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-418457541883916530798560665488393/1407374883553280000000000000000000), (600053535674629593880684152826383/11258999068426240000000000000000000), (2549978482405302709595802690659/2251799813685248000000000000000000), (673379085646559744363230155773/5629499534213120000000000000000000), (-581025793692258330795100840917/11258999068426240000000000000000000), (-6822121701439905720306236791/1125899906842624000000000000000000), (23000834597399759383483998997/11258999068426240000000000000000000), (1421737370655589665244041791/11258999068426240000000000000000000), (-460320523045062262771924779/11258999068426240000000000000000000), (-14183967598770296062413731/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial141.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial141.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial141.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 2095724751114967471746127113838452), (Int.ofNat 647739834370422551956376231564320), (Int.ofNat 7074190870144942305127171647616), (Int.negOfNat 2374709200168704606528914200845), (Int.ofNat 11844080094473491809539021008), (Int.ofNat 133576527985358683574339748126), (Int.negOfNat 1460831001028160658070266173), (Int.negOfNat 3430787958394574141551125533), (Int.ofNat 54918845736900455249107748), (Int.ofNat 48886149940487622169965594), (Int.negOfNat 965415932241378635109083), (Int.negOfNat 432213306709970704337098), (Int.ofNat 9559397088711414169539), (Int.ofNat 2565491802532630404149), (Int.negOfNat 58910954434964047915), (Int.negOfNat 11044337505905373475), (Int.ofNat 14979324522780428), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-523931187778741867936531778459613/2814749767106560000000000000000000), (4048373964815140949727351447277/70368744177664000000000000000000), (55267116173007361758806028497/87960930222080000000000000000000), (-474941840033740921305782840169/2251799813685248000000000000000000), (740255005904593238096188813/703687441776640000000000000000000), (66788263992679341787169874063/5629499534213120000000000000000000), (-1460831001028160658070266173/11258999068426240000000000000000000), (-3430787958394574141551125533/11258999068426240000000000000000000), (13729711434225113812276937/2814749767106560000000000000000000), (24443074970243811084982797/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial141.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial141.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial141.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 786977398331935234004844940100404), (Int.ofNat 656947169058554164530501608293138), (Int.ofNat 1441640932189694331719320976843), (Int.ofNat 1238036034923166991598943462659), (Int.ofNat 528786245995462811711018813967), (Int.negOfNat 67823772454178772733878305097), (Int.negOfNat 19065346270150112505135390497), (Int.ofNat 1760539220821087866713171597), (Int.ofNat 352697701795555929500170012), (Int.negOfNat 26090816618312025691461256), (Int.negOfNat 3878939069196734153341747), (Int.ofNat 244560331698967915533062), (Int.ofNat 27823012868875777408651), (Int.negOfNat 1550945134102792305551), (Int.negOfNat 139263271715463566735), (Int.ofNat 7620167145964434445), (Int.ofNat 416462969578378172), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-196744349582983808501211235025101/2814749767106560000000000000000000), (328473584529277082265250804146569/5629499534213120000000000000000000), (1441640932189694331719320976843/11258999068426240000000000000000000), (1238036034923166991598943462659/11258999068426240000000000000000000), (528786245995462811711018813967/11258999068426240000000000000000000), (-67823772454178772733878305097/11258999068426240000000000000000000), (-19065346270150112505135390497/11258999068426240000000000000000000), (1760539220821087866713171597/11258999068426240000000000000000000), (88174425448888982375042503/2814749767106560000000000000000000), (-3261352077289003211432657/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial141.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial141.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial141.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 547956738044971427284176916394683), (Int.ofNat 686478129326953056736007243354343), (Int.ofNat 13217821440094774012698248808259), (Int.ofNat 1135932643039959272066504729777), (Int.negOfNat 549562424229119583139062473914), (Int.negOfNat 65169250482133672790651062990), (Int.ofNat 19352900731316319676055059723), (Int.ofNat 1701836644389216116091002021), (Int.negOfNat 355463389449195862888390681), (Int.negOfNat 24734750453677957174249551), (Int.ofNat 3933815832221042506778152), (Int.ofNat 224575229944032988082835), (Int.negOfNat 28667611755640220948605), (Int.negOfNat 1375530909673694203437), (Int.ofNat 146395593868280483098), (Int.ofNat 6643215513511048603), (Int.negOfNat 347933030918601922), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(547956738044971427284176916394683/11258999068426240000000000000000000), (686478129326953056736007243354343/11258999068426240000000000000000000), (13217821440094774012698248808259/11258999068426240000000000000000000), (1135932643039959272066504729777/11258999068426240000000000000000000), (-274781212114559791569531236957/5629499534213120000000000000000000), (-6516925048213367279065106299/1125899906842624000000000000000000), (19352900731316319676055059723/11258999068426240000000000000000000), (1701836644389216116091002021/11258999068426240000000000000000000), (-355463389449195862888390681/11258999068426240000000000000000000), (-24734750453677957174249551/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial141.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial141.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial141.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1973350448724594579893664395239103), (Int.ofNat 734260176404677164626095834051941), (Int.ofNat 6717284061075591578590271476713), (Int.negOfNat 2521413850077300018100873650782), (Int.negOfNat 3033953974622421567156798873), (Int.ofNat 136072931038945526545938617618), (Int.ofNat 1408100107140752813201369724), (Int.negOfNat 3392178895427444442107128537), (Int.negOfNat 48787884454396292185819508), (Int.ofNat 47569037528778657370826103), (Int.ofNat 769167561233991545953492), (Int.negOfNat 420305764220071758852323), (Int.negOfNat 7054496136630340704650), (Int.ofNat 2523495075273195609190), (Int.ofNat 41928243340269797155), (Int.negOfNat 11033617724629179397), (Int.ofNat 27268007067152041), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(1973350448724594579893664395239103/11258999068426240000000000000000000), (734260176404677164626095834051941/11258999068426240000000000000000000), (6717284061075591578590271476713/11258999068426240000000000000000000), (-1260706925038650009050436825391/5629499534213120000000000000000000), (-3033953974622421567156798873/11258999068426240000000000000000000), (68036465519472763272969308809/5629499534213120000000000000000000), (352025026785188203300342431/2814749767106560000000000000000000), (-3392178895427444442107128537/11258999068426240000000000000000000), (-12196971113599073046454877/2814749767106560000000000000000000), (47569037528778657370826103/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial141.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial141.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial141.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3452542121605423888671683052328789), (Int.ofNat 740470560639313453077473902394423), (Int.ofNat 588948012042364402208116567241), (Int.ofNat 1385226554605147847933178750492), (Int.ofNat 622152947513084455640982579603), (Int.negOfNat 64030523688677087064285797560), (Int.negOfNat 23068644862761750425130321343), (Int.ofNat 1294933710437152118767236432), (Int.ofNat 438152716845650919528957118), (Int.negOfNat 13883149289994601049724466), (Int.negOfNat 4937769575531573107514269), (Int.ofNat 86547163828031606148717), (Int.ofNat 36198508967835408173352), (Int.negOfNat 324846895719249671464), (Int.negOfNat 184088478879671274142), (Int.ofNat 404436423998811412), (Int.ofNat 389707718129753443), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(3452542121605423888671683052328789/11258999068426240000000000000000000), (740470560639313453077473902394423/11258999068426240000000000000000000), (588948012042364402208116567241/11258999068426240000000000000000000), (346306638651286961983294687623/2814749767106560000000000000000000), (622152947513084455640982579603/11258999068426240000000000000000000), (-1600763092216927176607144939/281474976710656000000000000000000), (-23068644862761750425130321343/11258999068426240000000000000000000), (80933356902322007422952277/703687441776640000000000000000000), (219076358422825459764478559/5629499534213120000000000000000000), (-6941574644997300524862233/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial141.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial141.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial141.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4953615998572088975183381940782836), (Int.ofNat 770779701092615150918375176216234), (Int.ofNat 14712334936186844390879278151881), (Int.ofNat 1477603807190167663285174817808), (Int.negOfNat 663356803555407840803812766446), (Int.negOfNat 97652945419766898163605297818), (Int.ofNat 21427631835487203614329329836), (Int.ofNat 2828773505599751570090205442), (Int.negOfNat 345649906298971179402677956), (Int.negOfNat 44232221919680066673009948), (Int.ofNat 3223773894357191721180589), (Int.ofNat 420237900069536390934645), (Int.negOfNat 19139716741822101401509), (Int.negOfNat 2635281050170832511225), (Int.ofNat 77543060192535997656), (Int.ofNat 11914459533570919011), (Int.negOfNat 484923879449732761), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(1238403999643022243795845485195709/2814749767106560000000000000000000), (385389850546307575459187588108117/5629499534213120000000000000000000), (14712334936186844390879278151881/11258999068426240000000000000000000), (92350237949385478955323426113/703687441776640000000000000000000), (-331678401777703920401906383223/5629499534213120000000000000000000), (-48826472709883449081802648909/5629499534213120000000000000000000), (5356907958871800903582332459/2814749767106560000000000000000000), (1414386752799875785045102721/5629499534213120000000000000000000), (-86412476574742794850669489/2814749767106560000000000000000000), (-11058055479920016668252487/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial141.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial141.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial141.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 6553733349462593605426547765712067), (Int.ofNat 823266812663255592065483126592590), (Int.ofNat 6112795204295434748607297178430), (Int.negOfNat 3515612745685108139634207628898), (Int.negOfNat 69845949037319835932147591086), (Int.ofNat 188798321289154876451586728448), (Int.ofNat 8014395964315876880188659687), (Int.negOfNat 4480617124842886352404341604), (Int.negOfNat 243624556219357309240867085), (Int.ofNat 57017331885450073379062122), (Int.ofNat 3547345245277753481457045), (Int.negOfNat 439241752166091663646919), (Int.negOfNat 30049139363041925459636), (Int.ofNat 2240532222433968078032), (Int.ofNat 166220380256273212521), (Int.negOfNat 7632713438896756647), (Int.negOfNat 431482405340904964), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(6553733349462593605426547765712067/11258999068426240000000000000000000), (82326681266325559206548312659259/1125899906842624000000000000000000), (611279520429543474860729717843/1125899906842624000000000000000000), (-1757806372842554069817103814449/5629499534213120000000000000000000), (-34922974518659917966073795543/5629499534213120000000000000000000), (368746721267880618069505329/21990232555520000000000000000000), (8014395964315876880188659687/11258999068426240000000000000000000), (-1120154281210721588101085401/2814749767106560000000000000000000), (-48724911243871461848173417/2251799813685248000000000000000000), (28508665942725036689531061/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial141.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial141.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial141.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 8201426122675417575780545148073858), (Int.ofNat 817825392132719002805658647324001), (Int.negOfNat 2787800223278922674304778348810), (Int.ofNat 2153971193590472339323323971504), (Int.ofNat 1027740761605334940437146175040), (Int.negOfNat 72147470722793493320334382657), (Int.negOfNat 39442005820076070995036965289), (Int.ofNat 458867639740395514741295962), (Int.ofNat 719090500044307042918174907), (Int.ofNat 11326729720213644207599740), (Int.negOfNat 7306602237570407046524940), (Int.negOfNat 222569767473931275588192), (Int.ofNat 46327904499293555055625), (Int.ofNat 1814771861762429420807), (Int.negOfNat 201463198012463569309), (Int.negOfNat 9313435649546707411), (Int.ofNat 942579751832313481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(4100713061337708787890272574036929/5629499534213120000000000000000000), (817825392132719002805658647324001/11258999068426240000000000000000000), (-278780022327892267430477834881/1125899906842624000000000000000000), (134623199599404521207707748219/703687441776640000000000000000000), (3211689880016671688866081797/35184372088832000000000000000000), (-72147470722793493320334382657/11258999068426240000000000000000000), (-39442005820076070995036965289/11258999068426240000000000000000000), (229433819870197757370647981/5629499534213120000000000000000000), (719090500044307042918174907/11258999068426240000000000000000000), (566336486010682210379987/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial141.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial141.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial141.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 9855009205151184327590239898082189), (Int.ofNat 852994198733142350799497944371136), (Int.ofNat 21125988824420490814083825545450), (Int.ofNat 2669701456949095340544552384212), (Int.negOfNat 1182014101150280759078136298427), (Int.negOfNat 222354247618953043191404155306), (Int.ofNat 30257287431515873637160178449), (Int.ofNat 6680133929107347938890158861), (Int.negOfNat 288116905525783238572591455), (Int.negOfNat 96194521207085138192858285), (Int.ofNat 468078756292219142132769), (Int.ofNat 777904961555861326214113), (Int.ofNat 9876001574003356789514), (Int.negOfNat 4083581424316272237923), (Int.negOfNat 91117974727512965196), (Int.ofNat 15233165932734383932), (Int.ofNat 320705135091196245), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(9855009205151184327590239898082189/11258999068426240000000000000000000), (13328034355205349231242155380799/175921860444160000000000000000000), (422519776488409816281676510909/225179981368524800000000000000000), (667425364237273835136138096053/2814749767106560000000000000000000), (-1182014101150280759078136298427/11258999068426240000000000000000000), (-111177123809476521595702077653/5629499534213120000000000000000000), (30257287431515873637160178449/11258999068426240000000000000000000), (6680133929107347938890158861/11258999068426240000000000000000000), (-57623381105156647714518291/2251799813685248000000000000000000), (-19238904241417027638571657/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial141.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial141.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial141.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 11643502200529307793690067156108950), (Int.ofNat 922218393361137894344247887349815), (Int.ofNat 1806041379519352547552211898463), (Int.negOfNat 8092060778000811429339460136260), (Int.negOfNat 391371379196008731803922931324), (Int.ofNat 405247505994799087110758666053), (Int.ofNat 39599120697476669273969371869), (Int.negOfNat 7436509743210728925485622971), (Int.negOfNat 1002581010605333077384418455), (Int.ofNat 54367432176793464965884225), (Int.ofNat 10958105853643640277681419), (Int.negOfNat 168351861907437109528793), (Int.negOfNat 70832330812642466619206), (Int.negOfNat 129426989238441016547), (Int.ofNat 310639497865243513904), (Int.ofNat 3981235232278440378), (Int.negOfNat 1275533458228134975), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(232870044010586155873801343122179/225179981368524800000000000000000), (184443678672227578868849577469963/2251799813685248000000000000000000), (1806041379519352547552211898463/11258999068426240000000000000000000), (-404603038900040571466973006813/562949953421312000000000000000000), (-97842844799002182950980732831/2814749767106560000000000000000000), (405247505994799087110758666053/11258999068426240000000000000000000), (39599120697476669273969371869/11258999068426240000000000000000000), (-7436509743210728925485622971/11258999068426240000000000000000000), (-200516202121066615476883691/2251799813685248000000000000000000), (2174697287071738598635369/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial141.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial141.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial141.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 13438496880811141463685718494718332), (Int.ofNat 855656337871614518436972312513397), (Int.negOfNat 20642275653126096404033590917002), (Int.ofNat 5807359306364242635841632861542), (Int.ofNat 3182610835650427809849991329132), (Int.negOfNat 7295627658174877709062369807), (Int.negOfNat 109913101464158555305592507209), (Int.negOfNat 7690891615384560110831784812), (Int.ofNat 1219263062125804312784186377), (Int.ofNat 129899018508315061016316220), (Int.negOfNat 6948350426541842702033940), (Int.negOfNat 1069434659325397053998238), (Int.ofNat 22249033773610254788135), (Int.ofNat 5616489169544051397993), (Int.negOfNat 29876462792442236509), (Int.negOfNat 21628770021109141849), (Int.negOfNat 43451011643576779), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(3359624220202785365921429623679583/2814749767106560000000000000000000), (855656337871614518436972312513397/11258999068426240000000000000000000), (-10321137826563048202016795458501/5629499534213120000000000000000000), (2903679653182121317920816430771/5629499534213120000000000000000000), (795652708912606952462497832283/2814749767106560000000000000000000), (-7295627658174877709062369807/11258999068426240000000000000000000), (-109913101464158555305592507209/11258999068426240000000000000000000), (-1922722903846140027707946203/2814749767106560000000000000000000), (1219263062125804312784186377/11258999068426240000000000000000000), (6494950925415753050815811/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial141.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial141.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial141.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 15156738239326397770411444019418387), (Int.ofNat 920987636701022346914430995114510), (Int.ofNat 61129171536670677483828029677405), (Int.ofNat 11818871085894486652499726071853), (Int.negOfNat 3883027179893782767017771352403), (Int.negOfNat 1247823787169088107212381464585), (Int.negOfNat 30420481225949246756814324123), (Int.ofNat 19338938168715064895045409254), (Int.ofNat 1279846727291384919609919785), (Int.negOfNat 149378838412997446993236222), (Int.negOfNat 14153088382251600699618445), (Int.ofNat 705515260629120901040619), (Int.ofNat 90218414620026631712974), (Int.negOfNat 2183115195754926837802), (Int.negOfNat 393234045047996617059), (Int.ofNat 4328824693284588387), (Int.ofNat 1469860102900146736), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(15156738239326397770411444019418387/11258999068426240000000000000000000), (92098763670102234691443099511451/1125899906842624000000000000000000), (12225834307334135496765605935481/2251799813685248000000000000000000), (11818871085894486652499726071853/11258999068426240000000000000000000), (-3883027179893782767017771352403/11258999068426240000000000000000000), (-249564757433817621442476292917/2251799813685248000000000000000000), (-30420481225949246756814324123/11258999068426240000000000000000000), (9669469084357532447522704627/5629499534213120000000000000000000), (255969345458276983921983957/2251799813685248000000000000000000), (-74689419206498723496618111/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial141.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial141.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial141.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 17236489301146632453663597515105564), (Int.ofNat 1086975049972298221241672598697564), (Int.negOfNat 53813726654965277279815894147953), (Int.negOfNat 61883691641490254187844511800536), (Int.negOfNat 12090623216042383004477553763123), (Int.ofNat 198603157897638276863773114329), (Int.ofNat 250735497479917904017975402333), (Int.ofNat 10332445945279532228742320388), (Int.negOfNat 2468604989525106023568723926), (Int.negOfNat 165451339603783461070678202), (Int.ofNat 14919130954948460799273369), (Int.ofNat 1301641660582401611065865), (Int.negOfNat 61268106976852990083299), (Int.negOfNat 6657756087805727963425), (Int.ofNat 180168186623670798096), (Int.ofNat 24816329974289113349), (Int.negOfNat 414204860739003941), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(4309122325286658113415899378776391/2814749767106560000000000000000000), (271743762493074555310418149674391/2814749767106560000000000000000000), (-53813726654965277279815894147953/11258999068426240000000000000000000), (-7735461455186281773480563975067/1407374883553280000000000000000000), (-12090623216042383004477553763123/11258999068426240000000000000000000), (198603157897638276863773114329/11258999068426240000000000000000000), (250735497479917904017975402333/11258999068426240000000000000000000), (2583111486319883057185580097/2814749767106560000000000000000000), (-1234302494762553011784361963/5629499534213120000000000000000000), (-82725669801891730535339101/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial141.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial141.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial141.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 18529690883069742476505839596131915), (Int.negOfNat 191945532910464343771955801533923), (Int.negOfNat 637265392373553220242540625716513), (Int.negOfNat 109798442606722814943202365632910), (Int.ofNat 4646228118317191273268702042107), (Int.ofNat 2786514873623674092394528600790), (Int.ofNat 72205544921115122849319874270), (Int.negOfNat 33963094703005295386169765792), (Int.negOfNat 1749769947916513921020822212), (Int.ofNat 253742234006591559949007596), (Int.ofNat 17037516095833286543819961), (Int.negOfNat 1288489698150108308147777), (Int.negOfNat 102737585842603755634048), (Int.ofNat 4737787434903341748964), (Int.ofNat 434903887181507982258), (Int.negOfNat 12965951254316108112), (Int.negOfNat 1511634790111298257), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(3705938176613948495301167919226383/2251799813685248000000000000000000), (-191945532910464343771955801533923/11258999068426240000000000000000000), (-637265392373553220242540625716513/11258999068426240000000000000000000), (-10979844260672281494320236563291/1125899906842624000000000000000000), (4646228118317191273268702042107/11258999068426240000000000000000000), (278651487362367409239452860079/1125899906842624000000000000000000), (7220554492111512284931987427/1125899906842624000000000000000000), (-1061346709468915480817805181/351843720888320000000000000000000), (-437442486979128480255205553/2814749767106560000000000000000000), (63435558501647889987251899/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial141.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial141.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial141.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 14881829118617873173493769990922591), (Int.negOfNat 3689476576227243039038709275367600), (Int.negOfNat 968931645674076266843805029169956), (Int.ofNat 29791441390555965896839940698126), (Int.ofNat 26561062839166276827449004609359), (Int.ofNat 618561211708154263588353350328), (Int.negOfNat 395284708004482412549937718976), (Int.negOfNat 17789094942378003117028986193), (Int.ofNat 3633686618508358720441314172), (Int.ofNat 206291722295269780531897037), (Int.negOfNat 22492205980714984980619858), (Int.negOfNat 1454883285640222297841857), (Int.ofNat 99826634835225229483110), (Int.ofNat 7076440361962713871420), (Int.negOfNat 332717774156199716675), (Int.negOfNat 25786654074275271863), (Int.ofNat 871860733121584661), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(14881829118617873173493769990922591/11258999068426240000000000000000000), (-9223691440568107597596773188419/28147497671065600000000000000000), (-242232911418519066710951257292489/2814749767106560000000000000000000), (14895720695277982948419970349063/5629499534213120000000000000000000), (26561062839166276827449004609359/11258999068426240000000000000000000), (77320151463519282948544168791/1407374883553280000000000000000000), (-6176323562570037696092776859/175921860444160000000000000000000), (-17789094942378003117028986193/11258999068426240000000000000000000), (908421654627089680110328543/2814749767106560000000000000000000), (206291722295269780531897037/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial141.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial141.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial141.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 4283686947484645533110502067367798), (Int.negOfNat 6388063703330605056578529895293488), (Int.negOfNat 202885381832310319560974665617937), (Int.ofNat 201041628426687589250626981581608), (Int.ofNat 8601229682001773591672312450936), (Int.negOfNat 3787717152176378753070124367843), (Int.negOfNat 188668577135926975154776234817), (Int.ofNat 43906962163235060602261071969), (Int.ofNat 2378653366308702378459650039), (Int.negOfNat 334804662371633318582227429), (Int.negOfNat 19138478326224845412153188), (Int.ofNat 1790704166068674256864925), (Int.ofNat 106228785877863521790925), (Int.negOfNat 7079862029675623609963), (Int.negOfNat 431232924006018227752), (Int.ofNat 21173495062892272097), (Int.ofNat 1553409477322449778), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(2141843473742322766555251033683899/5629499534213120000000000000000000), (-399253981458162816036158118455843/703687441776640000000000000000000), (-202885381832310319560974665617937/11258999068426240000000000000000000), (25130203553335948656328372697701/1407374883553280000000000000000000), (1075153710250221698959039056367/1407374883553280000000000000000000), (-3787717152176378753070124367843/11258999068426240000000000000000000), (-188668577135926975154776234817/11258999068426240000000000000000000), (43906962163235060602261071969/11258999068426240000000000000000000), (2378653366308702378459650039/11258999068426240000000000000000000), (-334804662371633318582227429/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial141.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial141.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial141.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 7685268975149398467624714376335158), (Int.negOfNat 4829849036845551271834428649327421), (Int.ofNat 893557175592467268590843870464301), (Int.ofNat 114997632104722391823146973362197), (Int.negOfNat 27159032709288625222397450372704), (Int.negOfNat 2066198573450543875310576795146), (Int.ofNat 434077955063622887729797386416), (Int.ofNat 26602987231955540936570714583), (Int.negOfNat 4240742644524064258184937518), (Int.negOfNat 236800567189261317170800884), (Int.ofNat 27794036216226528555127903), (Int.ofNat 1481329154007534589251398), (Int.negOfNat 130763672619538017772909), (Int.negOfNat 6763071592445130973759), (Int.ofNat 463744912821028343485), (Int.ofNat 23187508645550026115), (Int.negOfNat 1343441501241215888), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-3842634487574699233812357188167579/5629499534213120000000000000000000), (-4829849036845551271834428649327421/11258999068426240000000000000000000), (893557175592467268590843870464301/11258999068426240000000000000000000), (114997632104722391823146973362197/11258999068426240000000000000000000), (-848719772165269538199920324147/351843720888320000000000000000000), (-1033099286725271937655288397573/5629499534213120000000000000000000), (27129872191476430483112336651/703687441776640000000000000000000), (26602987231955540936570714583/11258999068426240000000000000000000), (-2120371322262032129092468759/5629499534213120000000000000000000), (-59200141797315329292700221/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial141.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial141.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial141.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial141.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial141.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial141.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial141.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial141.reflect := by
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

end Bin141
end
end ErdosOverlap.OuterNumerics
