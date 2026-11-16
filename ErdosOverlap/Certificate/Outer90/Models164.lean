/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.IntegerOuterBindings
public import ErdosOverlap.Numerics.OuterTruncation
public import ErdosOverlap.Certificate.OuterData14
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

/-! # Exact integer weighted outer models for source bin 164

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin164

def weightDenominator : ℤ := (Int.ofNat 5000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 196785342991796020)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 876281834125958600)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 621544397470512650)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 234213176274037100)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 429149647764834700)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 348829233536395300)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 247215771449058320)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 179094714756427680)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 98907126212993690)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 57513696134903055)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial164.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial164.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 4544764576734312000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1767577912518729650)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 580724702910129150)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 480698001745849350)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 247491995460130450)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 94010035238484280)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 3920099309732503)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 16129886161805368)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 14411436926167773)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial164.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial164.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4544764576734312000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1767577912518729650)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 580724702910129150)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 480698001745849350)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 247491995460130450)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 94010035238484280)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 3920099309732503)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 16129886161805368)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 14411436926167773)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial164.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial164.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial164.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 1963927837460761819988414984283139), (Int.ofNat 1974163167296434890032121447809036), (Int.ofNat 193478434350956666374477117860344), (Int.negOfNat 47681715442722304983435255094734), (Int.negOfNat 6038407328687826439728596443976), (Int.ofNat 829775566388924009012061844120), (Int.ofNat 103503029196718093390483880085), (Int.negOfNat 9616090440599009574508381728), (Int.negOfNat 1095677554038070515207987734), (Int.ofNat 77121632030302809416472677), (Int.ofNat 7824226028119423353628511), (Int.negOfNat 447118566704756635509599), (Int.negOfNat 40149782273497204199983), (Int.ofNat 1943270099445632338186), (Int.ofNat 155225152403955059116), (Int.negOfNat 6446917728256990533), (Int.negOfNat 489074114606320971), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1963927837460761819988414984283139/5629499534213120000000000000000000), (493540791824108722508030361952259/1407374883553280000000000000000000), (24184804293869583296809639732543/703687441776640000000000000000000), (-23840857721361152491717627547367/2814749767106560000000000000000000), (-754800916085978304966074555497/703687441776640000000000000000000), (20744389159723100225301546103/140737488355328000000000000000000), (20700605839343618678096776017/1125899906842624000000000000000000), (-300502826268719049203386929/175921860444160000000000000000000), (-547838777019035257603993867/2814749767106560000000000000000000), (77121632030302809416472677/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial164.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial164.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial164.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial164 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 2311956089044431831299428198675516), (Int.ofNat 2063703774088216188344335148444505), (Int.negOfNat 154305759851882014898724401422915), (Int.negOfNat 53073883738019686867994312907673), (Int.ofNat 4942852804585373895227007538528), (Int.ofNat 975253333702399353007172952540), (Int.negOfNat 84181514782776666708733388184), (Int.negOfNat 11640062704124441360020322666), (Int.ofNat 895858904572195288682054478), (Int.ofNat 94095551007613070485569607), (Int.negOfNat 6495851274307946435009801), (Int.negOfNat 543348400218325653304961), (Int.ofNat 33933192425984194782204), (Int.ofNat 2340484282971735433924), (Int.negOfNat 133389549253927463057), (Int.negOfNat 7712280093669192917), (Int.ofNat 427727365290838615), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(577989022261107957824857049668879/1407374883553280000000000000000000), (412740754817643237668867029688901/1125899906842624000000000000000000), (-30861151970376402979744880284583/1125899906842624000000000000000000), (-53073883738019686867994312907673/5629499534213120000000000000000000), (154464150143292934225843985579/175921860444160000000000000000000), (48762666685119967650358647627/281474976710656000000000000000000), (-10522689347847083338591673523/703687441776640000000000000000000), (-5820031352062220680010161333/2814749767106560000000000000000000), (447929452286097644341027239/2814749767106560000000000000000000), (94095551007613070485569607/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial164.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial164.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial164.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial164 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 5501235642517250003618714918495162), (Int.ofNat 1025503805589754994525497855745180), (Int.negOfNat 302174563618969699259580453491803), (Int.ofNat 7484500090400245274237997562381), (Int.ofNat 7662779636267464986973793114692), (Int.negOfNat 486042135268387608184323994667), (Int.negOfNat 111030671131470987657975787613), (Int.ofNat 8186997814184640065918333189), (Int.ofNat 1037792670284852950661502411), (Int.negOfNat 79188763874731313360201814), (Int.negOfNat 6770079122391027751530991), (Int.ofNat 511867944576711538112789), (Int.ofNat 32484106110135802866159), (Int.negOfNat 2381352362509609322321), (Int.negOfNat 119010544772347601710), (Int.ofNat 8372511614786589289), (Int.ofNat 330944463127779579), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(2750617821258625001809357459247581/2814749767106560000000000000000000), (51275190279487749726274892787259/281474976710656000000000000000000), (-302174563618969699259580453491803/5629499534213120000000000000000000), (7484500090400245274237997562381/5629499534213120000000000000000000), (1915694909066866246743448278673/1407374883553280000000000000000000), (-486042135268387608184323994667/5629499534213120000000000000000000), (-111030671131470987657975787613/5629499534213120000000000000000000), (8186997814184640065918333189/5629499534213120000000000000000000), (1037792670284852950661502411/5629499534213120000000000000000000), (-39594381937365656680100907/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial164.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial164.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial164.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial164 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 6504633456469582803069835849231918), (Int.ofNat 96147027610635648150618526386814), (Int.negOfNat 131956897342642109804870204230330), (Int.ofNat 37519391292954490493384853079920), (Int.negOfNat 790304621613977111160830845394), (Int.negOfNat 862460347790242158018828385852), (Int.ofNat 52755105762852971820867052908), (Int.ofNat 10116560656790318811229009481), (Int.negOfNat 786551169496570565012848645), (Int.negOfNat 76659532373237972936187475), (Int.ofNat 6626407845633080786306586), (Int.ofNat 411951148376726483588002), (Int.negOfNat 37466472737041016520049), (Int.negOfNat 1658676133259230064280), (Int.ofNat 153940587747290372469), (Int.ofNat 5056686940126289265), (Int.negOfNat 470961676069341934), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(3252316728234791401534917924615959/2814749767106560000000000000000000), (48073513805317824075309263193407/2814749767106560000000000000000000), (-13195689734264210980487020423033/562949953421312000000000000000000), (468992391161931131167310663499/70368744177664000000000000000000), (-395152310806988555580415422697/2814749767106560000000000000000000), (-215615086947560539504707096463/1407374883553280000000000000000000), (13188776440713242955216763227/1407374883553280000000000000000000), (10116560656790318811229009481/5629499534213120000000000000000000), (-157310233899314113002569729/1125899906842624000000000000000000), (-3066381294929518917447499/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial164.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial164.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial164.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial164 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 6433449552070962475271496356647398), (Int.negOfNat 62017717423372414906142934185050), (Int.ofNat 22977319575951289308472300439554), (Int.ofNat 9097608636392412967282048858569), (Int.negOfNat 4505719864639928261210259742293), (Int.ofNat 174912050056934905725522008313), (Int.ofNat 80680643479994757893545638601), (Int.negOfNat 6029267915037139212724930767), (Int.negOfNat 762754131711489679907568466), (Int.ofNat 72355618961860051691083672), (Int.ofNat 4703071728069229652443290), (Int.negOfNat 515524088996945837273911), (Int.negOfNat 20763794476574497409709), (Int.ofNat 2524307193197308603335), (Int.ofNat 69442402509997139687), (Int.negOfNat 9230380100865401080), (Int.negOfNat 158403374723070414), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(3216724776035481237635748178323699/2814749767106560000000000000000000), (-1240354348467448298122858683701/112589990684262400000000000000000), (11488659787975644654236150219777/2814749767106560000000000000000000), (9097608636392412967282048858569/5629499534213120000000000000000000), (-4505719864639928261210259742293/5629499534213120000000000000000000), (174912050056934905725522008313/5629499534213120000000000000000000), (80680643479994757893545638601/5629499534213120000000000000000000), (-6029267915037139212724930767/5629499534213120000000000000000000), (-381377065855744839953784233/2814749767106560000000000000000000), (9044452370232506461385459/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial164.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial164.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial164.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial164 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 6411847224908573899091364787601196), (Int.ofNat 21065914133483808817880530282247), (Int.negOfNat 2264415703721022274636087142936), (Int.negOfNat 11348128844902846165186550095699), (Int.negOfNat 126731267821563438606899815476), (Int.ofNat 462227780002630007987044710679), (Int.negOfNat 32998051254830824805470180056), (Int.negOfNat 6255234319431429843616148790), (Int.ofNat 650769003519670891171770144), (Int.ofNat 46754428773082184826214939), (Int.negOfNat 6138480210380584116330790), (Int.negOfNat 228398794182035941118486), (Int.ofNat 36720437576704556215519), (Int.ofNat 792890465742792416928), (Int.negOfNat 155766359211569349589), (Int.negOfNat 1997837655790224043), (Int.ofNat 514195986847845253), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(1602961806227143474772841196900299/1407374883553280000000000000000000), (21065914133483808817880530282247/5629499534213120000000000000000000), (-283051962965127784329510892867/703687441776640000000000000000000), (-11348128844902846165186550095699/5629499534213120000000000000000000), (-31682816955390859651724953869/1407374883553280000000000000000000), (462227780002630007987044710679/5629499534213120000000000000000000), (-4124756406853853100683772507/703687441776640000000000000000000), (-625523431943142984361614879/562949953421312000000000000000000), (20336531359989715349117817/175921860444160000000000000000000), (46754428773082184826214939/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial164.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial164.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial164.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial164 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 6364171338890249090230030182383637), (Int.negOfNat 99643409270609765208879249360014), (Int.negOfNat 47232541514222612866138683490603), (Int.negOfNat 1337641109716485796026878688731), (Int.ofNat 1594206184781825880459510766431), (Int.negOfNat 125818648213191647689142164070), (Int.negOfNat 38043336205306052647446897133), (Int.ofNat 4739700705513216312646938131), (Int.ofNat 379445625940307625859972609), (Int.negOfNat 62470234098059923263862826), (Int.negOfNat 2093808392286862363826914), (Int.ofNat 469933973652486176826072), (Int.ofNat 7048681267655051425437), (Int.negOfNat 2373899295145315362060), (Int.negOfNat 13566904896178211045), (Int.ofNat 8909151790393816225), (Int.negOfNat 14137713681638751), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(6364171338890249090230030182383637/5629499534213120000000000000000000), (-49821704635304882604439624680007/2814749767106560000000000000000000), (-47232541514222612866138683490603/5629499534213120000000000000000000), (-1337641109716485796026878688731/5629499534213120000000000000000000), (1594206184781825880459510766431/5629499534213120000000000000000000), (-12581864821319164768914216407/562949953421312000000000000000000), (-38043336205306052647446897133/5629499534213120000000000000000000), (4739700705513216312646938131/5629499534213120000000000000000000), (379445625940307625859972609/5629499534213120000000000000000000), (-31235117049029961631931413/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial164.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial164.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial164.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial164 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 5984970216971430621592393728411399), (Int.negOfNat 268617855899304809977196775299382), (Int.negOfNat 32626937511782749863468582825078), (Int.ofNat 3282481362661954709669414420714), (Int.negOfNat 454621725982312318298075654661), (Int.negOfNat 143196872429218084065322700893), (Int.ofNat 28649440311803454425719181697), (Int.ofNat 2212194639089119296668498500), (Int.negOfNat 539239222896695019949972835), (Int.negOfNat 13928478022682461699914000), (Int.ofNat 5239365617937672484086840), (Int.ofNat 31956490594321703171479), (Int.negOfNat 32158008019191151950645), (Int.ofNat 104663533497047832381), (Int.ofNat 138189108656085431305), (Int.negOfNat 1183252905016205989), (Int.negOfNat 499916601491445517), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(5984970216971430621592393728411399/5629499534213120000000000000000000), (-134308927949652404988598387649691/2814749767106560000000000000000000), (-16313468755891374931734291412539/2814749767106560000000000000000000), (1641240681330977354834707210357/2814749767106560000000000000000000), (-454621725982312318298075654661/5629499534213120000000000000000000), (-143196872429218084065322700893/5629499534213120000000000000000000), (28649440311803454425719181697/5629499534213120000000000000000000), (4424389278178238593336997/11258999068426240000000000000000), (-107847844579339003989994567/1125899906842624000000000000000000), (-6964239011341230849957/2814749767106560000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial164.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial164.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial164.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial164 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 5333607208865997410973341526100728), (Int.negOfNat 379805574903517311516002758542775), (Int.negOfNat 27907608624330252906875986823764), (Int.negOfNat 1222489980417527713070608175663), (Int.negOfNat 140451220932190880098690070159), (Int.ofNat 156866107940588504419338560316), (Int.ofNat 6163612643646119332705739875), (Int.negOfNat 3969771602047526366299793802), (Int.negOfNat 30728629157925930041897123), (Int.ofNat 50405388738744414784748266), (Int.negOfNat 402573749959600870284614), (Int.negOfNat 382842368914949790622209), (Int.ofNat 6017450773882079439281), (Int.ofNat 1956862206648927999377), (Int.negOfNat 38679483528842369965), (Int.negOfNat 7361540221713830865), (Int.ofNat 157987979803780407), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(666700901108249676371667690762591/703687441776640000000000000000000), (-15192222996140692460640110341711/225179981368524800000000000000000), (-6976902156082563226718996705941/1407374883553280000000000000000000), (-1222489980417527713070608175663/5629499534213120000000000000000000), (-140451220932190880098690070159/5629499534213120000000000000000000), (39216526985147126104834640079/1407374883553280000000000000000000), (49308901149168954661645919/45035996273704960000000000000000), (-1984885801023763183149896901/2814749767106560000000000000000000), (-30728629157925930041897123/5629499534213120000000000000000000), (25202694369372207392374133/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial164.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial164.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial164.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial164 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 4455261325639092636662133347225767), (Int.negOfNat 498567543264202266818387577843525), (Int.negOfNat 27090025699608183640052037599449), (Int.ofNat 2886419043219054747001483978737), (Int.ofNat 835147951726855693862225643991), (Int.negOfNat 28151821273802068859431422106), (Int.negOfNat 25255679632829077844886472595), (Int.ofNat 728928989777754291853056201), (Int.ofNat 414379742352555413417718581), (Int.negOfNat 13340832068867503780696920), (Int.negOfNat 3948333665100918265580878), (Int.ofNat 137100451773666719564178), (Int.ofNat 24303806144788071615883), (Int.negOfNat 876141316504882328138), (Int.negOfNat 105037981690655977765), (Int.ofNat 3904762103022483729), (Int.ofNat 413712083073974953), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(4455261325639092636662133347225767/5629499534213120000000000000000000), (-19942701730568090672735503113741/225179981368524800000000000000000), (-27090025699608183640052037599449/5629499534213120000000000000000000), (2886419043219054747001483978737/5629499534213120000000000000000000), (835147951726855693862225643991/5629499534213120000000000000000000), (-14075910636901034429715711053/2814749767106560000000000000000000), (-5051135926565815568977294519/1125899906842624000000000000000000), (728928989777754291853056201/5629499534213120000000000000000000), (414379742352555413417718581/5629499534213120000000000000000000), (-333520801721687594517423/140737488355328000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial164.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial164.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial164.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial164 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 3383891516210576420192852603460401), (Int.negOfNat 551965102993196002023223800676091), (Int.ofNat 3089308073866158454745640671173), (Int.ofNat 5427225375845091515504577517371), (Int.negOfNat 391906074595716997885068147152), (Int.negOfNat 136946659677423249973877927985), (Int.ofNat 12331504579967906970586275206), (Int.ofNat 2852968075833492307693707512), (Int.negOfNat 215198711380851612994730008), (Int.negOfNat 34499584856670721278001325), (Int.ofNat 2299299136721031471915354), (Int.ofNat 259522069330214552308246), (Int.negOfNat 16114314520828986928317), (Int.negOfNat 1324615073799223760416), (Int.ofNat 78780215028334502521), (Int.ofNat 4893181308596324477), (Int.negOfNat 258735986717186781), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(3383891516210576420192852603460401/5629499534213120000000000000000000), (-551965102993196002023223800676091/5629499534213120000000000000000000), (3089308073866158454745640671173/5629499534213120000000000000000000), (5427225375845091515504577517371/5629499534213120000000000000000000), (-24494129662232312367816759197/351843720888320000000000000000000), (-27389331935484649994775585597/1125899906842624000000000000000000), (6165752289983953485293137603/2814749767106560000000000000000000), (356621009479186538461713439/703687441776640000000000000000000), (-26899838922606451624341251/703687441776640000000000000000000), (-1379983394266828851120053/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial164.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial164.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial164.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial164 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 2326168007328859770645624149849952), (Int.negOfNat 494617726128787951595120449337562), (Int.ofNat 19655855531735264286912337630543), (Int.negOfNat 142149922271850117591135237081), (Int.negOfNat 563346425535194197728428654003), (Int.ofNat 108958405641644066423260257420), (Int.ofNat 15375994361540838786071779408), (Int.negOfNat 2493692477736539562637306285), (Int.negOfNat 243843620095199882225013918), (Int.ofNat 31196255413652748976872124), (Int.ofNat 2285363452468316972012144), (Int.negOfNat 251130050485198881694769), (Int.negOfNat 13954166189963358048525), (Int.ofNat 1396176717568120302073), (Int.ofNat 59893176687414291127), (Int.negOfNat 5667134106110845884), (Int.negOfNat 241170994669265788), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(72692750229026867832675754682811/175921860444160000000000000000000), (-247308863064393975797560224668781/2814749767106560000000000000000000), (19655855531735264286912337630543/5629499534213120000000000000000000), (-142149922271850117591135237081/5629499534213120000000000000000000), (-563346425535194197728428654003/5629499534213120000000000000000000), (5447920282082203321163012871/281474976710656000000000000000000), (960999647596302424129486213/351843720888320000000000000000000), (-498738495547307912527461257/1125899906842624000000000000000000), (-121921810047599941112506959/2814749767106560000000000000000000), (7799063853413187244218031/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial164.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial164.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial164.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial164 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 1409512104480984901537138965570249), (Int.negOfNat 425344710069160569382553802599856), (Int.ofNat 15739128897075478399101353682539), (Int.ofNat 527215658771756840240298455609), (Int.ofNat 622136956269149146630226553567), (Int.ofNat 47741956286474515422745559700), (Int.negOfNat 22404143360729248867795598621), (Int.negOfNat 1218964491112679094169631223), (Int.ofNat 351023491841623408701112737), (Int.ofNat 14936367250371063481382391), (Int.negOfNat 3363021852866551412250878), (Int.negOfNat 111145076022489273659692), (Int.ofNat 21740358484631979316397), (Int.ofNat 557191314278931845478), (Int.negOfNat 100526926102245758131), (Int.negOfNat 1970606194902471979), (Int.ofNat 301970297495690100), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(1409512104480984901537138965570249/5629499534213120000000000000000000), (-26584044379322535586409612662491/351843720888320000000000000000000), (15739128897075478399101353682539/5629499534213120000000000000000000), (527215658771756840240298455609/5629499534213120000000000000000000), (622136956269149146630226553567/5629499534213120000000000000000000), (477419562864745154227455597/56294995342131200000000000000000), (-22404143360729248867795598621/5629499534213120000000000000000000), (-1218964491112679094169631223/5629499534213120000000000000000000), (351023491841623408701112737/5629499534213120000000000000000000), (14936367250371063481382391/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial164.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial164.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial164.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial164 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 635982896462523603862562752879522), (Int.negOfNat 336805616177889407922350792596773), (Int.ofNat 32114436454744167433673540864419), (Int.ofNat 3802222465724504620616980471039), (Int.negOfNat 179673539060137094437662690727), (Int.negOfNat 164255024578473853243253749596), (Int.negOfNat 1732334907965196370536612895), (Int.ofNat 3299622682902401256066260083), (Int.ofNat 43122631307961378950398303), (Int.negOfNat 38710370214483175745433022), (Int.negOfNat 417367223267414276362005), (Int.ofNat 296712533630622294896241), (Int.ofNat 2393207614146798619235), (Int.negOfNat 1591565914517394502987), (Int.negOfNat 9088501217857287100), (Int.ofNat 6308055060353482485), (Int.ofNat 68629906264556623), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(317991448231261801931281376439761/2814749767106560000000000000000000), (-336805616177889407922350792596773/5629499534213120000000000000000000), (32114436454744167433673540864419/5629499534213120000000000000000000), (3802222465724504620616980471039/5629499534213120000000000000000000), (-179673539060137094437662690727/5629499534213120000000000000000000), (-41063756144618463310813437399/1407374883553280000000000000000000), (-346466981593039274107322579/1125899906842624000000000000000000), (3299622682902401256066260083/5629499534213120000000000000000000), (43122631307961378950398303/5629499534213120000000000000000000), (-19355185107241587872716511/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial164.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial164.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial164.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial164 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 113419131294356146103579954640786), (Int.negOfNat 180509384649196030706942527859977), (Int.ofNat 39179145577392091493089168459866), (Int.negOfNat 2759652293419614563390243136094), (Int.negOfNat 1103400044254381150372152788020), (Int.ofNat 38539574898357819990470071129), (Int.ofNat 26063740591573818061573247508), (Int.negOfNat 526763908126083485188885932), (Int.negOfNat 380450775372430348591187974), (Int.ofNat 5572852628007838097437037), (Int.ofNat 3525254932089396742763783), (Int.negOfNat 42699221542527908138459), (Int.negOfNat 22258016685891395324922), (Int.ofNat 239958660805641829038), (Int.ofNat 101126284273100028213), (Int.negOfNat 1125170265044929869), (Int.negOfNat 345204608274193419), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(56709565647178073051789977320393/2814749767106560000000000000000000), (-180509384649196030706942527859977/5629499534213120000000000000000000), (19589572788696045746544584229933/2814749767106560000000000000000000), (-1379826146709807281695121568047/2814749767106560000000000000000000), (-55170002212719057518607639401/281474976710656000000000000000000), (38539574898357819990470071129/5629499534213120000000000000000000), (6515935147893454515393311877/1407374883553280000000000000000000), (-131690977031520871297221483/1407374883553280000000000000000000), (-190225387686215174295593987/2814749767106560000000000000000000), (5572852628007838097437037/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial164.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial164.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial164.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial164 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 127871862018307965689319957277775), (Int.negOfNat 84725713760622353696226559338065), (Int.ofNat 4505999873744207947056920503675), (Int.negOfNat 6771887519586809042320219793708), (Int.ofNat 337632804764018279226476510676), (Int.ofNat 172934775598351866609648137330), (Int.negOfNat 10153821217138981545510922643), (Int.negOfNat 3149508442719171680005199014), (Int.ofNat 149220257236804645669916944), (Int.ofNat 35956091563546847084250729), (Int.negOfNat 1375808953756488160251785), (Int.negOfNat 271558182415723460729321), (Int.ofNat 8705328301621746795021), (Int.ofNat 1443651280803954302272), (Int.negOfNat 39906469542876911404), (Int.negOfNat 5716153569650783851), (Int.ofNat 118322619066320315), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-5114874480732318627572798291111/225179981368524800000000000000000), (-16945142752124470739245311867613/1125899906842624000000000000000000), (180239994949768317882276820147/225179981368524800000000000000000), (-1692971879896702260580054948427/1407374883553280000000000000000000), (84408201191004569806619127669/1407374883553280000000000000000000), (17293477559835186660964813733/562949953421312000000000000000000), (-10153821217138981545510922643/5629499534213120000000000000000000), (-1574754221359585840002599507/2814749767106560000000000000000000), (9326266077300290354369809/351843720888320000000000000000000), (35956091563546847084250729/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial164.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial164.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial164.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial164 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 323536642568133731363116621148008), (Int.negOfNat 126460019841660240469259858944085), (Int.negOfNat 18330351198274377094636530225867), (Int.negOfNat 112306846063169498743652172170), (Int.ofNat 859605138720917951388227241667), (Int.negOfNat 91954280393250466834088535207), (Int.negOfNat 21221089493644194208780890217), (Int.ofNat 2014465715354012895882635276), (Int.ofNat 307018276008667683871773996), (Int.negOfNat 23547247289721926462544331), (Int.negOfNat 2826108902347072895675215), (Int.ofNat 178307978258524004821749), (Int.ofNat 17811922091588077767559), (Int.negOfNat 946391759673356904158), (Int.negOfNat 81193264213200700916), (Int.ofNat 3798046046618964229), (Int.ofNat 259000089856722855), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-40442080321016716420389577643501/703687441776640000000000000000000), (-25292003968332048093851971788817/1125899906842624000000000000000000), (-18330351198274377094636530225867/5629499534213120000000000000000000), (-11230684606316949874365217217/562949953421312000000000000000000), (859605138720917951388227241667/5629499534213120000000000000000000), (-91954280393250466834088535207/5629499534213120000000000000000000), (-21221089493644194208780890217/5629499534213120000000000000000000), (503616428838503223970658819/1407374883553280000000000000000000), (76754569002166920967943499/1407374883553280000000000000000000), (-23547247289721926462544331/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial164.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial164.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial164.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial164 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 640901618942817112419871607314478), (Int.negOfNat 183902001601745858308070559963368), (Int.negOfNat 9054190452273442482211863296726), (Int.ofNat 1208475656201332335915143453083), (Int.negOfNat 548846202667389969827850186459), (Int.negOfNat 103412585246375127569657944771), (Int.ofNat 19478610622461022593312216372), (Int.ofNat 2083665691848560075150223118), (Int.negOfNat 299864288907702752986372166), (Int.negOfNat 24007759611890134876806893), (Int.ofNat 2798444445179712810899637), (Int.ofNat 182889296472223284205891), (Int.negOfNat 17604831139487938692608), (Int.negOfNat 983638660491142626492), (Int.ofNat 79574636772578721657), (Int.ofNat 4031095697675623061), (Int.negOfNat 262172885188461971), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-320450809471408556209935803657239/2814749767106560000000000000000000), (-22987750200218232288508819995421/703687441776640000000000000000000), (-4527095226136721241105931648363/2814749767106560000000000000000000), (1208475656201332335915143453083/5629499534213120000000000000000000), (-548846202667389969827850186459/5629499534213120000000000000000000), (-103412585246375127569657944771/5629499534213120000000000000000000), (4869652655615255648328054093/1407374883553280000000000000000000), (1041832845924280037575111559/2814749767106560000000000000000000), (-149932144453851376493186083/2814749767106560000000000000000000), (-24007759611890134876806893/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial164.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial164.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial164.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial164 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 1045917876204875840092683054616465), (Int.negOfNat 227126227258163850402265010097974), (Int.negOfNat 17785473056243339229371066045770), (Int.negOfNat 3653285796907066884458350511128), (Int.negOfNat 220640571563305698292008993989), (Int.ofNat 148576348511593206680229653907), (Int.ofNat 9850165879237235535931623195), (Int.negOfNat 3033676588797706053719380557), (Int.negOfNat 149294729931519494201265643), (Int.ofNat 35860634517037043073834938), (Int.ofNat 1414877243355717858015195), (Int.negOfNat 273323172590199635162459), (Int.negOfNat 9239913878855287586915), (Int.ofNat 1449943160596315318233), (Int.ofNat 43356104615833315510), (Int.negOfNat 5723639933148562985), (Int.negOfNat 100870438378181463), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-209183575240975168018536610923293/1125899906842624000000000000000000), (-113563113629081925201132505048987/2814749767106560000000000000000000), (-1778547305624333922937106604577/562949953421312000000000000000000), (-456660724613383360557293813891/703687441776640000000000000000000), (-220640571563305698292008993989/5629499534213120000000000000000000), (148576348511593206680229653907/5629499534213120000000000000000000), (1970033175847447107186324639/1125899906842624000000000000000000), (-3033676588797706053719380557/5629499534213120000000000000000000), (-149294729931519494201265643/5629499534213120000000000000000000), (17930317258518521536917469/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial164.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial164.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial164.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial164 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 1599091210485666275718185807011856), (Int.negOfNat 336816030479510849811660480137160), (Int.negOfNat 32883113947546556554502282430614), (Int.ofNat 336654524897478564027440318486), (Int.ofNat 990942226974673154470990534543), (Int.ofNat 20255890666857039058025761060), (Int.negOfNat 24740476119866810829173330391), (Int.negOfNat 408954184092858427495758653), (Int.ofNat 380066076965196697679648603), (Int.ofNat 5221956167797323988068431), (Int.negOfNat 3599034156786680686723672), (Int.negOfNat 46456622028220516608202), (Int.ofNat 22829542778427130350233), (Int.ofNat 288942275932625746988), (Int.negOfNat 103280284593807299469), (Int.negOfNat 1375502544132719409), (Int.ofNat 305407195966965290), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-99943200655354142232386612938241/351843720888320000000000000000000), (-8420400761987771245291512003429/140737488355328000000000000000000), (-16441556973773278277251141215307/2814749767106560000000000000000000), (168327262448739282013720159243/2814749767106560000000000000000000), (990942226974673154470990534543/5629499534213120000000000000000000), (1012794533342851952901288053/281474976710656000000000000000000), (-24740476119866810829173330391/5629499534213120000000000000000000), (-408954184092858427495758653/5629499534213120000000000000000000), (380066076965196697679648603/5629499534213120000000000000000000), (5221956167797323988068431/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial164.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial164.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial164.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial164 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 2386598679342808465151160466232813), (Int.negOfNat 435528559180755520744860194412997), (Int.negOfNat 11008711371561882271884670054618), (Int.ofNat 5541423871533001710158460647056), (Int.negOfNat 6147253941830268912204745119), (Int.negOfNat 158278395106746098277521202850), (Int.ofNat 4164745583354315507725649237), (Int.ofNat 3288531359923424256142313445), (Int.negOfNat 62158600683743747564125722), (Int.negOfNat 40018849276747777090375486), (Int.ofNat 465688295152907165743946), (Int.ofNat 310715920298970316586731), (Int.negOfNat 2057495544730992036235), (Int.negOfNat 1666692027164533024947), (Int.ofNat 5174411827309522753), (Int.ofNat 6581508419227374776), (Int.negOfNat 71670650026527702), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-2386598679342808465151160466232813/5629499534213120000000000000000000), (-435528559180755520744860194412997/5629499534213120000000000000000000), (-5504355685780941135942335027309/2814749767106560000000000000000000), (346338991970812606884903790441/351843720888320000000000000000000), (-6147253941830268912204745119/5629499534213120000000000000000000), (-3165567902134921965550424057/112589990684262400000000000000000), (4164745583354315507725649237/5629499534213120000000000000000000), (657706271984684851228462689/1125899906842624000000000000000000), (-31079300341871873782062861/2814749767106560000000000000000000), (-20009424638373888545187743/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial164.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial164.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial164.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial164 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 3261870352016153569039491561359903), (Int.negOfNat 423802515464236507593601130953481), (Int.ofNat 12357379811859807401629903422975), (Int.ofNat 1362091011959361757415446281085), (Int.negOfNat 630695372986437671117774268955), (Int.ofNat 71620013263400102093953556175), (Int.ofNat 22040652352689849476405721134), (Int.negOfNat 1603569801807524495397881388), (Int.negOfNat 367311197623226426797512342), (Int.ofNat 17274091839511737226561375), (Int.ofNat 3608965824121998995034166), (Int.negOfNat 115816590659210198027104), (Int.negOfNat 23417870093862992808523), (Int.ofNat 531039928247595168344), (Int.ofNat 108023882582063585949), (Int.negOfNat 1683346740203345813), (Int.negOfNat 348641506745468609), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-3261870352016153569039491561359903/5629499534213120000000000000000000), (-423802515464236507593601130953481/5629499534213120000000000000000000), (494295192474392296065196136919/225179981368524800000000000000000), (272418202391872351483089256217/1125899906842624000000000000000000), (-126139074597287534223554853791/1125899906842624000000000000000000), (2864800530536004083758142247/225179981368524800000000000000000), (11020326176344924738202860567/2814749767106560000000000000000000), (-400892450451881123849470347/1407374883553280000000000000000000), (-183655598811613213398756171/2814749767106560000000000000000000), (138192734716093897812491/45035996273704960000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial164.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial164.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial164.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial164 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 4055824895157844362823076996252730), (Int.negOfNat 369286838286918558967905992396077), (Int.ofNat 14793226984034898775511631644730), (Int.ofNat 1292612450896796909309432020980), (Int.ofNat 658147123558853640501859049477), (Int.ofNat 95258193701109237715333719692), (Int.negOfNat 20718840375017779298694351265), (Int.negOfNat 2632761198089349498848840569), (Int.ofNat 294890237194050133620944789), (Int.ofNat 34679164050785827432757740), (Int.negOfNat 2518665009405855344532902), (Int.negOfNat 281491787425549128276032), (Int.ofNat 14340496168079886377767), (Int.ofNat 1553948875268066194692), (Int.negOfNat 58271340254216720115), (Int.negOfNat 6260280108755789921), (Int.ofNat 244211738431236867), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-405582489515784436282307699625273/562949953421312000000000000000000), (-369286838286918558967905992396077/5629499534213120000000000000000000), (1479322698403489877551163164473/562949953421312000000000000000000), (64630622544839845465471601049/281474976710656000000000000000000), (658147123558853640501859049477/5629499534213120000000000000000000), (23814548425277309428833429923/1407374883553280000000000000000000), (-4143768075003555859738870253/1125899906842624000000000000000000), (-2632761198089349498848840569/5629499534213120000000000000000000), (294890237194050133620944789/5629499534213120000000000000000000), (1733958202539291371637887/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial164.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial164.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial164.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial164 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 4712878984877663529139377386022824), (Int.negOfNat 270712482649205558229676353881591), (Int.ofNat 39875844841040787919232306331023), (Int.ofNat 6245074531798018787288094775512), (Int.ofNat 57098654276740004213662190156), (Int.negOfNat 199240428452387386037835964481), (Int.negOfNat 12739089637896292572862623890), (Int.ofNat 3674767408568601590331030138), (Int.ofNat 256249042008871732419341493), (Int.negOfNat 39963110174698339258975914), (Int.negOfNat 2768532128714713227832796), (Int.ofNat 279492907656133259175451), (Int.ofNat 19077753904927363329709), (Int.negOfNat 1354688304413757024273), (Int.negOfNat 91080320906543362385), (Int.ofNat 4864437301009775845), (Int.ofNat 334362121389068873), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-589109873109707941142422173252853/703687441776640000000000000000000), (-270712482649205558229676353881591/5629499534213120000000000000000000), (39875844841040787919232306331023/5629499534213120000000000000000000), (780634316474752348411011846939/703687441776640000000000000000000), (14274663569185001053415547539/1407374883553280000000000000000000), (-199240428452387386037835964481/5629499534213120000000000000000000), (-1273908963789629257286262389/562949953421312000000000000000000), (1837383704284300795165515069/2814749767106560000000000000000000), (256249042008871732419341493/5629499534213120000000000000000000), (-19981555087349169629487957/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial164.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial164.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial164.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial164 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 5050604079515842309512248739810077), (Int.negOfNat 51020210734227662446202195656115), (Int.ofNat 62441556571217198176758792698399), (Int.negOfNat 1032805821623522995578331355877), (Int.negOfNat 1568408135247502522194427100280), (Int.negOfNat 21845039028176330167976046954), (Int.ofNat 36157167422552450084879950263), (Int.ofNat 1142158872125321595855398540), (Int.negOfNat 509887239073400236352220765), (Int.negOfNat 19694626655137388288413750), (Int.ofNat 4443844784873848088587970), (Int.ofNat 186077462660612030625909), (Int.negOfNat 25839294451374276850105), (Int.negOfNat 1120122986561524846789), (Int.ofNat 107293490682838843685), (Int.ofNat 4712668540075804561), (Int.negOfNat 388062004553378523), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-5050604079515842309512248739810077/5629499534213120000000000000000000), (-10204042146845532489240439131223/1125899906842624000000000000000000), (62441556571217198176758792698399/5629499534213120000000000000000000), (-1032805821623522995578331355877/5629499534213120000000000000000000), (-39210203381187563054860677507/140737488355328000000000000000000), (-10922519514088165083988023477/2814749767106560000000000000000000), (36157167422552450084879950263/5629499534213120000000000000000000), (57107943606266079792769927/281474976710656000000000000000000), (-101977447814680047270444153/1125899906842624000000000000000000), (-15755701324109910630731/4503599627370496000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial164.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial164.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial164.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial164 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 4934609833953134857877580435671180), (Int.ofNat 141326211702069322809839834607641), (Int.ofNat 25350654634314797331921008174109), (Int.negOfNat 8975746935560748078528459541243), (Int.ofNat 115914923976983114934178070435), (Int.ofNat 278318353504363925438902174292), (Int.negOfNat 2194930307536447638018455197), (Int.negOfNat 5328613698845796526284203399), (Int.negOfNat 46375409998897481399487109), (Int.ofNat 59658666443253238103542074), (Int.ofNat 1127935150544044220849274), (Int.negOfNat 422638418760916960233358), (Int.negOfNat 10279344813986491184047), (Int.ofNat 2066551302444902414930), (Int.ofNat 56209116508531199885), (Int.negOfNat 7585946499016053585), (Int.negOfNat 248157602971598309), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-246730491697656742893879021783559/281474976710656000000000000000000), (141326211702069322809839834607641/5629499534213120000000000000000000), (25350654634314797331921008174109/5629499534213120000000000000000000), (-8975746935560748078528459541243/5629499534213120000000000000000000), (23182984795396622986835614087/1125899906842624000000000000000000), (69579588376090981359725543573/1407374883553280000000000000000000), (-2194930307536447638018455197/5629499534213120000000000000000000), (-5328613698845796526284203399/5629499534213120000000000000000000), (-46375409998897481399487109/5629499534213120000000000000000000), (29829333221626619051771037/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial164.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial164.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial164.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial164 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 4612403541431282441166254854326370), (Int.ofNat 158276808805299128668420101196014), (Int.negOfNat 7371467921742554537317101327895), (Int.negOfNat 14338301398584117618015136382), (Int.ofNat 1460790698703327665698397950609), (Int.negOfNat 99857568241314041495246242960), (Int.negOfNat 44488504230469824400297326394), (Int.ofNat 1349507857113276281303427270), (Int.ofNat 680540712255606285949358716), (Int.negOfNat 4178705479840272797647911), (Int.negOfNat 6025985541331444396173160), (Int.negOfNat 35674354022278384008776), (Int.ofNat 35079478445188106026121), (Int.ofNat 426046106450881914088), (Int.negOfNat 145771670216571048241), (Int.negOfNat 2244309626958298173), (Int.ofNat 488810011466784897), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-461240354143128244116625485432637/562949953421312000000000000000000), (79138404402649564334210050598007/2814749767106560000000000000000000), (-1474293584348510907463420265579/1125899906842624000000000000000000), (-7169150699292058809007568191/2814749767106560000000000000000000), (1460790698703327665698397950609/5629499534213120000000000000000000), (-1248219603016425518690578037/70368744177664000000000000000000), (-22244252115234912200148663197/2814749767106560000000000000000000), (134950785711327628130342727/562949953421312000000000000000000), (170135178063901571487339679/1407374883553280000000000000000000), (-4178705479840272797647911/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial164.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial164.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial164.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial164 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 4307781840189853949306163893984577), (Int.ofNat 160095219940497206369894026423233), (Int.ofNat 10974734850347018092600892417224), (Int.ofNat 2422211782531055521329684413206), (Int.negOfNat 1161923276265538139085370084508), (Int.negOfNat 270007108946776638611644817273), (Int.ofNat 29096264210732012613244331257), (Int.ofNat 6533887376277282677488344403), (Int.negOfNat 259424108002364239661069924), (Int.negOfNat 75315323975010283992551148), (Int.ofNat 1112030456279313848636110), (Int.ofNat 530457098636843015653369), (Int.negOfNat 1653709820386264250091), (Int.negOfNat 2573904662078052937605), (Int.negOfNat 7909702177423844847), (Int.ofNat 9348318502104415740), (Int.ofNat 75616514566889144), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-4307781840189853949306163893984577/5629499534213120000000000000000000), (160095219940497206369894026423233/5629499534213120000000000000000000), (1371841856293377261575111552153/703687441776640000000000000000000), (1211105891265527760664842206603/2814749767106560000000000000000000), (-290480819066384534771342521127/1407374883553280000000000000000000), (-270007108946776638611644817273/5629499534213120000000000000000000), (29096264210732012613244331257/5629499534213120000000000000000000), (6533887376277282677488344403/5629499534213120000000000000000000), (-64856027000591059915267481/1407374883553280000000000000000000), (-18828830993752570998137787/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial164.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial164.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial164.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial164 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 3948950044665002373880558145829172), (Int.ofNat 182364567011396251479026567681520), (Int.negOfNat 13389556678499031532430357988995), (Int.negOfNat 10190304082534065966138608129066), (Int.negOfNat 844738173177423226418220168310), (Int.ofNat 383593597914095163285296564512), (Int.ofNat 51836431133063679131473392789), (Int.negOfNat 4906861342373780020376220219), (Int.negOfNat 827829403374526162975684075), (Int.ofNat 33661641406499283557331485), (Int.ofNat 7187096482664057522413744), (Int.negOfNat 144920346675839219919478), (Int.negOfNat 41025356612613973600901), (Int.ofNat 414965495534004367950), (Int.ofNat 168556007109689927611), (Int.negOfNat 678265486735554325), (Int.negOfNat 532044322245288216), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-987237511166250593470139536457293/1407374883553280000000000000000000), (2279557087642453143487832096019/70368744177664000000000000000000), (-2677911335699806306486071597799/1125899906842624000000000000000000), (-5095152041267032983069304064533/2814749767106560000000000000000000), (-84473817317742322641822016831/562949953421312000000000000000000), (11987299934815473852665517641/175921860444160000000000000000000), (51836431133063679131473392789/5629499534213120000000000000000000), (-4906861342373780020376220219/5629499534213120000000000000000000), (-33113176134981046519027363/225179981368524800000000000000000), (6732328281299856711466297/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial164.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial164.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial164.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial164 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 3718040721029586773865135997835037), (Int.ofNat 17196935880060541889454613021758), (Int.negOfNat 56226565135562888841217133549270), (Int.ofNat 2738910399083036634139583598151), (Int.ofNat 4021610380597067517174974750423), (Int.ofNat 340263980443946029193891944806), (Int.negOfNat 67161287608219942152806303467), (Int.negOfNat 8094808140884304106376915451), (Int.ofNat 602722621372078861118073029), (Int.ofNat 87880045752056901208429576), (Int.negOfNat 3510851012236631791830539), (Int.negOfNat 594001157543146778757551), (Int.ofNat 14586723950089861577201), (Int.ofNat 2811457931765501134339), (Int.negOfNat 45812799816110468540), (Int.negOfNat 9989239456347052341), (Int.ofNat 96924573837820021), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-3718040721029586773865135997835037/5629499534213120000000000000000000), (8598467940030270944727306510879/2814749767106560000000000000000000), (-5622656513556288884121713354927/562949953421312000000000000000000), (2738910399083036634139583598151/5629499534213120000000000000000000), (4021610380597067517174974750423/5629499534213120000000000000000000), (170131990221973014596945972403/2814749767106560000000000000000000), (-67161287608219942152806303467/5629499534213120000000000000000000), (-8094808140884304106376915451/5629499534213120000000000000000000), (602722621372078861118073029/5629499534213120000000000000000000), (10985005719007112651053697/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial164.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial164.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial164.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial164 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 3816547509345062348507217009269492), (Int.negOfNat 34655692761626537315328470173499), (Int.ofNat 63817512447466905966027643116515), (Int.ofNat 34719373334356301087313523996462), (Int.ofNat 2087936033233122792425897439887), (Int.negOfNat 741995271940884594430991738331), (Int.negOfNat 73085469472343390633539988366), (Int.ofNat 8339848717331779956057108534), (Int.ofNat 983539152860796397546046352), (Int.negOfNat 60976243144884249613965913), (Int.negOfNat 7863316401617871494544519), (Int.ofNat 318303067863260194574069), (Int.ofNat 42925475103205630718366), (Int.negOfNat 1253419607372147189686), (Int.negOfNat 171933934467455928973), (Int.ofNat 3774041946682956173), (Int.ofNat 575278633023791535), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-954136877336265587126804252317373/1407374883553280000000000000000000), (-34655692761626537315328470173499/5629499534213120000000000000000000), (12763502489493381193205528623303/1125899906842624000000000000000000), (17359686667178150543656761998231/2814749767106560000000000000000000), (2087936033233122792425897439887/5629499534213120000000000000000000), (-741995271940884594430991738331/5629499534213120000000000000000000), (-36542734736171695316769994183/2814749767106560000000000000000000), (4169924358665889978028554267/2814749767106560000000000000000000), (61471197053799774846627897/351843720888320000000000000000000), (-60976243144884249613965913/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial164.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial164.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial164.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial164 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 3346567371054242347816441888905804), (Int.ofNat 635235960125246464614574198918794), (Int.ofNat 252351003844915658968161274702123), (Int.ofNat 16051398666631088336699438584080), (Int.negOfNat 6613698543336775284332707711126), (Int.negOfNat 650995713996305708005604919108), (Int.ofNat 93282649151495987499855608912), (Int.ofNat 10311655146534715539538937072), (Int.negOfNat 849216766797890786243834036), (Int.negOfNat 96099022899212478271294283), (Int.ofNat 5455321735243472784236109), (Int.ofNat 602780209075074513554691), (Int.negOfNat 26015589882770509830517), (Int.negOfNat 2737242727709815268404), (Int.ofNat 95441459456808361764), (Int.ofNat 9397337965644353707), (Int.negOfNat 283877099168696959), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-836641842763560586954110472226451/1407374883553280000000000000000000), (317617980062623232307287099459397/2814749767106560000000000000000000), (252351003844915658968161274702123/5629499534213120000000000000000000), (200642483332888604208742982301/70368744177664000000000000000000), (-3306849271668387642166353855563/2814749767106560000000000000000000), (-162748928499076427001401229777/1407374883553280000000000000000000), (5830165571968499218740975557/351843720888320000000000000000000), (644478446658419721221183567/351843720888320000000000000000000), (-212304191699472696560958509/1407374883553280000000000000000000), (-96099022899212478271294283/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial164.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial164.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial164.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial164.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial164 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial164 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial164 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 4872510222721731661845671058309631), (Int.negOfNat 864754971040725378802733572913146), (Int.ofNat 297348579356810651054699477014196), (Int.negOfNat 14115030410897594511921072738156), (Int.negOfNat 6853171180485986335488941956724), (Int.ofNat 645450462471751276607874388860), (Int.ofNat 93816800136607539348234593085), (Int.negOfNat 10303379917632539542800144622), (Int.negOfNat 849871076081814649718353836), (Int.ofNat 96091412227743770584626633), (Int.ofNat 5455826093085646361645659), (Int.negOfNat 602775236719894749453491), (Int.negOfNat 26015589882770509830517), (Int.ofNat 2737242727709815268404), (Int.ofNat 95441459456808361764), (Int.negOfNat 9397337965644353707), (Int.negOfNat 283877099168696959), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-4872510222721731661845671058309631/5629499534213120000000000000000000), (-432377485520362689401366786456573/2814749767106560000000000000000000), (74337144839202662763674869253549/1407374883553280000000000000000000), (-3528757602724398627980268184539/1407374883553280000000000000000000), (-1713292795121496583872235489181/1407374883553280000000000000000000), (32272523123587563830393719443/281474976710656000000000000000000), (18763360027321507869646918617/1125899906842624000000000000000000), (-5151689958816269771400072311/2814749767106560000000000000000000), (-212467769020453662429588459/1407374883553280000000000000000000), (96091412227743770584626633/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial164.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial164.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial164.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 5610021070975187666765798655435886), (Int.ofNat 362237827291375891585088594495), (Int.ofNat 114374889609297717468792213610525), (Int.negOfNat 34831703463913650242477624531807), (Int.ofNat 1826620442557213713937982907282), (Int.ofNat 743250661549825027648796547380), (Int.negOfNat 72512112050827720773450937066), (Int.negOfNat 8342635646454434521416316934), (Int.ofNat 982842793261004575100868252), (Int.ofNat 60979283330478800928448013), (Int.negOfNat 7862781445432309366189919), (Int.negOfNat 318304932496452606112019), (Int.ofNat 42925475103205630718366), (Int.ofNat 1253419607372147189686), (Int.negOfNat 171933934467455928973), (Int.negOfNat 3774041946682956173), (Int.ofNat 575278633023791535), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-2805010535487593833382899327717943/2814749767106560000000000000000000), (72447565458275178317017718899/1125899906842624000000000000000000), (4574995584371908698751688544421/225179981368524800000000000000000), (-34831703463913650242477624531807/5629499534213120000000000000000000), (913310221278606856968991453641/2814749767106560000000000000000000), (37162533077491251382439827369/281474976710656000000000000000000), (-36256056025413860386725468533/2814749767106560000000000000000000), (-4171317823227217260708158467/2814749767106560000000000000000000), (245710698315251143775217063/1407374883553280000000000000000000), (60979283330478800928448013/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial164.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial164.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial164.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 5382875039921938007206502778045642), (Int.ofNat 141237621267056211130025528122360), (Int.negOfNat 12379806575262020834465012427947), (Int.negOfNat 4802596595948517806081001484171), (Int.ofNat 3805709194850666576037201235678), (Int.negOfNat 332664018237331291673194538743), (Int.negOfNat 66701145351865912161285821637), (Int.ofNat 8081813117753224585414132251), (Int.ofNat 602172428803706283877240379), (Int.negOfNat 87867231942633300071198726), (Int.negOfNat 3510431153834125867936939), (Int.ofNat 593993077465979662093101), (Int.ofNat 14586723950089861577201), (Int.negOfNat 2811457931765501134339), (Int.negOfNat 45812799816110468540), (Int.ofNat 9989239456347052341), (Int.ofNat 96924573837820021), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-2691437519960969003603251389022821/2814749767106560000000000000000000), (3530940531676405278250638203059/140737488355328000000000000000000), (-12379806575262020834465012427947/5629499534213120000000000000000000), (-4802596595948517806081001484171/5629499534213120000000000000000000), (1902854597425333288018600617839/2814749767106560000000000000000000), (-332664018237331291673194538743/5629499534213120000000000000000000), (-66701145351865912161285821637/5629499534213120000000000000000000), (8081813117753224585414132251/5629499534213120000000000000000000), (602172428803706283877240379/5629499534213120000000000000000000), (-43933615971316650035599363/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial164.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial164.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial164.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 5141221272913283118000249374017548), (Int.ofNat 120473942766724660181024680502736), (Int.ofNat 13602232394472981661524243174930), (Int.ofNat 6768841451970911766403522673390), (Int.negOfNat 961229093214113982599940982136), (Int.negOfNat 371781045226949631906393655878), (Int.ofNat 52062908216045138723407651712), (Int.ofNat 4887262575858062515472434219), (Int.negOfNat 828085875899168816984579375), (Int.negOfNat 33642588461771969898353885), (Int.ofNat 7187286369639499356626844), (Int.ofNat 144908537332287280179128), (Int.negOfNat 41025356612613973600901), (Int.negOfNat 414965495534004367950), (Int.ofNat 168556007109689927611), (Int.ofNat 678265486735554325), (Int.negOfNat 532044322245288216), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-1285305318228320779500062343504387/1407374883553280000000000000000000), (7529621422920291261314042531421/351843720888320000000000000000000), (1360223239447298166152424317493/562949953421312000000000000000000), (676884145197091176640352267339/562949953421312000000000000000000), (-120153636651764247824992622767/703687441776640000000000000000000), (-185890522613474815953196827939/2814749767106560000000000000000000), (406741470437852646276622279/43980465111040000000000000000000), (4887262575858062515472434219/5629499534213120000000000000000000), (-1324937401438670107175327/9007199254740992000000000000000), (-6728517692354393979670777/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial164.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial164.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial164.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 4815254516510427780177594169270088), (Int.ofNat 206904674793012494051487180721080), (Int.ofNat 15627784440715718131353315120246), (Int.negOfNat 6278193416793668057335843837939), (Int.negOfNat 1152396097457803637192345343177), (Int.ofNat 282815765655236212125732061727), (Int.ofNat 29032891218269920379951656339), (Int.negOfNat 6554729765130605969897705553), (Int.negOfNat 259320024445839625475962274), (Int.ofNat 75335394399361383724093948), (Int.ofNat 1111939517256623170752160), (Int.negOfNat 530470151069189896419019), (Int.negOfNat 1653709820386264250091), (Int.ofNat 2573904662078052937605), (Int.negOfNat 7909702177423844847), (Int.negOfNat 9348318502104415740), (Int.ofNat 75616514566889144), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-601906814563803472522199271158761/703687441776640000000000000000000), (5172616869825312351287179518027/140737488355328000000000000000000), (7813892220357859065676657560123/2814749767106560000000000000000000), (-6278193416793668057335843837939/5629499534213120000000000000000000), (-1152396097457803637192345343177/5629499534213120000000000000000000), (282815765655236212125732061727/5629499534213120000000000000000000), (29032891218269920379951656339/5629499534213120000000000000000000), (-6554729765130605969897705553/5629499534213120000000000000000000), (-129660012222919812737981137/2814749767106560000000000000000000), (18833848599840345931023487/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial164.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial164.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial164.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 4397556458016366190501213585935866), (Int.ofNat 182371714150295143491987411520133), (Int.negOfNat 24629901307959533361062090586334), (Int.negOfNat 3274598555924057835150821417001), (Int.ofNat 1588961947286833561604351548646), (Int.ofNat 110240980162270874358417988031), (Int.negOfNat 44819014174626394463773586144), (Int.negOfNat 1365946995456737090207802720), (Int.ofNat 680973594113186898736083116), (Int.ofNat 4194316966079375880607111), (Int.negOfNat 6026330579943176354110210), (Int.ofNat 35664409311918855806376), (Int.ofNat 35079478445188106026121), (Int.negOfNat 426046106450881914088), (Int.negOfNat 145771670216571048241), (Int.ofNat 2244309626958298173), (Int.ofNat 488810011466784897), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-2198778229008183095250606792967933/2814749767106560000000000000000000), (182371714150295143491987411520133/5629499534213120000000000000000000), (-12314950653979766680531045293167/2814749767106560000000000000000000), (-3274598555924057835150821417001/5629499534213120000000000000000000), (794480973643416780802175774323/2814749767106560000000000000000000), (110240980162270874358417988031/5629499534213120000000000000000000), (-1400594192957074826992924567/175921860444160000000000000000000), (-8537168721604606813798767/35184372088832000000000000000000), (170243398528296724684020779/1407374883553280000000000000000000), (4194316966079375880607111/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial164.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial164.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial164.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 4131451062279380233375105438718597), (Int.ofNat 95683143054509643158612346261114), (Int.negOfNat 7824143037275411566113279075557), (Int.ofNat 7066282997710162355456065119551), (Int.ofNat 324029485249487374659294967839), (Int.negOfNat 273059595755867374955156934130), (Int.negOfNat 2697906568744050173690492497), (Int.ofNat 5320970922358012347281833899), (Int.negOfNat 45734937768561576671468559), (Int.negOfNat 59651744238738539357269824), (Int.ofNat 1127431475443044786361274), (Int.ofNat 422634689494532137157458), (Int.negOfNat 10279344813986491184047), (Int.negOfNat 2066551302444902414930), (Int.ofNat 56209116508531199885), (Int.ofNat 7585946499016053585), (Int.negOfNat 248157602971598309), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-4131451062279380233375105438718597/5629499534213120000000000000000000), (47841571527254821579306173130557/2814749767106560000000000000000000), (-7824143037275411566113279075557/5629499534213120000000000000000000), (7066282997710162355456065119551/5629499534213120000000000000000000), (324029485249487374659294967839/5629499534213120000000000000000000), (-27305959575586737495515693413/562949953421312000000000000000000), (-2697906568744050173690492497/5629499534213120000000000000000000), (5320970922358012347281833899/5629499534213120000000000000000000), (-45734937768561576671468559/5629499534213120000000000000000000), (-932058503730289677457341/87960930222080000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial164.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial164.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial164.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 3917936389064335728844228525536709), (Int.ofNat 139397847896679990017607511159082), (Int.ofNat 23100748834068479135138631698788), (Int.ofNat 915029581835819330928154246226), (Int.negOfNat 1339286224471603525080143702159), (Int.ofNat 20722815841114185066789168263), (Int.ofNat 35621838084817887777951140513), (Int.negOfNat 1139056248939308059553574190), (Int.negOfNat 509216246473018703021721265), (Int.ofNat 19691028925438743650624000), (Int.ofNat 4443321444491177916936670), (Int.negOfNat 186074354938624678062659), (Int.negOfNat 25839294451374276850105), (Int.ofNat 1120122986561524846789), (Int.ofNat 107293490682838843685), (Int.negOfNat 4712668540075804561), (Int.negOfNat 388062004553378523), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-3917936389064335728844228525536709/5629499534213120000000000000000000), (69698923948339995008803755579541/2814749767106560000000000000000000), (5775187208517119783784657924697/1407374883553280000000000000000000), (457514790917909665464077123113/2814749767106560000000000000000000), (-1339286224471603525080143702159/5629499534213120000000000000000000), (20722815841114185066789168263/5629499534213120000000000000000000), (35621838084817887777951140513/5629499534213120000000000000000000), (-113905624893930805955357419/562949953421312000000000000000000), (-101843249294603740604344253/1125899906842624000000000000000000), (307672326959980369541/87960930222080000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial164.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial164.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial164.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 3558165116077708731719084797893558), (Int.ofNat 207454980177814576526570593852665), (Int.ofNat 5112313485141420969644504493804), (Int.negOfNat 4657504470355351347910362838037), (Int.ofNat 244477412908083744551635921259), (Int.ofNat 192244102558602620014519027874), (Int.negOfNat 13159955814750721109289715685), (Int.negOfNat 3661929804796562445028991488), (Int.ofNat 256766411548337527063408743), (Int.ofNat 39950053873780454148905114), (Int.negOfNat 2768932179167635918737896), (Int.negOfNat 279484206034568671998351), (Int.ofNat 19077753904927363329709), (Int.ofNat 1354688304413757024273), (Int.negOfNat 91080320906543362385), (Int.negOfNat 4864437301009775845), (Int.ofNat 334362121389068873), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-1779082558038854365859542398946779/2814749767106560000000000000000000), (41490996035562915305314118770533/1125899906842624000000000000000000), (1278078371285355242411126123451/1407374883553280000000000000000000), (-4657504470355351347910362838037/5629499534213120000000000000000000), (244477412908083744551635921259/5629499534213120000000000000000000), (96122051279301310007259513937/2814749767106560000000000000000000), (-2631991162950144221857943137/1125899906842624000000000000000000), (-7152206649993286025447249/10995116277760000000000000000000), (256766411548337527063408743/5629499534213120000000000000000000), (19975026936890227074452557/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial164.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial164.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial164.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 3151230585375090958859359550354427), (Int.ofNat 191387908030869148559411686138515), (Int.negOfNat 6599018274417737723186267280291), (Int.ofNat 1454836284710042067453953613153), (Int.ofNat 754426999364104875425568742509), (Int.negOfNat 106024049870972515803886609134), (Int.negOfNat 20912015503866215581200777415), (Int.ofNat 2651662353096767796921527769), (Int.ofNat 295113314451584669427924189), (Int.negOfNat 34698026422806931359507090), (Int.negOfNat 2518831501833241618506802), (Int.ofNat 281504218313498538529032), (Int.ofNat 14340496168079886377767), (Int.negOfNat 1553948875268066194692), (Int.negOfNat 58271340254216720115), (Int.ofNat 6260280108755789921), (Int.ofNat 244211738431236867), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-3151230585375090958859359550354427/5629499534213120000000000000000000), (38277581606173829711882337227703/1125899906842624000000000000000000), (-6599018274417737723186267280291/5629499534213120000000000000000000), (1454836284710042067453953613153/5629499534213120000000000000000000), (754426999364104875425568742509/5629499534213120000000000000000000), (-53012024935486257901943304567/2814749767106560000000000000000000), (-4182403100773243116240155483/1125899906842624000000000000000000), (2651662353096767796921527769/5629499534213120000000000000000000), (295113314451584669427924189/5629499534213120000000000000000000), (-3469802642280693135950709/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial164.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial164.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial164.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 2775477219834815802598009708340231), (Int.ofNat 195495238883156574624358809538561), (Int.ofNat 8865926299632827228482757919357), (Int.ofNat 1704935418372758344247935364939), (Int.negOfNat 648200169967173794228487781268), (Int.negOfNat 83055341040203878568258892715), (Int.ofNat 22124025536409869694004752534), (Int.ofNat 1623229617725461985722549138), (Int.negOfNat 367441166257283415570663692), (Int.negOfNat 17293526481777708321591825), (Int.ofNat 3609076397827972073876966), (Int.ofNat 115829021547159608280104), (Int.negOfNat 23417870093862992808523), (Int.negOfNat 531039928247595168344), (Int.ofNat 108023882582063585949), (Int.ofNat 1683346740203345813), (Int.negOfNat 348641506745468609), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-2775477219834815802598009708340231/5629499534213120000000000000000000), (195495238883156574624358809538561/5629499534213120000000000000000000), (8865926299632827228482757919357/5629499534213120000000000000000000), (1704935418372758344247935364939/5629499534213120000000000000000000), (-162050042491793448557121945317/1407374883553280000000000000000000), (-16611068208040775713651778543/1125899906842624000000000000000000), (11062012768204934847002376267/2814749767106560000000000000000000), (811614808862730992861274569/2814749767106560000000000000000000), (-91860291564320853892665923/1407374883553280000000000000000000), (-691741059271108332863673/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial164.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial164.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial164.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 2346887900913754920866888870183302), (Int.ofNat 228609444080096209864512937382952), (Int.ofNat 2599952475907380362853405196367), (Int.negOfNat 3047834882143947422193226363709), (Int.negOfNat 127720105029819143445768543347), (Int.ofNat 149398820098094380744181702760), (Int.ofNat 4496292289015171847105387242), (Int.negOfNat 3273579324739421905264128995), (Int.negOfNat 62602647677960003463887622), (Int.ofNat 40004210938484046602282736), (Int.ofNat 466046243529073508621446), (Int.negOfNat 310706597133008258896981), (Int.negOfNat 2057495544730992036235), (Int.ofNat 1666692027164533024947), (Int.ofNat 5174411827309522753), (Int.negOfNat 6581508419227374776), (Int.negOfNat 71670650026527702), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-1173443950456877460433444435091651/2814749767106560000000000000000000), (28576180510012026233064117172869/703687441776640000000000000000000), (2599952475907380362853405196367/5629499534213120000000000000000000), (-3047834882143947422193226363709/5629499534213120000000000000000000), (-127720105029819143445768543347/5629499534213120000000000000000000), (3734970502452359518604542569/140737488355328000000000000000000), (2248146144507585923552693621/2814749767106560000000000000000000), (-654715864947884381052825799/1125899906842624000000000000000000), (-31301323838980001731943811/2814749767106560000000000000000000), (2500263183655252912642671/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial164.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial164.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial164.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 1901041594907890207757000770556699), (Int.ofNat 209723810382804278680478297787426), (Int.negOfNat 7852270436000519096336782546319), (Int.ofNat 889720697329574623866579381621), (Int.ofNat 804101812453556810217342698713), (Int.negOfNat 24126242491612592900037031370), (Int.negOfNat 24257845053851722302082932819), (Int.ofNat 415080523948497288219039903), (Int.ofNat 379433502424547896605809503), (Int.negOfNat 5227772744332222350439831), (Int.negOfNat 3598530400214545428819372), (Int.ofNat 46460351294605339684102), (Int.ofNat 22829542778427130350233), (Int.negOfNat 288942275932625746988), (Int.negOfNat 103280284593807299469), (Int.ofNat 1375502544132719409), (Int.ofNat 305407195966965290), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-1901041594907890207757000770556699/5629499534213120000000000000000000), (104861905191402139340239148893713/2814749767106560000000000000000000), (-7852270436000519096336782546319/5629499534213120000000000000000000), (889720697329574623866579381621/5629499534213120000000000000000000), (804101812453556810217342698713/5629499534213120000000000000000000), (-2412624249161259290003703137/562949953421312000000000000000000), (-24257845053851722302082932819/5629499534213120000000000000000000), (415080523948497288219039903/5629499534213120000000000000000000), (379433502424547896605809503/5629499534213120000000000000000000), (-5227772744332222350439831/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial164.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial164.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial164.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 1495200114722445279196807570196502), (Int.ofNat 208680113684706539714392879885793), (Int.ofNat 9928617562088010672723378591771), (Int.ofNat 3309618369297314607933700649301), (Int.negOfNat 416236310089772956222941105303), (Int.negOfNat 146431491300047922604865563194), (Int.ofNat 10345539449061690420950650945), (Int.ofNat 3029340232739376512827722957), (Int.negOfNat 149938651080002182806730193), (Int.negOfNat 35856054328015889846232838), (Int.ofNat 1415387724846701131937895), (Int.ofNat 273320064868212282599209), (Int.negOfNat 9239913878855287586915), (Int.negOfNat 1449943160596315318233), (Int.ofNat 43356104615833315510), (Int.ofNat 5723639933148562985), (Int.negOfNat 100870438378181463), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-747600057361222639598403785098251/2814749767106560000000000000000000), (208680113684706539714392879885793/5629499534213120000000000000000000), (9928617562088010672723378591771/5629499534213120000000000000000000), (3309618369297314607933700649301/5629499534213120000000000000000000), (-416236310089772956222941105303/5629499534213120000000000000000000), (-73215745650023961302432781597/2814749767106560000000000000000000), (2069107889812338084190130189/1125899906842624000000000000000000), (3029340232739376512827722957/5629499534213120000000000000000000), (-149938651080002182806730193/5629499534213120000000000000000000), (-17928027164007944923116419/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial164.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial164.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial164.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1021998971068175936589435382162556), (Int.ofNat 266193289106394002365023852795977), (Int.ofNat 12190035062325724396365262264534), (Int.negOfNat 2955404882123326456884733193826), (Int.negOfNat 695181151074666094681564558430), (Int.ofNat 110862433438539950352235299311), (Int.ofNat 19845890712056934300408524322), (Int.negOfNat 2097177311234354070819532568), (Int.negOfNat 300339860769461183575734816), (Int.ofNat 24021435103745483147491943), (Int.ofNat 2798820815748754949915137), (Int.negOfNat 182898619638185341895641), (Int.negOfNat 17604831139487938692608), (Int.ofNat 983638660491142626492), (Int.ofNat 79574636772578721657), (Int.negOfNat 4031095697675623061), (Int.negOfNat 262172885188461971), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-255499742767043984147358845540639/1407374883553280000000000000000000), (266193289106394002365023852795977/5629499534213120000000000000000000), (6095017531162862198182631132267/2814749767106560000000000000000000), (-1477702441061663228442366596913/2814749767106560000000000000000000), (-69518115107466609468156455843/562949953421312000000000000000000), (110862433438539950352235299311/5629499534213120000000000000000000), (9922945356028467150204262161/2814749767106560000000000000000000), (-262147163904294258852441571/703687441776640000000000000000000), (-9385620649045661986741713/175921860444160000000000000000000), (24021435103745483147491943/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial164.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial164.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial164.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 471131253404966976494786696271675), (Int.ofNat 268742339118018790907799876084565), (Int.negOfNat 10405469664478032252042147375425), (Int.negOfNat 2456883048205405139743668066942), (Int.ofNat 805549386926809024292375808654), (Int.ofNat 102493783432977946557093284150), (Int.negOfNat 21085922649196765819042690867), (Int.negOfNat 2033307065938517263965840176), (Int.ofNat 306843536852711071771124946), (Int.ofNat 23566199713412459317248581), (Int.negOfNat 2825970807421310282246165), (Int.negOfNat 178320409146473415074749), (Int.ofNat 17811922091588077767559), (Int.ofNat 946391759673356904158), (Int.negOfNat 81193264213200700916), (Int.negOfNat 3798046046618964229), (Int.ofNat 259000089856722855), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-18845250136198679059791467850867/225179981368524800000000000000000), (53748467823603758181559975216913/1125899906842624000000000000000000), (-416218786579121290081685895017/225179981368524800000000000000000), (-1228441524102702569871834033471/2814749767106560000000000000000000), (402774693463404512146187904327/2814749767106560000000000000000000), (2049875668659558931141865683/112589990684262400000000000000000), (-21085922649196765819042690867/5629499534213120000000000000000000), (-127081691621157328997865011/351843720888320000000000000000000), (153421768426355535885562473/2814749767106560000000000000000000), (23566199713412459317248581/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial164.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial164.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial164.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 19722748818851756427634829262868), (Int.ofNat 227008033037125563278294439194675), (Int.negOfNat 3418881659979262161449719704713), (Int.ofNat 4202697625316311151154029368410), (Int.ofNat 391688556558629060192170606423), (Int.negOfNat 162395272558628790186791578203), (Int.negOfNat 10288988061586409935249121993), (Int.ofNat 3130667092134667311921994114), (Int.ofNat 149394996392761257770565994), (Int.negOfNat 35937139139856314229546479), (Int.negOfNat 1375947048682250773680835), (Int.ofNat 271545751527774050476321), (Int.ofNat 8705328301621746795021), (Int.negOfNat 1443651280803954302272), (Int.negOfNat 39906469542876911404), (Int.ofNat 5716153569650783851), (Int.ofNat 118322619066320315), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(4930687204712939106908707315717/1407374883553280000000000000000000), (9080321321485022531131777567787/225179981368524800000000000000000), (-3418881659979262161449719704713/5629499534213120000000000000000000), (420269762531631115115402936841/562949953421312000000000000000000), (391688556558629060192170606423/5629499534213120000000000000000000), (-162395272558628790186791578203/5629499534213120000000000000000000), (-10288988061586409935249121993/5629499534213120000000000000000000), (1565333546067333655960997057/2814749767106560000000000000000000), (74697498196380628885282997/2814749767106560000000000000000000), (-35937139139856314229546479/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial164.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial164.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial164.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 494516483420575227747718492590068), (Int.ofNat 262800672154213438672394278173308), (Int.ofNat 17934920062837576943939545896146), (Int.ofNat 1012723067494072777333907956457), (Int.negOfNat 957065095846859788408493159711), (Int.negOfNat 31089726705980557563711602299), (Int.ofNat 25696460501977906354476939558), (Int.ofNat 513252288740289489519576482), (Int.negOfNat 379975203510671918001825324), (Int.negOfNat 5559177136152489826751987), (Int.ofNat 3524878561520354603748283), (Int.ofNat 42689898376565850448709), (Int.negOfNat 22258016685891395324922), (Int.negOfNat 239958660805641829038), (Int.ofNat 101126284273100028213), (Int.ofNat 1125170265044929869), (Int.negOfNat 345204608274193419), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(123629120855143806936929623147517/1407374883553280000000000000000000), (65700168038553359668098569543327/1407374883553280000000000000000000), (8967460031418788471969772948073/2814749767106560000000000000000000), (1012723067494072777333907956457/5629499534213120000000000000000000), (-957065095846859788408493159711/5629499534213120000000000000000000), (-31089726705980557563711602299/5629499534213120000000000000000000), (12848230250988953177238469779/2814749767106560000000000000000000), (256626144370144744759788241/2814749767106560000000000000000000), (-94993800877667979500456331/1407374883553280000000000000000000), (-5559177136152489826751987/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial164.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial164.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial164.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1085265134981838583036128899289285), (Int.ofNat 318359502604929543020496194672114), (Int.ofNat 4400345836429177575004140745810), (Int.negOfNat 4145889893337185884297324393322), (Int.ofNat 15922199466839511176003662639), (Int.ofNat 166399881789983440647822954383), (Int.negOfNat 2227708477789651255555640645), (Int.negOfNat 3303959038960730796957917683), (Int.ofNat 43766552456444067555862853), (Int.ofNat 38714950403504328973035122), (Int.negOfNat 417877704758397550284705), (Int.negOfNat 296715641352609647459491), (Int.ofNat 2393207614146798619235), (Int.ofNat 1591565914517394502987), (Int.negOfNat 9088501217857287100), (Int.negOfNat 6308055060353482485), (Int.ofNat 68629906264556623), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(217053026996367716607225779857857/1125899906842624000000000000000000), (159179751302464771510248097336057/2814749767106560000000000000000000), (440034583642917757500414074581/562949953421312000000000000000000), (-2072944946668592942148662196661/2814749767106560000000000000000000), (15922199466839511176003662639/5629499534213120000000000000000000), (166399881789983440647822954383/5629499534213120000000000000000000), (-445541695557930251111128129/1125899906842624000000000000000000), (-3303959038960730796957917683/5629499534213120000000000000000000), (43766552456444067555862853/5629499534213120000000000000000000), (19357475201752164486517561/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial164.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial164.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial164.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 1711462488905973034807770575660356), (Int.ofNat 298252489972976641892567778847810), (Int.negOfNat 9291714614475175947388283952466), (Int.ofNat 699159563453430140019523240804), (Int.ofNat 808977370790589616263353979267), (Int.negOfNat 51612308111254488838460975740), (Int.negOfNat 22886774426773160268738331739), (Int.ofNat 1225090830968317954892912473), (Int.ofNat 351656066382272209774951837), (Int.negOfNat 14942183826905961843753791), (Int.negOfNat 3363525609438686670155178), (Int.ofNat 111148805288874096735592), (Int.ofNat 21740358484631979316397), (Int.negOfNat 557191314278931845478), (Int.negOfNat 100526926102245758131), (Int.ofNat 1970606194902471979), (Int.ofNat 301970297495690100), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(427865622226493258701942643915089/1407374883553280000000000000000000), (29825248997297664189256777884781/562949953421312000000000000000000), (-4645857307237587973694141976233/2814749767106560000000000000000000), (174789890863357535004880810201/1407374883553280000000000000000000), (808977370790589616263353979267/5629499534213120000000000000000000), (-2580615405562724441923048787/281474976710656000000000000000000), (-22886774426773160268738331739/5629499534213120000000000000000000), (1225090830968317954892912473/5629499534213120000000000000000000), (351656066382272209774951837/5629499534213120000000000000000000), (-14942183826905961843753791/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial164.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial164.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial164.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 2286457228903579832562128163481383), (Int.ofNat 287698611028602536592090414534357), (Int.ofNat 6047191684247758111178155009428), (Int.ofNat 2635738911656623470108358382234), (Int.negOfNat 441773574448603338306023170151), (Int.negOfNat 117837980650288910159657207130), (Int.ofNat 15044447655879982446692041403), (Int.ofNat 2508644512920541913515490735), (Int.negOfNat 243399573100983626325252018), (Int.negOfNat 31210893751916479464964874), (Int.ofNat 2285005504092150629134644), (Int.ofNat 251139373651160939384519), (Int.negOfNat 13954166189963358048525), (Int.negOfNat 1396176717568120302073), (Int.ofNat 59893176687414291127), (Int.ofNat 5667134106110845884), (Int.negOfNat 241170994669265788), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(2286457228903579832562128163481383/5629499534213120000000000000000000), (287698611028602536592090414534357/5629499534213120000000000000000000), (1511797921061939527794538752357/1407374883553280000000000000000000), (1317869455828311735054179191117/2814749767106560000000000000000000), (-441773574448603338306023170151/5629499534213120000000000000000000), (-11783798065028891015965720713/562949953421312000000000000000000), (15044447655879982446692041403/5629499534213120000000000000000000), (501728902584108382703098147/1125899906842624000000000000000000), (-121699786550491813162626009/2814749767106560000000000000000000), (-15605446875958239732482437/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial164.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial164.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial164.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 2897498384033846517191242005202163), (Int.ofNat 323657826412434601663746936042481), (Int.ofNat 6580761586031541767888689046895), (Int.negOfNat 2360198945523238410038345211195), (Int.negOfNat 374401277614279227348780204405), (Int.ofNat 125511331900664875748509607715), (Int.ofNat 12248131396247886752987243806), (Int.negOfNat 2833308259915554817369039762), (Int.negOfNat 215068742746794624221578658), (Int.ofNat 34480150214404750182970875), (Int.ofNat 2299188563015058393072554), (Int.negOfNat 259509638442265142055246), (Int.negOfNat 16114314520828986928317), (Int.ofNat 1324615073799223760416), (Int.ofNat 78780215028334502521), (Int.negOfNat 4893181308596324477), (Int.negOfNat 258735986717186781), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(2897498384033846517191242005202163/5629499534213120000000000000000000), (323657826412434601663746936042481/5629499534213120000000000000000000), (1316152317206308353577737809379/1125899906842624000000000000000000), (-472039789104647682007669042239/1125899906842624000000000000000000), (-74880255522855845469756040881/1125899906842624000000000000000000), (25102266380132975149701921543/1125899906842624000000000000000000), (6124065698123943376493621903/2814749767106560000000000000000000), (-1416654129957777408684519881/2814749767106560000000000000000000), (-107534371373397312110789329/2814749767106560000000000000000000), (275841201715238001463767/45035996273704960000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial164.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial164.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial164.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 3550667015861246451303896841288880), (Int.ofNat 320668613008112255287203193169717), (Int.negOfNat 5697780441268084441261766050170), (Int.negOfNat 138970307615894629762695960180), (Int.ofNat 738868075921751506526785636153), (Int.ofNat 17385965104091114170560615298), (Int.negOfNat 25062504503980641562380046445), (Int.negOfNat 710027834770335993780369001), (Int.ofNat 414156665095020877610739181), (Int.ofNat 13321969696846399853947570), (Int.negOfNat 3948167172673531991606978), (Int.negOfNat 137088020885717309311178), (Int.ofNat 24303806144788071615883), (Int.ofNat 876141316504882328138), (Int.negOfNat 105037981690655977765), (Int.negOfNat 3904762103022483729), (Int.ofNat 413712083073974953), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(44383337698265580641298710516111/70368744177664000000000000000000), (320668613008112255287203193169717/5629499534213120000000000000000000), (-569778044126808444126176605017/562949953421312000000000000000000), (-6948515380794731488134798009/281474976710656000000000000000000), (738868075921751506526785636153/5629499534213120000000000000000000), (8692982552045557085280307649/2814749767106560000000000000000000), (-5012500900796128312476009289/1125899906842624000000000000000000), (-710027834770335993780369001/5629499534213120000000000000000000), (414156665095020877610739181/5629499534213120000000000000000000), (1332196969684639985394757/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial164.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial164.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial164.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 4178893340070398731856582609783884), (Int.ofNat 316548072431619010218962244218041), (Int.ofNat 6855922731457607971143279998617), (Int.ofNat 2810060041863286009089613383928), (Int.negOfNat 327829979563323022195225137526), (Int.negOfNat 163862433834426512890211978199), (Int.ofNat 6584478820500547869132831670), (Int.ofNat 3982609205819565511601832452), (Int.negOfNat 31245998697391724685964373), (Int.negOfNat 50418445039662299894819066), (Int.negOfNat 402173699506678179379514), (Int.ofNat 382851070536514377799309), (Int.ofNat 6017450773882079439281), (Int.negOfNat 1956862206648927999377), (Int.negOfNat 38679483528842369965), (Int.ofNat 7361540221713830865), (Int.ofNat 157987979803780407), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(1044723335017599682964145652445971/1407374883553280000000000000000000), (316548072431619010218962244218041/5629499534213120000000000000000000), (6855922731457607971143279998617/5629499534213120000000000000000000), (351257505232910751136201672991/703687441776640000000000000000000), (-163914989781661511097612568763/2814749767106560000000000000000000), (-163862433834426512890211978199/5629499534213120000000000000000000), (658447882050054786913283167/562949953421312000000000000000000), (995652301454891377900458113/1407374883553280000000000000000000), (-31245998697391724685964373/5629499534213120000000000000000000), (-25209222519831149947409533/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial164.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial164.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial164.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 4852302526522851444890172498181157), (Int.ofNat 356995493060848428709851386959335), (Int.ofNat 6713870225286052396404268290591), (Int.negOfNat 3400257602443923237628601795343), (Int.negOfNat 683743636757069833427422557530), (Int.ofNat 142074649242199475833550173134), (Int.ofNat 29184769649538016732647991447), (Int.negOfNat 2209092015903105760366674150), (Int.negOfNat 539910215497076553280472335), (Int.ofNat 13924880292983817062124250), (Int.ofNat 5239888958320342655738140), (Int.negOfNat 31953382872334350608229), (Int.negOfNat 32158008019191151950645), (Int.negOfNat 104663533497047832381), (Int.ofNat 138189108656085431305), (Int.ofNat 1183252905016205989), (Int.negOfNat 499916601491445517), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(4852302526522851444890172498181157/5629499534213120000000000000000000), (71399098612169685741970277391867/1125899906842624000000000000000000), (6713870225286052396404268290591/5629499534213120000000000000000000), (-3400257602443923237628601795343/5629499534213120000000000000000000), (-68374363675706983342742255753/562949953421312000000000000000000), (71037324621099737916775086567/2814749767106560000000000000000000), (29184769649538016732647991447/5629499534213120000000000000000000), (-44181840318062115207333483/112589990684262400000000000000000), (-107982043099415310656094467/1125899906842624000000000000000000), (55699521171935268248497/22517998136852480000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial164.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial164.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial164.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 5561012567217343367432405330424680), (Int.ofNat 336652764026067959714491012600839), (Int.negOfNat 14057743842651628134663923664109), (Int.negOfNat 571822828127159251943921409987), (Int.ofNat 1386091623509346949134671629225), (Int.ofNat 131077405961553420549966916948), (Int.negOfNat 37540359944098450111774859833), (Int.negOfNat 4747343482001000491649307631), (Int.ofNat 378805153709971721131954059), (Int.ofNat 62477156302574622010135076), (Int.negOfNat 2093304717185862929338914), (Int.negOfNat 469937702918870999901972), (Int.ofNat 7048681267655051425437), (Int.ofNat 2373899295145315362060), (Int.negOfNat 13566904896178211045), (Int.negOfNat 8909151790393816225), (Int.negOfNat 14137713681638751), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(139025314180433584185810133260617/140737488355328000000000000000000), (336652764026067959714491012600839/5629499534213120000000000000000000), (-14057743842651628134663923664109/5629499534213120000000000000000000), (-571822828127159251943921409987/5629499534213120000000000000000000), (55443664940373877965386865169/225179981368524800000000000000000), (32769351490388355137491729237/1407374883553280000000000000000000), (-37540359944098450111774859833/5629499534213120000000000000000000), (-4747343482001000491649307631/5629499534213120000000000000000000), (378805153709971721131954059/5629499534213120000000000000000000), (15619289075643655502533769/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial164.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial164.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial164.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 6197000141492257860190509110063950), (Int.ofNat 319582608821020583162262687081976), (Int.ofNat 14994017682538918966559677491495), (Int.ofNat 8059191987588231524045664439732), (Int.negOfNat 254902516406297443784231791519), (Int.negOfNat 451844368081713275094816041350), (Int.negOfNat 32667541310674254741993920306), (Int.ofNat 6238795181087969034711773340), (Int.ofNat 650336121662090278385045744), (Int.negOfNat 46738817286843081743255739), (Int.negOfNat 6138135171768852158393740), (Int.ofNat 228388849471676412916086), (Int.ofNat 36720437576704556215519), (Int.negOfNat 792890465742792416928), (Int.negOfNat 155766359211569349589), (Int.ofNat 1997837655790224043), (Int.ofNat 514195986847845253), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(123940002829845157203810182201279/112589990684262400000000000000000), (39947826102627572895282835885247/703687441776640000000000000000000), (2998803536507783793311935498299/1125899906842624000000000000000000), (2014797996897057881011416109933/1407374883553280000000000000000000), (-254902516406297443784231791519/5629499534213120000000000000000000), (-9036887361634265501896320827/112589990684262400000000000000000), (-16333770655337127370996960153/2814749767106560000000000000000000), (311939759054398451735588667/281474976710656000000000000000000), (40646007603880642399065359/351843720888320000000000000000000), (-46738817286843081743255739/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial164.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial164.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial164.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 6940922228388197887958523829383627), (Int.ofNat 429017612156055398154988878951587), (Int.ofNat 18324269985670412052474465347296), (Int.negOfNat 12953590270653238577754822164616), (Int.negOfNat 4515247043448190700237016263322), (Int.negOfNat 162103393348565237731463045687), (Int.ofNat 80744016472428027252985977973), (Int.ofNat 6008425526183815920315569617), (Int.negOfNat 762858215268014294092676116), (Int.negOfNat 72335548537508951959540872), (Int.ofNat 4703162667091920330327240), (Int.ofNat 515511036564598956508261), (Int.negOfNat 20763794476574497409709), (Int.negOfNat 2524307193197308603335), (Int.ofNat 69442402509997139687), (Int.ofNat 9230380100865401080), (Int.negOfNat 158403374723070414), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(6940922228388197887958523829383627/5629499534213120000000000000000000), (429017612156055398154988878951587/5629499534213120000000000000000000), (572633437052200376639827042103/175921860444160000000000000000000), (-1619198783831654822219352770577/703687441776640000000000000000000), (-2257623521724095350118508131661/2814749767106560000000000000000000), (-162103393348565237731463045687/5629499534213120000000000000000000), (80744016472428027252985977973/5629499534213120000000000000000000), (6008425526183815920315569617/5629499534213120000000000000000000), (-190714553817003573523169029/1407374883553280000000000000000000), (-9041943567188618994942609/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial164.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial164.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial164.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 7696904684713198935484014160901572), (Int.ofNat 206691482166978824882261677877770), (Int.negOfNat 158948686415539050145600257222945), (Int.negOfNat 40940853923522448608123625772524), (Int.negOfNat 673813701578556232280151796970), (Int.ofNat 874272900477427789368674370228), (Int.ofNat 52528628679900335102785129531), (Int.negOfNat 10136159423306036316132795481), (Int.negOfNat 786294696971927911003953345), (Int.ofNat 76678585317965286595165075), (Int.ofNat 6626217958657638952093486), (Int.negOfNat 411962957720278423328352), (Int.negOfNat 37466472737041016520049), (Int.ofNat 1658676133259230064280), (Int.ofNat 153940587747290372469), (Int.negOfNat 5056686940126289265), (Int.negOfNat 470961676069341934), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(1924226171178299733871003540225393/1407374883553280000000000000000000), (20669148216697882488226167787777/562949953421312000000000000000000), (-31789737283107810029120051444589/1125899906842624000000000000000000), (-10235213480880612152030906443131/1407374883553280000000000000000000), (-67381370157855623228015179697/562949953421312000000000000000000), (218568225119356947342168592557/1407374883553280000000000000000000), (52528628679900335102785129531/5629499534213120000000000000000000), (-10136159423306036316132795481/5629499534213120000000000000000000), (-157258939394385582200790669/1125899906842624000000000000000000), (3067143412718611463806603/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial164.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial164.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial164.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 7166069961404145509926860607318997), (Int.negOfNat 867069248442938777707531696947698), (Int.negOfNat 346021322179240179175819393979590), (Int.negOfNat 9548186287272013701037483884281), (Int.ofNat 7878680822014845096910718612697), (Int.ofNat 493642097475124510997373293294), (Int.negOfNat 111490813387825017649496269443), (Int.negOfNat 8199992837315719586881116389), (Int.ofNat 1038342862853225527902335061), (Int.ofNat 79201577684154914497432664), (Int.negOfNat 6770498980793533675424591), (Int.negOfNat 511876024653878654777239), (Int.ofNat 32484106110135802866159), (Int.ofNat 2381352362509609322321), (Int.negOfNat 119010544772347601710), (Int.negOfNat 8372511614786589289), (Int.ofNat 330944463127779579), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(7166069961404145509926860607318997/5629499534213120000000000000000000), (-433534624221469388853765848473849/2814749767106560000000000000000000), (-34602132217924017917581939397959/562949953421312000000000000000000), (-9548186287272013701037483884281/5629499534213120000000000000000000), (7878680822014845096910718612697/5629499534213120000000000000000000), (246821048737562255498686646647/2814749767106560000000000000000000), (-111490813387825017649496269443/5629499534213120000000000000000000), (-8199992837315719586881116389/5629499534213120000000000000000000), (1038342862853225527902335061/5629499534213120000000000000000000), (9900197210519364312179083/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial164.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial164.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial164.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 4105429650668594768203325602338562), (Int.negOfNat 2097997229022764155320900943564781), (Int.negOfNat 204863137013682183680219390099965), (Int.ofNat 52961553608464740289827114464598), (Int.ofNat 5204168395262955848651247443863), (Int.negOfNat 973997944093527842634163554779), (Int.negOfNat 84754872204292336568822439484), (Int.ofNat 11637275775001786794661114266), (Int.ofNat 896555264171987111127232578), (Int.negOfNat 94092510822018519171087507), (Int.negOfNat 6496386230493508563364401), (Int.ofNat 543346535585133241767011), (Int.ofNat 33933192425984194782204), (Int.negOfNat 2340484282971735433924), (Int.negOfNat 133389549253927463057), (Int.ofNat 7712280093669192917), (Int.ofNat 427727365290838615), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(2052714825334297384101662801169281/2814749767106560000000000000000000), (-2097997229022764155320900943564781/5629499534213120000000000000000000), (-40972627402736436736043878019993/1125899906842624000000000000000000), (26480776804232370144913557232299/2814749767106560000000000000000000), (5204168395262955848651247443863/5629499534213120000000000000000000), (-973997944093527842634163554779/5629499534213120000000000000000000), (-21188718051073084142205609871/1407374883553280000000000000000000), (5818637887500893397330557133/2814749767106560000000000000000000), (448277632085993555563616289/2814749767106560000000000000000000), (-94092510822018519171087507/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial164.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial164.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial164.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 437984985799564274962389315329976), (Int.negOfNat 2203682178212007429857089520412734), (Int.ofNat 148480858839103687890347241317717), (Int.ofNat 49618083698458740044972261441600), (Int.negOfNat 5798934691539480762423826564894), (Int.negOfNat 835320817913579623026911396392), (Int.ofNat 102968878211635364415957231458), (Int.ofNat 9624365669501185571247174178), (Int.negOfNat 1095023244754146651733467934), (Int.negOfNat 77129242701771517103140327), (Int.ofNat 7823721670277249776218961), (Int.ofNat 447123539059936399610799), (Int.negOfNat 40149782273497204199983), (Int.negOfNat 1943270099445632338186), (Int.ofNat 155225152403955059116), (Int.ofNat 6446917728256990533), (Int.negOfNat 489074114606320971), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-54748123224945534370298664416247/703687441776640000000000000000000), (-1101841089106003714928544760206367/2814749767106560000000000000000000), (148480858839103687890347241317717/5629499534213120000000000000000000), (31011302311536712528107663401/3518437208883200000000000000000), (-2899467345769740381211913282447/2814749767106560000000000000000000), (-104415102239197452878363924549/703687441776640000000000000000000), (51484439105817682207978615729/2814749767106560000000000000000000), (4812182834750592785623587089/2814749767106560000000000000000000), (-547511622377073325866733967/2814749767106560000000000000000000), (-77129242701771517103140327/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial164.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial164.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial164.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial164.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial164.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial164.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial164.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial164.reflect := by
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

end Bin164
end
end ErdosOverlap.OuterNumerics
