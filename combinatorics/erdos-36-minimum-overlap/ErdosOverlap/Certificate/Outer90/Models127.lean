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

/-! # Exact integer weighted outer models for source bin 127

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin127

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 8388421086623785000)⟩, ⟨(5980904522613/1000000000000), (Int.negOfNat 225490788711299320)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 3817564040891707000)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 587250838456134450)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 920875884526631700)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 145869944069065470)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 159007085175056070)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 665793138513388300)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 466641790927445700)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 28569346145637287)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial127.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial127.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 3547658575757772000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 235054514469487450)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 632387106338428200)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 214602996566944270)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 78301209705102010)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 192648694742048950)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 8712466389361630)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 60227836632461470)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 25326652617990424)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial127.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial127.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 3547658575757772000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 235054514469487450)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 632387106338428200)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 214602996566944270)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 78301209705102010)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 192648694742048950)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 8712466389361630)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 60227836632461470)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 25326652617990424)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial127.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial127.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial127.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 15985440587489586359638091239358465), (Int.ofNat 2224473058124465480130837215425997), (Int.ofNat 800919018800923012389221668472660), (Int.negOfNat 84955160433243855702370955531095), (Int.negOfNat 19286202811746679903984676875906), (Int.ofNat 2028453366669889339701674275570), (Int.ofNat 297335819065227506623356149677), (Int.negOfNat 26836869142267930670506041215), (Int.negOfNat 2787625097395602267152003471), (Int.ofNat 218133778327059526187848623), (Int.ofNat 17047347509768953054206077), (Int.negOfNat 1198669991732276661161763), (Int.negOfNat 72860384577462310464712), (Int.ofNat 4773540107581271724265), (Int.ofNat 229858337865731125956), (Int.negOfNat 14625212397577600168), (Int.negOfNat 517756442580151061), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-3197088117497917271927618247871693/2251799813685248000000000000000000), (2224473058124465480130837215425997/11258999068426240000000000000000000), (40045950940046150619461083423633/562949953421312000000000000000000), (-16991032086648771140474191106219/2251799813685248000000000000000000), (-9643101405873339951992338437953/5629499534213120000000000000000000), (202845336666988933970167427557/1125899906842624000000000000000000), (297335819065227506623356149677/11258999068426240000000000000000000), (-5367373828453586134101208243/2251799813685248000000000000000000), (-2787625097395602267152003471/11258999068426240000000000000000000), (218133778327059526187848623/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial127.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial127.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial127.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial127 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.negOfNat 9241121245594933535523722951325101), (Int.ofNat 3996590866128884156881276399826258), (Int.ofNat 40089956119163603666746879704165), (Int.negOfNat 129179752722024452575709034163658), (Int.ofNat 9252722178720748616874197311739), (Int.ofNat 2629488306675864015615798494560), (Int.negOfNat 207575102734355608845822977185), (Int.negOfNat 31239064691498250508968033646), (Int.ofNat 2275394489775908813248492891), (Int.ofNat 231227650761420563303360388), (Int.negOfNat 15543882681789740217982646), (Int.negOfNat 1153371880173042521423952), (Int.ofNat 73558087959175033343515), (Int.ofNat 4117051644639394013083), (Int.negOfNat 257800484953297850845), (Int.negOfNat 11013185668295551425), (Int.ofNat 707705987786406935), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-9241121245594933535523722951325101/11258999068426240000000000000000000), (1998295433064442078440638199913129/5629499534213120000000000000000000), (8017991223832720733349375940833/2251799813685248000000000000000000), (-64589876361012226287854517081829/5629499534213120000000000000000000), (9252722178720748616874197311739/11258999068426240000000000000000000), (16434301916724150097598740591/70368744177664000000000000000000), (-41515020546871121769164595437/2251799813685248000000000000000000), (-15619532345749125254484016823/5629499534213120000000000000000000), (2275394489775908813248492891/11258999068426240000000000000000000), (57806912690355140825840097/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial127.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial127.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial127.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial127 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.negOfNat 1905430995835855940015656523542106), (Int.ofNat 3062162482761153130935657069120170), (Int.negOfNat 368437855218669324982952085359785), (Int.ofNat 4358060550846851751473372734581), (Int.ofNat 17579823400268290029047831723051), (Int.negOfNat 1150889367603471794516721220319), (Int.negOfNat 298937677418731516825620588639), (Int.ofNat 19641608488133970149966821932), (Int.ofNat 2813207632139077975726430609), (Int.negOfNat 175735193236116835306136532), (Int.negOfNat 16865310222052197712970051), (Int.ofNat 1015267397982316088409225), (Int.ofNat 69715531542567534967366), (Int.negOfNat 4169352214488202592608), (Int.negOfNat 209115064260412053451), (Int.ofNat 12692539134978501799), (Int.ofNat 406721751525248776), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-952715497917927970007828261771053/5629499534213120000000000000000000), (306216248276115313093565706912017/1125899906842624000000000000000000), (-73687571043733864996590417071957/2251799813685248000000000000000000), (4358060550846851751473372734581/11258999068426240000000000000000000), (17579823400268290029047831723051/11258999068426240000000000000000000), (-1150889367603471794516721220319/11258999068426240000000000000000000), (-298937677418731516825620588639/11258999068426240000000000000000000), (4910402122033492537491705483/2814749767106560000000000000000000), (2813207632139077975726430609/11258999068426240000000000000000000), (-43933798309029208826534133/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial127.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial127.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial127.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial127 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 3008453124726796893634130518177627), (Int.ofNat 2064996781392673411237317511916853), (Int.negOfNat 66921000183369646872251570894206), (Int.ofNat 66017196100678758680780251569243), (Int.negOfNat 4100105005614505197323214348575), (Int.negOfNat 2282671857837265744458164430305), (Int.ofNat 134454277317808818643095492468), (Int.ofNat 29757302886597843248371875676), (Int.negOfNat 1693671478880357657988906018), (Int.negOfNat 223478510917493734263608360), (Int.ofNat 12381122087104420701309783), (Int.ofNat 1099057149625344935908459), (Int.negOfNat 60888306203639175791927), (Int.negOfNat 3795758222472692562693), (Int.ofNat 218051905490533470010), (Int.ofNat 9213531038133192345), (Int.negOfNat 631726029932435663), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(3008453124726796893634130518177627/11258999068426240000000000000000000), (2064996781392673411237317511916853/11258999068426240000000000000000000), (-33460500091684823436125785447103/5629499534213120000000000000000000), (66017196100678758680780251569243/11258999068426240000000000000000000), (-164004200224580207892928573943/450359962737049600000000000000000), (-456534371567453148891632886061/2251799813685248000000000000000000), (33613569329452204660773873117/2814749767106560000000000000000000), (7439325721649460812092968919/2814749767106560000000000000000000), (-846835739440178828994453009/5629499534213120000000000000000000), (-5586962772937343356590209/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial127.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial127.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial127.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial127 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 7272133736157825026234983217004415), (Int.ofNat 2312673403593054268363171946704089), (Int.ofNat 96535940427009841074080116565502), (Int.negOfNat 23921418161290805833741709556311), (Int.negOfNat 13121532461506131400804367073807), (Int.ofNat 746258176073697327679031603480), (Int.ofNat 264789616952467689578187169132), (Int.negOfNat 13685475422909302355959877224), (Int.negOfNat 2627737814314890252052883390), (Int.ofNat 131461268951627571412034518), (Int.ofNat 15884672512840356869819697), (Int.negOfNat 793522662161607067279823), (Int.negOfNat 64577296108467804281910), (Int.ofNat 3347508478099344044136), (Int.ofNat 186647602420668579224), (Int.negOfNat 10693599705882741816), (Int.negOfNat 321013713088336915), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(1454426747231565005246996643400883/2251799813685248000000000000000000), (2312673403593054268363171946704089/11258999068426240000000000000000000), (48267970213504920537040058282751/5629499534213120000000000000000000), (-23921418161290805833741709556311/11258999068426240000000000000000000), (-13121532461506131400804367073807/11258999068426240000000000000000000), (18656454401842433191975790087/281474976710656000000000000000000), (66197404238116922394546792283/2814749767106560000000000000000000), (-1710684427863662794494984653/1407374883553280000000000000000000), (-262773781431489025205288339/1125899906842624000000000000000000), (65730634475813785706017259/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial127.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial127.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial127.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial127 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 11920792510307464824511313493132477), (Int.ofNat 2093963360520390435519157961079864), (Int.negOfNat 251802081504950585882120978839983), (Int.negOfNat 68138754061296219013670606282450), (Int.ofNat 4156652124816496854543828633893), (Int.ofNat 1961296723411874563635274317935), (Int.negOfNat 94100126867922258407332958210), (Int.negOfNat 26945433318681549848477478125), (Int.ofNat 1203035794904447308348318968), (Int.ofNat 207405181870210567433796987), (Int.negOfNat 9116585915059184572886272), (Int.negOfNat 1018449885603738223686641), (Int.ofNat 46077531524049142044228), (Int.ofNat 3439707787131391559914), (Int.negOfNat 168120481282219083473), (Int.negOfNat 8529063906552755471), (Int.ofNat 555746072078464391), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(11920792510307464824511313493132477/11258999068426240000000000000000000), (261745420065048804439894745134983/1407374883553280000000000000000000), (-251802081504950585882120978839983/11258999068426240000000000000000000), (-1362775081225924380273412125649/225179981368524800000000000000000), (4156652124816496854543828633893/11258999068426240000000000000000000), (392259344682374912727054863587/2251799813685248000000000000000000), (-9410012686792225840733295821/1125899906842624000000000000000000), (-8622538661978095951512793/3602879701896396800000000000000), (150379474363055913543539871/1407374883553280000000000000000000), (207405181870210567433796987/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial127.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial127.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial127.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial127 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 14676600339773810220474904243365438), (Int.ofNat 530520729144351289594677781206964), (Int.negOfNat 441681123178860358062622564132788), (Int.ofNat 16514728420886910862412237039642), (Int.ofNat 12603908460114697165070344346867), (Int.negOfNat 572250817056701555806255581590), (Int.negOfNat 239574377386924360731558354721), (Int.ofNat 9501138094456073589597437525), (Int.ofNat 2420106797238322304615742905), (Int.negOfNat 91223056814064719150104101), (Int.negOfNat 14715970661896835396335032), (Int.ofNat 561803103482144469611091), (Int.ofNat 59231103897193759693055), (Int.negOfNat 2410467994114640370243), (Int.negOfNat 165903839142765603296), (Int.ofNat 7508133520596828641), (Int.ofNat 235305674651425054), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(7338300169886905110237452121682719/5629499534213120000000000000000000), (132630182286087822398669445301741/2814749767106560000000000000000000), (-110420280794715089515655641033197/2814749767106560000000000000000000), (8257364210443455431206118519821/5629499534213120000000000000000000), (12603908460114697165070344346867/11258999068426240000000000000000000), (-57225081705670155580625558159/1125899906842624000000000000000000), (-239574377386924360731558354721/11258999068426240000000000000000000), (380045523778242943583897501/450359962737049600000000000000000), (484021359447664460923148581/2251799813685248000000000000000000), (-91223056814064719150104101/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial127.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial127.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial127.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial127 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 14272828170408460095144065392646113), (Int.negOfNat 720023483714744065692153047877258), (Int.negOfNat 133225769792307924915608754950635), (Int.ofNat 65094667012733983526938406669884), (Int.negOfNat 2657611538189959613063042226930), (Int.negOfNat 1845738180213469797756792124759), (Int.ofNat 64918599490075643166804558205), (Int.ofNat 25103081894451795136036550739), (Int.negOfNat 784247343662508138719966392), (Int.negOfNat 193138551708343042905598976), (Int.ofNat 5952156780514102230405305), (Int.ofNat 943677370805641046167888), (Int.negOfNat 30552309617824951159253), (Int.negOfNat 3142318539350162220987), (Int.ofNat 111721795905715392553), (Int.ofNat 7031952542004118129), (Int.negOfNat 451196768078855832), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(14272828170408460095144065392646113/11258999068426240000000000000000000), (-360011741857372032846076523938629/5629499534213120000000000000000000), (-26645153958461584983121750990127/2251799813685248000000000000000000), (16273666753183495881734601667471/2814749767106560000000000000000000), (-265761153818995961306304222693/1125899906842624000000000000000000), (-1845738180213469797756792124759/11258999068426240000000000000000000), (12983719898015128633360911641/2251799813685248000000000000000000), (25103081894451795136036550739/11258999068426240000000000000000000), (-98030917957813517339995799/1407374883553280000000000000000000), (-188611866902678752837499/10995116277760000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial127.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial127.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial127.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial127 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 12726126262961216142412795954484445), (Int.negOfNat 681990490104283458836005873374155), (Int.ofNat 76147505767373124656767554015564), (Int.negOfNat 7867714364873083053929174205088), (Int.negOfNat 11733136659695238349703743771876), (Int.ofNat 373137048322300649463435610189), (Int.ofNat 230293202254897630574511374071), (Int.negOfNat 5619973000938407763356212355), (Int.negOfNat 2288519906055904500793543838), (Int.ofNat 52853995974734747484395264), (Int.ofNat 13787385585169741047158491), (Int.negOfNat 331371638982408049453874), (Int.negOfNat 55062397343282215691751), (Int.ofNat 1444443932243927600205), (Int.ofNat 152891928744221284963), (Int.negOfNat 4664870304229747499), (Int.negOfNat 228820287596131328), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(2545225252592243228482559190896889/2251799813685248000000000000000000), (-136398098020856691767201174674831/2251799813685248000000000000000000), (19036876441843281164191888503891/2814749767106560000000000000000000), (-245866073902283845435286693909/351843720888320000000000000000000), (-2933284164923809587425935942969/2814749767106560000000000000000000), (373137048322300649463435610189/11258999068426240000000000000000000), (230293202254897630574511374071/11258999068426240000000000000000000), (-1123994600187681552671242471/2251799813685248000000000000000000), (-1144259953027952250396771919/5629499534213120000000000000000000), (206460921776307607360919/43980465111040000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial127.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial127.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial127.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial127 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 11441477626710576260998536746963558), (Int.negOfNat 777879971697552507740973097153849), (Int.negOfNat 175020764964232577676739532172980), (Int.negOfNat 56732380627131755978405601619355), (Int.ofNat 2057197213398112061249594320828), (Int.ofNat 1842292310458633162257587053990), (Int.negOfNat 30591239576696072990200278005), (Int.negOfNat 24317734846719042846391156393), (Int.ofNat 355382842844461202051531633), (Int.ofNat 183293584308493000333930989), (Int.negOfNat 2845294689514548097863758), (Int.negOfNat 888451434891300242194451), (Int.ofNat 15312413193132997485655), (Int.ofNat 2952598684562699787349), (Int.negOfNat 57375915344587134320), (Int.negOfNat 6948692911604363315), (Int.ofNat 343404770551600410), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(5720738813355288130499268373481779/5629499534213120000000000000000000), (-777879971697552507740973097153849/11258999068426240000000000000000000), (-8751038248211628883836976608649/562949953421312000000000000000000), (-11346476125426351195681120323871/2251799813685248000000000000000000), (514299303349528015312398580207/2814749767106560000000000000000000), (184229231045863316225758705399/1125899906842624000000000000000000), (-6118247915339214598040055601/2251799813685248000000000000000000), (-24317734846719042846391156393/11258999068426240000000000000000000), (355382842844461202051531633/11258999068426240000000000000000000), (183293584308493000333930989/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial127.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial127.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial127.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial127 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 8818753755336484286369799553584393), (Int.negOfNat 1961543596283122876228241946592847), (Int.negOfNat 340917200320066243116891684040123), (Int.ofNat 16447894613888985037113968193361), (Int.ofNat 12899924064157137535121883373310), (Int.negOfNat 85528570351572963972787099192), (Int.negOfNat 229264762446336388046849619102), (Int.ofNat 1016973518064588118944957061), (Int.ofNat 2196529830326314697538121272), (Int.negOfNat 13950190026632199189364151), (Int.negOfNat 13073760709809790722239058), (Int.ofNat 111216188798614493819715), (Int.ofNat 52336668106483712447898), (Int.negOfNat 534540380992180379674), (Int.negOfNat 147000164851572247983), (Int.ofNat 1218208237489477397), (Int.ofNat 276230899304465313), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(8818753755336484286369799553584393/11258999068426240000000000000000000), (-1961543596283122876228241946592847/11258999068426240000000000000000000), (-340917200320066243116891684040123/11258999068426240000000000000000000), (16447894613888985037113968193361/11258999068426240000000000000000000), (1289992406415713753512188337331/1125899906842624000000000000000000), (-10691071293946620496598387399/1407374883553280000000000000000000), (-114632381223168194023424809551/5629499534213120000000000000000000), (1016973518064588118944957061/11258999068426240000000000000000000), (274566228790789337192265159/1407374883553280000000000000000000), (-13950190026632199189364151/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial127.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial127.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial127.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial127 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 3853242234020696683604029429543457), (Int.negOfNat 2763292946216836255270615011759049), (Int.ofNat 9913742357260937445064943745561), (Int.ofNat 83783990643968395774305675516115), (Int.ofNat 812649857651868950309343437791), (Int.negOfNat 1892510516231659216784541930076), (Int.negOfNat 17803183917080328839339780851), (Int.ofNat 23396344535798433808998805418), (Int.ofNat 105394287035309189750825206), (Int.negOfNat 173468622470465225030941200), (Int.negOfNat 94600015887230995074781), (Int.ofNat 844973273492743782889397), (Int.negOfNat 1617327528927565328776), (Int.negOfNat 2864779949940966687124), (Int.ofNat 8339535976501319420), (Int.ofNat 6961685126630880840), (Int.negOfNat 257696732114688549), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(3853242234020696683604029429543457/11258999068426240000000000000000000), (-2763292946216836255270615011759049/11258999068426240000000000000000000), (9913742357260937445064943745561/11258999068426240000000000000000000), (16756798128793679154861135103223/2251799813685248000000000000000000), (812649857651868950309343437791/11258999068426240000000000000000000), (-473127629057914804196135482519/2814749767106560000000000000000000), (-17803183917080328839339780851/11258999068426240000000000000000000), (11698172267899216904499402709/5629499534213120000000000000000000), (52697143517654594875412603/5629499534213120000000000000000000), (-433671556176163062577353/28147497671065600000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial127.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial127.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial127.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial127 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.negOfNat 1009179605386322680003093615781017), (Int.negOfNat 1836845688010847410430810292779763), (Int.ofNat 391581690885919367548668180690946), (Int.ofNat 24127748250476944793236613159653), (Int.negOfNat 13177859290877116462564059493048), (Int.negOfNat 420208666845540473430145730885), (Int.ofNat 216452186308640910031165465946), (Int.ofNat 4133073048150299133820161908), (Int.negOfNat 2042334500016986829150934400), (Int.negOfNat 22411755705888277395250346), (Int.ofNat 12279727196188057162936341), (Int.ofNat 77370087375403055717021), (Int.negOfNat 50474686256030284790375), (Int.negOfNat 215644182085593008357), (Int.ofNat 148526376913789950302), (Int.ofNat 1068536630076363577), (Int.negOfNat 352210857158436585), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-1009179605386322680003093615781017/11258999068426240000000000000000000), (-1836845688010847410430810292779763/11258999068426240000000000000000000), (195790845442959683774334090345473/5629499534213120000000000000000000), (24127748250476944793236613159653/11258999068426240000000000000000000), (-1647232411359639557820507436631/1407374883553280000000000000000000), (-84041733369108094686029146177/2251799813685248000000000000000000), (108226093154320455015582732973/5629499534213120000000000000000000), (1033268262037574783455040477/2814749767106560000000000000000000), (-638229531255308384109667/3518437208883200000000000000000), (-11205877852944138697625173/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial127.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial127.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial127.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial127 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.negOfNat 3133954470221632580468233778906626), (Int.negOfNat 394964178106800533984789716382682), (Int.ofNat 237565927689468541827964973808749), (Int.negOfNat 64750704725166606108468187730212), (Int.negOfNat 5451349204853506727316269628031), (Int.ofNat 1660522343824623014305544344385), (Int.ofNat 69997629527410707740672050455), (Int.negOfNat 20813042703660247281316942450), (Int.negOfNat 513895811354217166327174311), (Int.ofNat 158154695285664209576250516), (Int.ofNat 2441094643251842970677809), (Int.negOfNat 798777365894755099743533), (Int.negOfNat 8751091389924553774656), (Int.ofNat 2845060583211707030252), (Int.ofNat 27823412237969901711), (Int.negOfNat 6930924431292736653), (Int.ofNat 171988693677776688), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-1566977235110816290234116889453313/5629499534213120000000000000000000), (-197482089053400266992394858191341/5629499534213120000000000000000000), (237565927689468541827964973808749/11258999068426240000000000000000000), (-16187676181291651527117046932553/2814749767106560000000000000000000), (-5451349204853506727316269628031/11258999068426240000000000000000000), (332104468764924602861108868877/2251799813685248000000000000000000), (13999525905482141548134410091/2251799813685248000000000000000000), (-416260854073204945626338849/225179981368524800000000000000000), (-513895811354217166327174311/11258999068426240000000000000000000), (39538673821416052394062629/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial127.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial127.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial127.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial127 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.negOfNat 3523943577593155461250804571014565), (Int.negOfNat 259353411484927562318754518191188), (Int.negOfNat 146302457289709066473523230198578), (Int.negOfNat 42463340285251429805750355435424), (Int.ofNat 9587204588537863677851090477641), (Int.ofNat 836935249536149966227627709880), (Int.negOfNat 176158852364822880788751124993), (Int.negOfNat 8044691753112562352722325030), (Int.ofNat 1764915754360835227694436215), (Int.ofNat 47768695938733738908074522), (Int.negOfNat 11205858799752341071056456), (Int.negOfNat 202090372066266948806272), (Int.ofNat 48847560772124293960315), (Int.ofNat 699200223175425001011), (Int.negOfNat 154385273869382567103), (Int.negOfNat 2125816614477733197), (Int.ofNat 428190815012407857), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-704788715518631092250160914202913/2251799813685248000000000000000000), (-64838352871231890579688629547797/2814749767106560000000000000000000), (-73151228644854533236761615099289/5629499534213120000000000000000000), (-1326979383914107181429698607357/351843720888320000000000000000000), (9587204588537863677851090477641/11258999068426240000000000000000000), (20923381238403749155690692747/281474976710656000000000000000000), (-176158852364822880788751124993/11258999068426240000000000000000000), (-804469175311256235272232503/1125899906842624000000000000000000), (352983150872167045538887243/2251799813685248000000000000000000), (23884347969366869454037261/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial127.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial127.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial127.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial127 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 4799229047128178369298772369550637), (Int.negOfNat 1015945576618396176815538069983042), (Int.negOfNat 148467506953683726912327572984013), (Int.ofNat 38265727839676366127022453754257), (Int.ofNat 7150963119703021512739020612831), (Int.negOfNat 1157059403909429462073732867678), (Int.negOfNat 96731465101495727779553889875), (Int.ofNat 16493718192231920568471388967), (Int.ofNat 726443192775024651110075459), (Int.negOfNat 136854681110546235818053813), (Int.negOfNat 3640186016976446127367185), (Int.ofNat 744851922667379544909799), (Int.ofNat 13969348835000236310936), (Int.negOfNat 2860382524253330060571), (Int.negOfNat 46627018864600656376), (Int.ofNat 7976671415283422332), (Int.negOfNat 111607307858855251), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-4799229047128178369298772369550637/11258999068426240000000000000000000), (-507972788309198088407769034991521/5629499534213120000000000000000000), (-148467506953683726912327572984013/11258999068426240000000000000000000), (38265727839676366127022453754257/11258999068426240000000000000000000), (7150963119703021512739020612831/11258999068426240000000000000000000), (-578529701954714731036866433839/5629499534213120000000000000000000), (-773851720811965822236431119/90071992547409920000000000000000), (16493718192231920568471388967/11258999068426240000000000000000000), (726443192775024651110075459/11258999068426240000000000000000000), (-136854681110546235818053813/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial127.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial127.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial127.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial127 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 7045440783234510143453562048749682), (Int.negOfNat 1025125553690424309916873706192839), (Int.ofNat 148704126827060399054063499547568), (Int.ofNat 43492826309441134772162922783414), (Int.negOfNat 5360221588993613276144374497105), (Int.negOfNat 889695407575180871105463730343), (Int.ofNat 122540722170852932073057905483), (Int.ofNat 8881508332416930170419907465), (Int.negOfNat 1418054520654118363272218329), (Int.negOfNat 54184582464558420031781573), (Int.ofNat 9958448856098540999047423), (Int.ofNat 235668092057852644781423), (Int.negOfNat 47266744108011767951968), (Int.negOfNat 833719582710597925065), (Int.ofNat 161637168739546351224), (Int.ofNat 2951552137164881408), (Int.negOfNat 535982812539663279), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-3522720391617255071726781024374841/5629499534213120000000000000000000), (-1025125553690424309916873706192839/11258999068426240000000000000000000), (9294007926691274940878968721723/703687441776640000000000000000000), (21746413154720567386081461391707/5629499534213120000000000000000000), (-1072044317798722655228874899421/2251799813685248000000000000000000), (-889695407575180871105463730343/11258999068426240000000000000000000), (122540722170852932073057905483/11258999068426240000000000000000000), (1776301666483386034083981493/2251799813685248000000000000000000), (-1418054520654118363272218329/11258999068426240000000000000000000), (-54184582464558420031781573/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial127.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial127.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial127.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial127 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 8258567414093931110520518172520343), (Int.negOfNat 125115594009490131042677862021612), (Int.ofNat 242545536580125249678500100483668), (Int.negOfNat 13071580541102534073739634104418), (Int.negOfNat 6086931555038237366661946410477), (Int.ofNat 664692680106592070443157748023), (Int.ofNat 85741796248594562767175253035), (Int.negOfNat 12021954812957110209443931604), (Int.negOfNat 666560858946932903897903961), (Int.ofNat 114696664094817749286048202), (Int.ofNat 3382957808228820819422006), (Int.negOfNat 690328175548534425655388), (Int.negOfNat 13020309591920217460985), (Int.ofNat 2889587150786203447977), (Int.ofNat 43609768971213729465), (Int.negOfNat 8509814967675031215), (Int.ofNat 105121920803561525), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-8258567414093931110520518172520343/11258999068426240000000000000000000), (-31278898502372532760669465505403/2814749767106560000000000000000000), (60636384145031312419625025120917/2814749767106560000000000000000000), (-6535790270551267036869817052209/5629499534213120000000000000000000), (-6086931555038237366661946410477/11258999068426240000000000000000000), (664692680106592070443157748023/11258999068426240000000000000000000), (17148359249718912553435050607/2251799813685248000000000000000000), (-3005488703239277552360982901/2814749767106560000000000000000000), (-666560858946932903897903961/11258999068426240000000000000000000), (57348332047408874643024101/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial127.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial127.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial127.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial127 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 7715471068277828449182658651888574), (Int.ofNat 557268863849047412236032147469518), (Int.ofNat 83057554925976446829536836369816), (Int.negOfNat 28748603355154621975616341369347), (Int.ofNat 2069998443618997098079267348827), (Int.ofNat 622875916934280451868941706179), (Int.negOfNat 79108898931043368067564007141), (Int.negOfNat 6576679954847055405543079212), (Int.ofNat 1112319603410813572548073971), (Int.ofNat 40466763982664970873164542), (Int.negOfNat 8811170076471326293732829), (Int.negOfNat 171730696126178408676605), (Int.ofNat 45833118758809164202504), (Int.ofNat 593488841231357130428), (Int.negOfNat 170373500818398142769), (Int.negOfNat 1684672013079171339), (Int.ofNat 647017503594565564), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-3857735534138914224591329325944287/5629499534213120000000000000000000), (278634431924523706118016073734759/5629499534213120000000000000000000), (10382194365747055853692104546227/1407374883553280000000000000000000), (-28748603355154621975616341369347/11258999068426240000000000000000000), (2069998443618997098079267348827/11258999068426240000000000000000000), (622875916934280451868941706179/11258999068426240000000000000000000), (-79108898931043368067564007141/11258999068426240000000000000000000), (-1644169988711763851385769803/2814749767106560000000000000000000), (1112319603410813572548073971/11258999068426240000000000000000000), (20233381991332485436582271/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial127.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial127.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial127.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial127 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 6451248439607507923328381516742128), (Int.ofNat 643636947032678750062892195608205), (Int.negOfNat 11253158615070605760455114128206), (Int.negOfNat 1540502841754946806384392328317), (Int.ofNat 2999886366431952212805784468121), (Int.negOfNat 370436791397669770407318996918), (Int.negOfNat 48844298323351674093401295431), (Int.ofNat 8833923389407161114500616194), (Int.ofNat 382793096843746748294505308), (Int.negOfNat 96884883827359935112190340), (Int.negOfNat 1793049613403064733933263), (Int.ofNat 643128439496892042461731), (Int.ofNat 6132416100924093551117), (Int.negOfNat 2911486986992586750947), (Int.negOfNat 19207987356575190670), (Int.ofNat 9643676459324001995), (Int.negOfNat 181101878657532797), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-403203027475469245208023844796383/703687441776640000000000000000000), (128727389406535750012578439121641/2251799813685248000000000000000000), (-5626579307535302880227557064103/5629499534213120000000000000000000), (-1540502841754946806384392328317/11258999068426240000000000000000000), (2999886366431952212805784468121/11258999068426240000000000000000000), (-185218395698834885203659498459/5629499534213120000000000000000000), (-48844298323351674093401295431/11258999068426240000000000000000000), (4416961694703580557250308097/5629499534213120000000000000000000), (95698274210936687073626327/2814749767106560000000000000000000), (-4844244191367996755609517/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial127.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial127.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial127.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial127 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 5187114418813821348257157719302763), (Int.ofNat 641246008262797065185253173852218), (Int.ofNat 16316843441694284816341315059495), (Int.ofNat 4937604045304839312616158958867), (Int.negOfNat 1120766944011640074979992740115), (Int.negOfNat 234118370858610862064625359384), (Int.ofNat 55813044229283233583813604948), (Int.ofNat 2524505042283152624502704354), (Int.negOfNat 902172490940697291853327240), (Int.negOfNat 11985828947457073397014958), (Int.ofNat 7900640733535789238643463), (Int.ofNat 25594487387779089431263), (Int.negOfNat 44451454461303061034480), (Int.negOfNat 19997618203086554976), (Int.ofNat 175765860249387449436), (Int.ofNat 351525722496799656), (Int.negOfNat 732725542031477425), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-5187114418813821348257157719302763/11258999068426240000000000000000000), (320623004131398532592626586926109/5629499534213120000000000000000000), (3263368688338856963268263011899/2251799813685248000000000000000000), (4937604045304839312616158958867/11258999068426240000000000000000000), (-224153388802328014995998548023/2251799813685248000000000000000000), (-29264796357326357758078169923/1407374883553280000000000000000000), (13953261057320808395953401237/2814749767106560000000000000000000), (1262252521141576312251352177/5629499534213120000000000000000000), (-22554312273517432296333181/281474976710656000000000000000000), (-5992914473728536698507479/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial127.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial127.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial127.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial127 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 3821612213271364444571370880717552), (Int.ofNat 722105927448599293017089639197102), (Int.ofNat 13823058889950426023822703988221), (Int.negOfNat 4613034418924491735293591621751), (Int.negOfNat 363264479846969421572025744972), (Int.ofNat 279490469262438873154024257729), (Int.ofNat 6481043644758143531268060530), (Int.negOfNat 6970786963779381170126077125), (Int.ofNat 17325020253671443193267012), (Int.ofNat 83760592921463417133801583), (Int.negOfNat 744919065638070331176958), (Int.negOfNat 601484677482603399078739), (Int.ofNat 5501294693942699223952), (Int.ofNat 2896037535614782827706), (Int.negOfNat 20830274030392948807), (Int.negOfNat 9662350452391050569), (Int.ofNat 257081836511504069), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-238850763329460277785710680044847/703687441776640000000000000000000), (361052963724299646508544819598551/5629499534213120000000000000000000), (13823058889950426023822703988221/11258999068426240000000000000000000), (-4613034418924491735293591621751/11258999068426240000000000000000000), (-90816119961742355393006436243/2814749767106560000000000000000000), (279490469262438873154024257729/11258999068426240000000000000000000), (648104364475814353126806053/1125899906842624000000000000000000), (-55766295710235049361008617/90071992547409920000000000000000), (4331255063417860798316753/2814749767106560000000000000000000), (83760592921463417133801583/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial127.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial127.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial127.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial127 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 2356313037194808119878119463939055), (Int.ofNat 731098392620019916631284680828866), (Int.negOfNat 2950862021564705557132390389206), (Int.ofNat 1239723108837294870001260877768), (Int.ofNat 1192098922193003540125714015603), (Int.negOfNat 73991739371754454289491383379), (Int.negOfNat 43357419530072741209468838339), (Int.ofNat 1909317617415642466851603985), (Int.ofNat 747908200007395773299369375), (Int.negOfNat 25009584961748882434820169), (Int.negOfNat 7119493488435879028838298), (Int.ofNat 178853573058061289835669), (Int.ofNat 42681234509761643402315), (Int.negOfNat 803677168380742379997), (Int.negOfNat 177063265207629446024), (Int.ofNat 2168147324275725219), (Int.ofNat 818433580468389286), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-471262607438961623975623892787811/2251799813685248000000000000000000), (365549196310009958315642340414433/5629499534213120000000000000000000), (-1475431010782352778566195194603/5629499534213120000000000000000000), (154965388604661858750157609721/1407374883553280000000000000000000), (1192098922193003540125714015603/11258999068426240000000000000000000), (-73991739371754454289491383379/11258999068426240000000000000000000), (-43357419530072741209468838339/11258999068426240000000000000000000), (381863523483128493370320797/2251799813685248000000000000000000), (1196653120011833237278991/18014398509481984000000000000000), (-25009584961748882434820169/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial127.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial127.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial127.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial127 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 881654649299583237334748982930726), (Int.ofNat 759604983341809296147870565689389), (Int.ofNat 19206512909339158077174954929264), (Int.ofNat 3057322099014352983148887400062), (Int.negOfNat 961023876568215641223510401157), (Int.negOfNat 197485097847000313081165688184), (Int.ofNat 31276824663567518459629849668), (Int.ofNat 5306807247740127850090672871), (Int.negOfNat 473086266932519523567876428), (Int.negOfNat 71950048563922338006230404), (Int.ofNat 3896531237722177328285025), (Int.ofNat 557402709939393599350172), (Int.negOfNat 20353931697737022114817), (Int.negOfNat 2814674485272886520913), (Int.ofNat 73840345385318863367), (Int.ofNat 9827875539912911311), (Int.negOfNat 361631140511112628), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-440827324649791618667374491465363/5629499534213120000000000000000000), (759604983341809296147870565689389/11258999068426240000000000000000000), (1200407056833697379823434683079/703687441776640000000000000000000), (1528661049507176491574443700031/5629499534213120000000000000000000), (-961023876568215641223510401157/11258999068426240000000000000000000), (-24685637230875039135145711023/1407374883553280000000000000000000), (7819206165891879614907462417/2814749767106560000000000000000000), (5306807247740127850090672871/11258999068426240000000000000000000), (-118271566733129880891969107/2814749767106560000000000000000000), (-17987512140980584501557601/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial127.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial127.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial127.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial127 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.ofNat 719672106949770655533604848646364), (Int.ofNat 834325304510254703831637495347434), (Int.ofNat 8639155422710737600563227161461), (Int.negOfNat 5708392068037807025450618208320), (Int.negOfNat 320912539277549928770752135685), (Int.ofNat 311630847233636687308931260054), (Int.ofNat 23827327422530546246749139639), (Int.negOfNat 6717261217453439140956777355), (Int.negOfNat 586641770748483047604477542), (Int.ofNat 68102995343321524336214926), (Int.ofNat 6336655231320972006366969), (Int.negOfNat 420114376736902667699396), (Int.negOfNat 40194598876130687376099), (Int.ofNat 1775742394349697263355), (Int.ofNat 171515457845044628857), (Int.negOfNat 5011410540642806361), (Int.negOfNat 824918967523683012), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(179918026737442663883401212161591/2814749767106560000000000000000000), (417162652255127351915818747673717/5629499534213120000000000000000000), (8639155422710737600563227161461/11258999068426240000000000000000000), (-17838725212618146954533181901/35184372088832000000000000000000), (-64182507855509985754150427137/2251799813685248000000000000000000), (155815423616818343654465630027/5629499534213120000000000000000000), (23827327422530546246749139639/11258999068426240000000000000000000), (-1343452243490687828191355471/2251799813685248000000000000000000), (-293320885374241523802238771/5629499534213120000000000000000000), (34051497671660762168107463/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial127.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial127.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial127.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial127 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.ofNat 2382605096406589489512294144783310), (Int.ofNat 816191026179346871077706405169782), (Int.negOfNat 7856721276747910324404491116876), (Int.ofNat 3630800691682203180645374438707), (Int.ofNat 2024887596953097130497289340066), (Int.negOfNat 56869050856236241210865403136), (Int.negOfNat 76945643653914459623944364935), (Int.negOfNat 3191728048556986255785325707), (Int.ofNat 1007013699029545794332856607), (Int.ofNat 60562371206842288503777231), (Int.negOfNat 7458183536879645831043562), (Int.negOfNat 510167927408749777379659), (Int.ofNat 36805579174790874308925), (Int.ofNat 2660424761470432299151), (Int.negOfNat 130520321806560779600), (Int.negOfNat 9911135170312666125), (Int.ofNat 469423138038368050), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(238260509640658948951229414478331/1125899906842624000000000000000000), (408095513089673435538853202584891/5629499534213120000000000000000000), (-1964180319186977581101122779219/2814749767106560000000000000000000), (3630800691682203180645374438707/11258999068426240000000000000000000), (1012443798476548565248644670033/5629499534213120000000000000000000), (-222144729907172817229942981/43980465111040000000000000000000), (-15389128730782891924788872987/2251799813685248000000000000000000), (-3191728048556986255785325707/11258999068426240000000000000000000), (1007013699029545794332856607/11258999068426240000000000000000000), (60562371206842288503777231/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial127.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial127.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial127.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial127 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.ofNat 4038132290264726411386777579526842), (Int.ofNat 873504984863036749826780985136061), (Int.ofNat 39350276571485755034208824238600), (Int.ofNat 5455324006426427529273019735533), (Int.negOfNat 2798490981165422988192859429821), (Int.negOfNat 745866609708548550721183333531), (Int.ofNat 1890267049428067017421551422), (Int.ofNat 12941736579316089189820924129), (Int.ofNat 450521089545390028459859038), (Int.negOfNat 116488245298454496696458029), (Int.negOfNat 5677201675632003665690402), (Int.ofNat 675454200681230030579365), (Int.ofNat 37241980795751500249882), (Int.negOfNat 2777800491611280410386), (Int.negOfNat 161450851446598638197), (Int.ofNat 8458072607383076463), (Int.ofNat 777508355815349027), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(2019066145132363205693388789763421/5629499534213120000000000000000000), (873504984863036749826780985136061/11258999068426240000000000000000000), (196751382857428775171044121193/56294995342131200000000000000000), (5455324006426427529273019735533/11258999068426240000000000000000000), (-2798490981165422988192859429821/11258999068426240000000000000000000), (-745866609708548550721183333531/11258999068426240000000000000000000), (945133524714033508710775711/5629499534213120000000000000000000), (12941736579316089189820924129/11258999068426240000000000000000000), (225260544772695014229929519/5629499534213120000000000000000000), (-116488245298454496696458029/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial127.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial127.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial127.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial127 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.ofNat 5919371279255077204494346894729839), (Int.ofNat 953482005313381592785444884562148), (Int.negOfNat 45374183654292058187061824473592), (Int.negOfNat 39091751051366176730852813911387), (Int.negOfNat 6529357374543897397593187671523), (Int.ofNat 307832097023170116612792229952), (Int.ofNat 147657353252896333100642996887), (Int.ofNat 2076737179399927003400642382), (Int.negOfNat 1618524877371771044358453136), (Int.negOfNat 54646319383975999898901840), (Int.ofNat 11100653937221780648316981), (Int.ofNat 471273437065704524093523), (Int.negOfNat 52872705935052469219754), (Int.negOfNat 2451952315735532898766), (Int.ofNat 186248188222098388640), (Int.ofNat 8566556678259372000), (Int.negOfNat 555131176475279911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(5919371279255077204494346894729839/11258999068426240000000000000000000), (238370501328345398196361221140537/2814749767106560000000000000000000), (-5671772956786507273382728059199/1407374883553280000000000000000000), (-39091751051366176730852813911387/11258999068426240000000000000000000), (-6529357374543897397593187671523/11258999068426240000000000000000000), (4809876515987033072074878593/175921860444160000000000000000000), (147657353252896333100642996887/11258999068426240000000000000000000), (1038368589699963501700321191/5629499534213120000000000000000000), (-101157804835735690272403321/703687441776640000000000000000000), (-683078992299699998736273/140737488355328000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial127.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial127.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial127.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial127 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.ofNat 7246771126532346520624801410818478), (Int.ofNat 146129442369085470787610864402859), (Int.negOfNat 378184312405274866511304331697314), (Int.negOfNat 57235460351092282605570296933615), (Int.ofNat 4118522537415562697799996905092), (Int.ofNat 1516395614332683825498047125198), (Int.negOfNat 503963889177187304885442896), (Int.negOfNat 20060004574719825025286835298), (Int.negOfNat 460498924882409390501891560), (Int.ofNat 163857292589911391017755126), (Int.ofNat 5431838729588941995981699), (Int.negOfNat 910792151259991642001051), (Int.negOfNat 34426838527979709786595), (Int.ofNat 3677012840058672288117), (Int.ofNat 145041671144492465038), (Int.negOfNat 11410610613462305737), (Int.negOfNat 701528397961377755), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(3623385563266173260312400705409239/5629499534213120000000000000000000), (146129442369085470787610864402859/11258999068426240000000000000000000), (-189092156202637433255652165848657/5629499534213120000000000000000000), (-11447092070218456521114059386723/2251799813685248000000000000000000), (1029630634353890674449999226273/2814749767106560000000000000000000), (758197807166341912749023562599/5629499534213120000000000000000000), (-31497743073574206555340181/703687441776640000000000000000000), (-10030002287359912512643417649/5629499534213120000000000000000000), (-11512473122060234762547289/281474976710656000000000000000000), (81928646294955695508877563/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial127.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial127.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial127.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial127 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.ofNat 5680199760034709560990023201720556), (Int.negOfNat 1809489712631597700407684092078890), (Int.negOfNat 515077087161483608230387009535368), (Int.ofNat 25152236466549071672386371553245), (Int.ofNat 13811983846346929033277770047154), (Int.negOfNat 35954861685948003067604699754), (Int.negOfNat 219170165709266433905993576135), (Int.negOfNat 3852348151971171271124571550), (Int.ofNat 2160753708292062655446444201), (Int.ofNat 58830377569672304733628404), (Int.negOfNat 14189480930248196158917679), (Int.negOfNat 450778222656449350277687), (Int.ofNat 66228234556417139837076), (Int.ofNat 2221083230421805571488), (Int.negOfNat 230972712980889080231), (Int.negOfNat 7931524235084127887), (Int.ofNat 640839214912191772), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(1420049940008677390247505800430139/2814749767106560000000000000000000), (-180948971263159770040768409207889/1125899906842624000000000000000000), (-64384635895185451028798376191921/1407374883553280000000000000000000), (5030447293309814334477274310649/2251799813685248000000000000000000), (6905991923173464516638885023577/5629499534213120000000000000000000), (-17977430842974001533802349877/5629499534213120000000000000000000), (-43834033141853286781198715227/2251799813685248000000000000000000), (-77046963039423425422491431/225179981368524800000000000000000), (2160753708292062655446444201/11258999068426240000000000000000000), (14707594392418076183407101/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial127.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial127.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial127.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial127 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.ofNat 408019179017748913550541409660445), (Int.negOfNat 3170398506145555285900679811206938), (Int.negOfNat 86770318996660848585489734895351), (Int.ofNat 100944649721397463873349329163784), (Int.ofNat 1680020710727213157844063337075), (Int.negOfNat 2023535840324980411972567733027), (Int.negOfNat 41693207544527593839669099967), (Int.ofNat 25001363517035647547880912230), (Int.ofNat 638001148593538787478886555), (Int.negOfNat 198449236246419879053902182), (Int.negOfNat 5634445811804472583844524), (Int.ofNat 1086394265442868155878612), (Int.ofNat 32034797081740722852455), (Int.negOfNat 4346665035737868328511), (Int.negOfNat 127336854998431577477), (Int.ofNat 13133683736377063657), (Int.ofNat 625548440107406483), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(81603835803549782710108281932089/2251799813685248000000000000000000), (-1585199253072777642950339905603469/5629499534213120000000000000000000), (-86770318996660848585489734895351/11258999068426240000000000000000000), (12618081215174682984168666145473/1407374883553280000000000000000000), (67200828429088526313762533483/450359962737049600000000000000000), (-2023535840324980411972567733027/11258999068426240000000000000000000), (-41693207544527593839669099967/11258999068426240000000000000000000), (2500136351703564754788091223/1125899906842624000000000000000000), (127600229718707757495777311/2251799813685248000000000000000000), (-99224618123209939526951091/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial127.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial127.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial127.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial127 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 5509584646231612026087627455399806), (Int.negOfNat 2410890655353788273797589959918572), (Int.ofNat 404325718945111078709146161979940), (Int.ofNat 40811277973272012632696490391006), (Int.negOfNat 14169595054113299391771085927948), (Int.negOfNat 549574335514482949281654042372), (Int.ofNat 244431653418754714247648121029), (Int.ofNat 7261752742401952525457519783), (Int.negOfNat 2452272316581241015105824729), (Int.negOfNat 69045825623292907418320567), (Int.ofNat 16121130993726307734382085), (Int.ofNat 443266664495974881341031), (Int.negOfNat 74966291415624392784236), (Int.negOfNat 1987762842742780389619), (Int.ofNat 261154451291258270856), (Int.ofNat 6219984112580053908), (Int.negOfNat 701220600731113209), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-2754792323115806013043813727699903/5629499534213120000000000000000000), (-602722663838447068449397489979643/2814749767106560000000000000000000), (20216285947255553935457308098997/562949953421312000000000000000000), (20405638986636006316348245195503/5629499534213120000000000000000000), (-3542398763528324847942771481987/2814749767106560000000000000000000), (-137393583878620737320413510593/2814749767106560000000000000000000), (244431653418754714247648121029/11258999068426240000000000000000000), (7261752742401952525457519783/11258999068426240000000000000000000), (-2452272316581241015105824729/11258999068426240000000000000000000), (-69045825623292907418320567/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial127.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial127.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial127.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial127.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial127 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial127 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial127 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 16902900224629850359997057706835341), (Int.ofNat 1285083238248792836100980101675961), (Int.ofNat 769123782541109129525710780369700), (Int.negOfNat 93735261199063950828086254353843), (Int.negOfNat 17948880868771327933969124266150), (Int.ofNat 2269486637212261922604761436018), (Int.ofNat 284103239246347537124417533345), (Int.negOfNat 28732020227962652890333233103), (Int.negOfNat 2783097209935810056062548159), (Int.ofNat 222018135087170203879566987), (Int.ofNat 17971764295741066791543885), (Int.negOfNat 1154342535836301886616331), (Int.negOfNat 82108448951795678943536), (Int.ofNat 4316785783562669916869), (Int.ofNat 281128245446659919856), (Int.negOfNat 12212122359200548608), (Int.negOfNat 701220600731113209), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-16902900224629850359997057706835341/11258999068426240000000000000000000), (1285083238248792836100980101675961/11258999068426240000000000000000000), (7691237825411091295257107803697/112589990684262400000000000000000), (-93735261199063950828086254353843/11258999068426240000000000000000000), (-358977617375426558679382485323/225179981368524800000000000000000), (1134743318606130961302380718009/5629499534213120000000000000000000), (56820647849269507424883506669/2251799813685248000000000000000000), (-28732020227962652890333233103/11258999068426240000000000000000000), (-2783097209935810056062548159/11258999068426240000000000000000000), (222018135087170203879566987/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial127.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial127.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial127.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 12206757377761831419719312018095389), (Int.ofNat 2883364745976879160875154808086586), (Int.ofNat 2580376096922570468032859274337), (Int.negOfNat 120754510889559456003577288725250), (Int.ofNat 11709527295437601476646311972339), (Int.ofNat 2570131933280967297269810314740), (Int.negOfNat 241064832311615886024567688837), (Int.negOfNat 31640510439853292990956771630), (Int.ofNat 2493694778311804798515405315), (Int.ofNat 245543279833477598694266632), (Int.negOfNat 16203093221429952814490514), (Int.negOfNat 1305152734117998856508312), (Int.ofNat 72968544660544408074955), (Int.ofNat 5063724245916787527611), (Int.negOfNat 242519067961247753377), (Int.negOfNat 15131063151917228557), (Int.ofNat 625548440107406483), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-12206757377761831419719312018095389/11258999068426240000000000000000000), (1441682372988439580437577404043293/5629499534213120000000000000000000), (2580376096922570468032859274337/11258999068426240000000000000000000), (-483018043558237824014309154901/45035996273704960000000000000000), (11709527295437601476646311972339/11258999068426240000000000000000000), (128506596664048364863490515737/562949953421312000000000000000000), (-241064832311615886024567688837/11258999068426240000000000000000000), (-3164051043985329299095677163/1125899906842624000000000000000000), (498738955662360959703081063/2251799813685248000000000000000000), (30692909979184699836783329/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial127.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial127.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial127.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 7144878769508782370868612178947238), (Int.ofNat 1967511797166187844304258853219130), (Int.negOfNat 309043072104187193048935832934193), (Int.ofNat 24932154857434175567751376655905), (Int.ofNat 17608498113328357930045019065671), (Int.negOfNat 1528733757152870927309618692491), (Int.negOfNat 308262600284116818232218813035), (Int.ofNat 23449068066576730366461381760), (Int.ofNat 3004014369663494816141754301), (Int.negOfNat 198552124704432392683797064), (Int.negOfNat 19004724419391265515767199), (Int.ofNat 1100292788332643456543637), (Int.ofNat 84888459937093875617526), (Int.negOfNat 4348958101110594578288), (Int.negOfNat 283570370923446755931), (Int.ofNat 12592076204677845987), (Int.ofNat 640839214912191772), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-3572439384754391185434306089473619/5629499534213120000000000000000000), (196751179716618784430425885321913/1125899906842624000000000000000000), (-309043072104187193048935832934193/11258999068426240000000000000000000), (4986430971486835113550275331181/2251799813685248000000000000000000), (17608498113328357930045019065671/11258999068426240000000000000000000), (-1528733757152870927309618692491/11258999068426240000000000000000000), (-61652520056823363646443762607/2251799813685248000000000000000000), (36639168854026141197595909/17592186044416000000000000000000), (3004014369663494816141754301/11258999068426240000000000000000000), (-24819015588054049085474633/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial127.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial127.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial127.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 4029830591412312912720232376426497), (Int.ofNat 1425552931065884148369266339519717), (Int.ofNat 86915125233157391131862525252378), (Int.ofNat 72538696600428703791984982054891), (Int.negOfNat 7244954470307639522600523574119), (Int.negOfNat 2426439016117795748791073745705), (Int.ofNat 179342785435827163177239940600), (Int.ofNat 32060954682800617055063699788), (Int.negOfNat 2087024616618150464210927590), (Int.negOfNat 250089462390533169217819476), (Int.ofNat 14653867050853830292655679), (Int.ofNat 1312231172380976318958351), (Int.negOfNat 70112527874558694770595), (Int.negOfNat 4992620081761127568917), (Int.ofNat 245576435060014098338), (Int.ofNat 14073783167515858937), (Int.negOfNat 701528397961377755), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-4029830591412312912720232376426497/11258999068426240000000000000000000), (1425552931065884148369266339519717/11258999068426240000000000000000000), (43457562616578695565931262626189/5629499534213120000000000000000000), (72538696600428703791984982054891/11258999068426240000000000000000000), (-7244954470307639522600523574119/11258999068426240000000000000000000), (-485287803223559149758214749141/2251799813685248000000000000000000), (896713927179135815886199703/56294995342131200000000000000000), (8015238670700154263765924947/2814749767106560000000000000000000), (-208702461661815046421092759/1125899906842624000000000000000000), (-62522365597633292304454869/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial127.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial127.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial127.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 429383189845060025142996435159569), (Int.ofNat 2263895781226278623792604558941297), (Int.ofNat 214048477508572286310655325927190), (Int.negOfNat 40642589353284789999831357505787), (Int.negOfNat 14875587314362968285125794246723), (Int.ofNat 1128133224851717324116345829420), (Int.ofNat 290003436391946349411437880828), (Int.negOfNat 18545857509361695041947536252), (Int.negOfNat 2923047701910590719080258306), (Int.ofNat 170417583691348906840515610), (Int.ofNat 18515525461549781421540861), (Int.negOfNat 1008088715990932759216123), (Int.negOfNat 81581511528411602850554), (Int.ofNat 4209567659110820756916), (Int.ofNat 266809157982218372940), (Int.negOfNat 13227108647853090100), (Int.negOfNat 555131176475279911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-429383189845060025142996435159569/11258999068426240000000000000000000), (2263895781226278623792604558941297/11258999068426240000000000000000000), (21404847750857228631065532592719/1125899906842624000000000000000000), (-40642589353284789999831357505787/11258999068426240000000000000000000), (-14875587314362968285125794246723/11258999068426240000000000000000000), (56406661242585866205817291471/562949953421312000000000000000000), (72500859097986587352859470207/2814749767106560000000000000000000), (-4636464377340423760486884063/2814749767106560000000000000000000), (-1461523850955295359540129153/5629499534213120000000000000000000), (17041758369134890684051561/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial127.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial127.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial127.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.ofNat 4443094337297649750119675219993429), (Int.ofNat 2291463730461168257159027581473024), (Int.negOfNat 243705148079063870491746629924587), (Int.negOfNat 82594993879793476844072769915138), (Int.ofNat 6224123636581247737881152091361), (Int.ofNat 2197205327429064486678428509395), (Int.negOfNat 138923746501593640806126956438), (Int.negOfNat 29835302562671645351214666309), (Int.ofNat 1712485599737734826962529248), (Int.ofNat 235634758928325993684228159), (Int.negOfNat 12815577095509543707119832), (Int.negOfNat 1228332706095670115377165), (Int.ofNat 64848895112047029705332), (Int.ofNat 4588092035229183198086), (Int.negOfNat 238682855514151680997), (Int.negOfNat 13118624576976794563), (Int.ofNat 777508355815349027), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(4443094337297649750119675219993429/11258999068426240000000000000000000), (8951030197113938504527451490129/43980465111040000000000000000000), (-243705148079063870491746629924587/11258999068426240000000000000000000), (-41297496939896738422036384957569/5629499534213120000000000000000000), (6224123636581247737881152091361/11258999068426240000000000000000000), (439441065485812897335685701879/2251799813685248000000000000000000), (-69461873250796820403063478219/5629499534213120000000000000000000), (-29835302562671645351214666309/11258999068426240000000000000000000), (53515174991804213342579039/351843720888320000000000000000000), (235634758928325993684228159/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial127.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial127.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial127.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.ofNat 7548171466487740977496625564250914), (Int.ofNat 662630863234883472050214716707864), (Int.negOfNat 463533369358528516291434032851324), (Int.ofNat 20245903845026014132687060850414), (Int.ofNat 14160426628850611049270160229391), (Int.negOfNat 865667875890866265148455679630), (Int.negOfNat 263060838568076253569688367785), (Int.ofNat 14732988707061700582046510157), (Int.ofNat 2674234338866061621879254877), (Int.negOfNat 142605616688619778464543541), (Int.negOfNat 16891940657177043730835932), (Int.ofNat 891179850083616171765959), (Int.ofNat 73293665250316604805775), (Int.negOfNat 3908121103044521973351), (Int.negOfNat 233052465137622577800), (Int.ofNat 12574307724366219325), (Int.ofNat 469423138038368050), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(3774085733243870488748312782125457/5629499534213120000000000000000000), (82828857904360434006276839588483/1407374883553280000000000000000000), (-115883342339632129072858508212831/2814749767106560000000000000000000), (10122951922513007066343530425207/5629499534213120000000000000000000), (14160426628850611049270160229391/11258999068426240000000000000000000), (-86566787589086626514845567963/1125899906842624000000000000000000), (-52612167713615250713937673557/2251799813685248000000000000000000), (14732988707061700582046510157/11258999068426240000000000000000000), (2674234338866061621879254877/11258999068426240000000000000000000), (-142605616688619778464543541/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial127.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial127.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial127.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.ofNat 7365778711725286251581466800869009), (Int.negOfNat 606243874168299565599445683557286), (Int.negOfNat 120725314347014818955701844382759), (Int.ofNat 68874067818412226761893887313948), (Int.negOfNat 3916236371618806756280754994366), (Int.negOfNat 1978182441785742387096090345295), (Int.ofNat 106635322239694953694396310209), (Int.ofNat 26824071303872176264481638075), (Int.negOfNat 1370279169873681966273333512), (Int.negOfNat 210363879850283578633786616), (Int.ofNat 10809068415668903310118789), (Int.ofNat 1080338573322859575890696), (Int.negOfNat 57521435139703276256849), (Int.negOfNat 3937572715102669073455), (Int.ofNat 220118356956521974757), (Int.ofNat 10337755648749912761), (Int.negOfNat 824918967523683012), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(7365778711725286251581466800869009/11258999068426240000000000000000000), (-303121937084149782799722841778643/5629499534213120000000000000000000), (-120725314347014818955701844382759/11258999068426240000000000000000000), (17218516954603056690473471828487/2814749767106560000000000000000000), (-1958118185809403378140377497183/5629499534213120000000000000000000), (-395636488357148477419218069059/2251799813685248000000000000000000), (106635322239694953694396310209/11258999068426240000000000000000000), (1072962852154887050579265523/450359962737049600000000000000000), (-171284896234210245784166689/1407374883553280000000000000000000), (-26295484981285447329223327/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial127.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial127.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial127.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.ofNat 6105233289516835292219456455049433), (Int.negOfNat 515561239769779819653808957965671), (Int.ofNat 80618696953689776654483246068536), (Int.negOfNat 12882235984997651981615796819276), (Int.negOfNat 11989673315311599254518281639056), (Int.ofNat 628917111880975037996595882657), (Int.ofNat 235551839928744766639322147315), (Int.negOfNat 11091558585494410867312855291), (Int.negOfNat 2353917862450790743447209558), (Int.ofNat 113755499269164969598587104), (Int.ofNat 14583069699991739661461615), (Int.negOfNat 752294222550686814240922), (Int.negOfNat 61718600888935037536267), (Int.ofNat 3453835898245739288913), (Int.ofNat 189688351486648427567), (Int.negOfNat 11825254955453076211), (Int.negOfNat 361631140511112628), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(6105233289516835292219456455049433/11258999068426240000000000000000000), (-515561239769779819653808957965671/11258999068426240000000000000000000), (10077337119211222081810405758567/1407374883553280000000000000000000), (-3220558996249412995403949204819/2814749767106560000000000000000000), (-749354582206974953407392602441/703687441776640000000000000000000), (628917111880975037996595882657/11258999068426240000000000000000000), (47110367985748953327864429463/2251799813685248000000000000000000), (-11091558585494410867312855291/11258999068426240000000000000000000), (-1176958931225395371723604779/5629499534213120000000000000000000), (3554859352161405299955847/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial127.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial127.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial127.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.ofNat 5134942693107698371613173989032042), (Int.negOfNat 642855967820201699244057016799633), (Int.negOfNat 188585377922270408937067641670344), (Int.negOfNat 55586190980394885490367637367235), (Int.ofNat 3307068303771373746843855724696), (Int.ofNat 1789015025631453138029798891910), (Int.negOfNat 71825734195778170852733677029), (Int.negOfNat 23468425623348500114748436425), (Int.ofNat 1004877697884157172669396085), (Int.ofNat 178784226084890599648309349), (Int.negOfNat 8583764150132157154414618), (Int.negOfNat 893673056219176163680519), (Int.ofNat 48358572231727364586615), (Int.ofNat 3145271636532329031097), (Int.negOfNat 193042300531950765224), (Int.negOfNat 8160285570896219919), (Int.ofNat 818433580468389286), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(2567471346553849185806586994516021/5629499534213120000000000000000000), (-642855967820201699244057016799633/11258999068426240000000000000000000), (-23573172240283801117133455208793/1407374883553280000000000000000000), (-11117238196078977098073527473447/2251799813685248000000000000000000), (413383537971421718355481965587/1407374883553280000000000000000000), (178901502563145313802979889191/1125899906842624000000000000000000), (-71825734195778170852733677029/11258999068426240000000000000000000), (-938737024933940004589937457/450359962737049600000000000000000), (200975539576831434533879217/2251799813685248000000000000000000), (178784226084890599648309349/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial127.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial127.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial127.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.ofNat 2753098872789188464528172634035985), (Int.negOfNat 1838200548669069111110483632709087), (Int.negOfNat 330116420147481909405172864616579), (Int.ofNat 20395021806696834742152027424209), (Int.ofNat 12016784810450840015308563942650), (Int.negOfNat 323549994784952190564278354552), (Int.negOfNat 206361762932823860912875364410), (Int.ofNat 6871846042501557776692901125), (Int.ofNat 1968987450640211355512102752), (Int.negOfNat 82485773125457110115175283), (Int.negOfNat 11839253645742078184853218), (Int.ofNat 595296729815602394165039), (Int.ofNat 48457643285250000848002), (Int.negOfNat 2875397948320867790406), (Int.negOfNat 141338832101316231107), (Int.ofNat 9662350452391050569), (Int.ofNat 257081836511504069), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(550619774557837692905634526807197/2251799813685248000000000000000000), (-1838200548669069111110483632709087/11258999068426240000000000000000000), (-330116420147481909405172864616579/11258999068426240000000000000000000), (20395021806696834742152027424209/11258999068426240000000000000000000), (240335696209016800306171278853/225179981368524800000000000000000), (-40443749348119023820534794319/1407374883553280000000000000000000), (-20636176293282386091287536441/1125899906842624000000000000000000), (54974768340012462213543209/90071992547409920000000000000000), (61530857832506604859753211/351843720888320000000000000000000), (-82485773125457110115175283/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial127.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial127.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial127.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 1910569233295412256800350950167867), (Int.negOfNat 2590042416222419744842632946710301), (Int.ofNat 12895082189054047093315177170841), (Int.ofNat 77350458595628380231532336516875), (Int.ofNat 67377037892606072913828395003), (Int.negOfNat 1580858793078248139052287700804), (Int.ofNat 26113456309123136299710717165), (Int.ofNat 19142826706590534247850219366), (Int.negOfNat 614052575541123170920484990), (Int.negOfNat 141528041768362631472607052), (Int.ofNat 6247910789525562141741183), (Int.ofNat 687496823411732691818937), (Int.negOfNat 38041549747634442854980), (Int.negOfNat 2315604711701879601424), (Int.ofNat 157789445509525965336), (Int.ofNat 5640612524123695044), (Int.negOfNat 732725542031477425), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-1910569233295412256800350950167867/11258999068426240000000000000000000), (-2590042416222419744842632946710301/11258999068426240000000000000000000), (12895082189054047093315177170841/11258999068426240000000000000000000), (123760733753005408370451738427/18014398509481984000000000000000), (67377037892606072913828395003/11258999068426240000000000000000000), (-395214698269562034763071925201/2814749767106560000000000000000000), (5222691261824627259942143433/2251799813685248000000000000000000), (9571413353295267123925109683/5629499534213120000000000000000000), (-61405257554112317092048499/1125899906842624000000000000000000), (-35382010442090657868151763/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial127.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial127.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial127.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 6465879999977940700032564813020789), (Int.negOfNat 1721895628714586026481660015150375), (Int.ofNat 369613302573815018403504630115478), (Int.ofNat 27812192822248735653283049654389), (Int.negOfNat 9965274512427255900087059920364), (Int.negOfNat 153649526098286901112896496885), (Int.ofNat 158762753295058261858800983406), (Int.negOfNat 2576794055718633974141911284), (Int.negOfNat 1492767211001653078773416692), (Int.ofNat 52413036075647417632944010), (Int.ofNat 8841130525675821997678637), (Int.negOfNat 436298255252926066701231), (Int.negOfNat 35021903546065693063883), (Int.ofNat 2233709571985957461547), (Int.ofNat 95974225606240985230), (Int.negOfNat 7646297043783837095), (Int.negOfNat 181101878657532797), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-6465879999977940700032564813020789/11258999068426240000000000000000000), (-13775165029716688211853280121203/90071992547409920000000000000000), (184806651286907509201752315057739/5629499534213120000000000000000000), (27812192822248735653283049654389/11258999068426240000000000000000000), (-2491318628106813975021764980091/2814749767106560000000000000000000), (-30729905219657380222579299377/2251799813685248000000000000000000), (79381376647529130929400491703/5629499534213120000000000000000000), (-644198513929658493535477821/2814749767106560000000000000000000), (-373191802750413269693354173/2814749767106560000000000000000000), (5241303607564741763294401/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial127.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial127.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial127.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 8363597972005426012303069009889970), (Int.negOfNat 212917020832867934075120604676198), (Int.ofNat 319053426830052286043185031759817), (Int.negOfNat 36376079109726250868544782981932), (Int.negOfNat 4061226619563852190423294116035), (Int.ofNat 1027610333191063207051019901985), (Int.ofNat 12447089142020405045196412739), (Int.negOfNat 13343710523356555621959105598), (Int.ofNat 292302472926941497783633381), (Int.ofNat 100621173465760374271632288), (Int.negOfNat 4162677913456383311525139), (Int.negOfNat 483295304309791549253545), (Int.ofNat 27839273767484272856504), (Int.ofNat 1551696651058779972172), (Int.negOfNat 119773222291380631969), (Int.negOfNat 2975879956514546761), (Int.ofNat 647017503594565564), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-836359797200542601230306900988997/1125899906842624000000000000000000), (-106458510416433967037560302338099/5629499534213120000000000000000000), (319053426830052286043185031759817/11258999068426240000000000000000000), (-9094019777431562717136195745483/2814749767106560000000000000000000), (-812245323912770438084658823207/2251799813685248000000000000000000), (205522066638212641410203980397/2251799813685248000000000000000000), (12447089142020405045196412739/11258999068426240000000000000000000), (-6671855261678277810979552799/5629499534213120000000000000000000), (292302472926941497783633381/11258999068426240000000000000000000), (3144411670805011695988509/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial127.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial127.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial127.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 7837113195923142881046659436793781), (Int.ofNat 575950315413490886000140321851884), (Int.ofNat 80484655216811333475567847694382), (Int.negOfNat 32258533594752497155420897331840), (Int.ofNat 3886152155822239783358573081473), (Int.ofNat 345253343404219269214327923600), (Int.negOfNat 93251655531488266717430376685), (Int.ofNat 94638951040489779776754354), (Int.ofNat 976100579519537657646246559), (Int.negOfNat 30406011100035627363120402), (Int.negOfNat 5943867568568001459480764), (Int.ofNat 298970079325764222810088), (Int.ofNat 23074214196444043296715), (Int.negOfNat 1607935359147930970477), (Int.negOfNat 58256581221334680435), (Int.ofNat 5846642413621478015), (Int.ofNat 105121920803561525), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-7837113195923142881046659436793781/11258999068426240000000000000000000), (143987578853372721500035080462971/2814749767106560000000000000000000), (40242327608405666737783923847191/5629499534213120000000000000000000), (-50403958741800776805345152081/17592186044416000000000000000000), (3886152155822239783358573081473/11258999068426240000000000000000000), (863133358510548173035819809/28147497671065600000000000000000), (-18650331106297653343486075337/2251799813685248000000000000000000), (47319475520244889888377177/5629499534213120000000000000000000), (976100579519537657646246559/11258999068426240000000000000000000), (-15203005550017813681560201/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial127.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial127.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial127.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 6553842743441390581435357057301645), (Int.ofNat 645804632831538218385246579464478), (Int.negOfNat 12945133923596117636348671491169), (Int.negOfNat 717313301419033431653499175563), (Int.ofNat 2675756341763974725257527834403), (Int.negOfNat 427145387048822283895471866134), (Int.negOfNat 17605695398810315962703670647), (Int.ofNat 7598740845421210906751344055), (Int.negOfNat 136204156280319995662460629), (Int.negOfNat 63118493379668120718566377), (Int.ofNat 2681561597747034884020583), (Int.ofNat 309182776424481983323727), (Int.negOfNat 19104008518095671877368), (Int.negOfNat 950606028505282718935), (Int.ofNat 82407785256453143524), (Int.ofNat 1708999832428836692), (Int.negOfNat 535982812539663279), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1310768548688278116287071411460329/2251799813685248000000000000000000), (322902316415769109192623289732239/5629499534213120000000000000000000), (-12945133923596117636348671491169/11258999068426240000000000000000000), (-717313301419033431653499175563/11258999068426240000000000000000000), (2675756341763974725257527834403/11258999068426240000000000000000000), (-213572693524411141947735933067/5629499534213120000000000000000000), (-17605695398810315962703670647/11258999068426240000000000000000000), (1519748169084242181350268811/2251799813685248000000000000000000), (-136204156280319995662460629/11258999068426240000000000000000000), (-63118493379668120718566377/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial127.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial127.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial127.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 5290827086919503695923475101448118), (Int.ofNat 636624655759600297191723748367953), (Int.ofNat 13181753797014476311358465301340), (Int.ofNat 4509785168341942340072401532670), (Int.negOfNat 885014811055423068000381836037), (Int.negOfNat 159781390714420008881480548271), (Int.ofNat 43414952468167520256207686255), (Int.negOfNat 13469014393779491300137447), (Int.negOfNat 555407171598773716499682241), (Int.ofNat 19551605266319695067705863), (Int.ofNat 3636701241375059987659655), (Int.negOfNat 200001054185044916804649), (Int.negOfNat 14193386754915859763664), (Int.ofNat 1076056913037449416571), (Int.ofNat 32602364618492551324), (Int.negOfNat 3316119445689704232), (Int.negOfNat 111607307858855251), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-2645413543459751847961737550724059/5629499534213120000000000000000000), (636624655759600297191723748367953/11258999068426240000000000000000000), (659087689850723815567923265067/562949953421312000000000000000000), (450978516834194234007240153267/1125899906842624000000000000000000), (-885014811055423068000381836037/11258999068426240000000000000000000), (-159781390714420008881480548271/11258999068426240000000000000000000), (8682990493633504051241537251/2251799813685248000000000000000000), (-13469014393779491300137447/11258999068426240000000000000000000), (-555407171598773716499682241/11258999068426240000000000000000000), (19551605266319695067705863/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial127.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial127.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial127.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.negOfNat 3945397795761861231259427210166291), (Int.ofNat 710188132889106215409394424055900), (Int.ofNat 15758424073614733330991248217804), (Int.negOfNat 2866773850606759565217363632710), (Int.negOfNat 385879122321629795093991832853), (Int.ofNat 173010773974379106780860063523), (Int.ofNat 2834599415259948695854504727), (Int.negOfNat 3882624108804058076944852220), (Int.ofNat 122254315894364666150285695), (Int.ofNat 36521957056048383014853278), (Int.negOfNat 1879033422955518792153686), (Int.negOfNat 189267724156503254039028), (Int.ofNat 12753036983760033202615), (Int.ofNat 582451568462847476489), (Int.negOfNat 52518923676834157203), (Int.negOfNat 537355939575820003), (Int.ofNat 428190815012407857), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-3945397795761861231259427210166291/11258999068426240000000000000000000), (7101881328891062154093944240559/112589990684262400000000000000000), (3939606018403683332747812054451/2814749767106560000000000000000000), (-286677385060675956521736363271/1125899906842624000000000000000000), (-385879122321629795093991832853/11258999068426240000000000000000000), (173010773974379106780860063523/11258999068426240000000000000000000), (2834599415259948695854504727/11258999068426240000000000000000000), (-194131205440202903847242611/562949953421312000000000000000000), (24450863178872933230057139/2251799813685248000000000000000000), (18260978528024191507426639/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial127.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial127.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial127.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.negOfNat 2485827566491563827272414389337282), (Int.ofNat 739316021123190701088262565305322), (Int.ofNat 1570055785401956210019664320908), (Int.negOfNat 373977739712192033667358835575), (Int.ofNat 679875858329651202987407380695), (Int.negOfNat 10036093699570920037348562949), (Int.negOfNat 21558358545653065372088369425), (Int.ofNat 892652225456636253814757640), (Int.ofNat 306121319129654908437266279), (Int.negOfNat 17066757837238864431453686), (Int.negOfNat 2207397519763100011529881), (Int.ofNat 143751365458785141813383), (Int.ofNat 9242753601400337571344), (Int.negOfNat 699875090921569927652), (Int.negOfNat 22776866289047609089), (Int.ofNat 2270372461699018553), (Int.ofNat 171988693677776688), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-1242913783245781913636207194668641/5629499534213120000000000000000000), (369658010561595350544131282652661/5629499534213120000000000000000000), (392513946350489052504916080227/2814749767106560000000000000000000), (-14959109588487681346694353423/450359962737049600000000000000000), (135975171665930240597481476139/2251799813685248000000000000000000), (-10036093699570920037348562949/11258999068426240000000000000000000), (-862334341826122614883534777/450359962737049600000000000000000), (22316305636415906345368941/281474976710656000000000000000000), (306121319129654908437266279/11258999068426240000000000000000000), (-8533378918619432215726843/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial127.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial127.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial127.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.negOfNat 994548045012965233763029720025492), (Int.ofNat 758587006329186970530419820997657), (Int.ofNat 10715229697035374123306821595178), (Int.ofNat 2143941730010449893962170849111), (Int.negOfNat 212698412020150847018676730347), (Int.negOfNat 103877650650519228830555962598), (Int.ofNat 8845134690281627384199167957), (Int.ofNat 2124056285538228006538543002), (Int.negOfNat 166774192171587002083012400), (Int.negOfNat 22060092045824240083995984), (Int.ofNat 1645547057109170431324441), (Int.ofNat 129460096868562920043479), (Int.negOfNat 9320366609040498175375), (Int.negOfNat 462133232921036281043), (Int.ofNat 33344163950973774402), (Int.ofNat 928842785463801323), (Int.negOfNat 352210857158436585), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-248637011253241308440757430006373/2814749767106560000000000000000000), (758587006329186970530419820997657/11258999068426240000000000000000000), (5357614848517687061653410797589/5629499534213120000000000000000000), (2143941730010449893962170849111/11258999068426240000000000000000000), (-212698412020150847018676730347/11258999068426240000000000000000000), (-51938825325259614415277981299/5629499534213120000000000000000000), (8845134690281627384199167957/11258999068426240000000000000000000), (1062028142769114003269271501/5629499534213120000000000000000000), (-416935480428967505207531/28147497671065600000000000000000), (-1378755752864015005249749/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial127.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial127.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial127.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 576697048505638680140823971351661), (Int.ofNat 814496538257343357202566869115214), (Int.ofNat 13335503609835883130939107144959), (Int.negOfNat 1495928003049905722036054318801), (Int.negOfNat 375494124252439317560999527159), (Int.ofNat 77533352295142433624630677464), (Int.ofNat 11896404003079768444763106932), (Int.negOfNat 1729012786924746936645881698), (Int.negOfNat 182725628364264931182017044), (Int.ofNat 19954751754645520161319190), (Int.ofNat 1558129928122996101827499), (Int.negOfNat 131881962693232001639197), (Int.negOfNat 8027232242596183508276), (Int.ofNat 529177620036000530724), (Int.ofNat 26315950716362803520), (Int.negOfNat 969546880010386140), (Int.negOfNat 257696732114688549), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(576697048505638680140823971351661/11258999068426240000000000000000000), (407248269128671678601283434557607/5629499534213120000000000000000000), (13335503609835883130939107144959/11258999068426240000000000000000000), (-1495928003049905722036054318801/11258999068426240000000000000000000), (-375494124252439317560999527159/11258999068426240000000000000000000), (9691669036892804203078834683/1407374883553280000000000000000000), (2974101000769942111190776733/2814749767106560000000000000000000), (-864506393462373468322940849/5629499534213120000000000000000000), (-45681407091066232795504261/2814749767106560000000000000000000), (1995475175464552016131919/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial127.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial127.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial127.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 2244042669279174450362307541210396), (Int.ofNat 845448975062367034738737354158502), (Int.ofNat 3022278717239375361693289913901), (Int.negOfNat 665907226118560503722372040283), (Int.ofNat 519874773863222288684016454704), (Int.ofNat 41469044829094599065004497941), (Int.negOfNat 16421955868754383602706194162), (Int.negOfNat 1115914439342411512378133061), (Int.ofNat 244867399939774785219285532), (Int.ofNat 15225009822638506207990451), (Int.negOfNat 1979426129705782868562798), (Int.negOfNat 117404136465615498733415), (Int.ofNat 9380319515176410823848), (Int.ofNat 555179968286095416974), (Int.negOfNat 26491606780648965683), (Int.negOfNat 1218208237489477397), (Int.ofNat 276230899304465313), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(561010667319793612590576885302599/2814749767106560000000000000000000), (422724487531183517369368677079251/5629499534213120000000000000000000), (3022278717239375361693289913901/11258999068426240000000000000000000), (-665907226118560503722372040283/11258999068426240000000000000000000), (32492173366451393042751028419/703687441776640000000000000000000), (41469044829094599065004497941/11258999068426240000000000000000000), (-8210977934377191801353097081/5629499534213120000000000000000000), (-1115914439342411512378133061/11258999068426240000000000000000000), (61216849984943696304821383/2814749767106560000000000000000000), (15225009822638506207990451/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial127.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial127.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial127.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 3950221896410259324828956658597577), (Int.ofNat 866122396496653582593451667514430), (Int.ofNat 10613750936406054482224829820794), (Int.ofNat 2385912755592998145183958087264), (Int.negOfNat 57772168179148184635631416637), (Int.negOfNat 127269024199611340558529470087), (Int.negOfNat 2122924910990643346935439315), (Int.ofNat 2758626840786185198494323953), (Int.ofNat 98413344967699802681504923), (Int.negOfNat 29518943185351283120441809), (Int.negOfNat 1381024027818269972287438), (Int.ofNat 173631951730185368349601), (Int.ofNat 9635075471167276301355), (Int.negOfNat 611004216411113136249), (Int.negOfNat 41396880020265815120), (Int.ofNat 956554664983868615), (Int.ofNat 343404770551600410), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(3950221896410259324828956658597577/11258999068426240000000000000000000), (86612239649665358259345166751443/1125899906842624000000000000000000), (5306875468203027241112414910397/5629499534213120000000000000000000), (74559773612281192036998690227/351843720888320000000000000000000), (-57772168179148184635631416637/11258999068426240000000000000000000), (-127269024199611340558529470087/11258999068426240000000000000000000), (-424584982198128669387087863/2251799813685248000000000000000000), (2758626840786185198494323953/11258999068426240000000000000000000), (98413344967699802681504923/11258999068426240000000000000000000), (-29518943185351283120441809/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial127.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial127.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial127.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 5739238324145447638981179139388830), (Int.ofNat 926034233675573059184555237710173), (Int.ofNat 14735321723071566375736689847904), (Int.negOfNat 1957199521096885682959986155490), (Int.negOfNat 704487220954117901675413260885), (Int.ofNat 58294965711621698016744365452), (Int.ofNat 26018186989720382394819076424), (Int.negOfNat 164778336815875253865970065), (Int.negOfNat 407688310537633280914210708), (Int.negOfNat 11048545269492115892038564), (Int.ofNat 3100847122900178713981901), (Int.ofNat 136480126371114834563124), (Int.negOfNat 13697728152084200270301), (Int.negOfNat 805282519271074832205), (Int.ofNat 37043922642891720763), (Int.ofNat 2667490888689582599), (Int.negOfNat 228820287596131328), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(573923832414544763898117913938883/1125899906842624000000000000000000), (926034233675573059184555237710173/11258999068426240000000000000000000), (460478803845986449241771557747/351843720888320000000000000000000), (-195719952109688568295998615549/1125899906842624000000000000000000), (-140897444190823580335082652177/2251799813685248000000000000000000), (14573741427905424504186091363/2814749767106560000000000000000000), (3252273373715047799352384553/1407374883553280000000000000000000), (-32955667363175050773194013/2251799813685248000000000000000000), (-101922077634408320228552677/2814749767106560000000000000000000), (-2762136317373028973009641/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial127.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial127.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial127.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 7626721565632364326060751047231264), (Int.ofNat 948104914056216763316927729210894), (Int.negOfNat 3861300022520665433717783740087), (Int.negOfNat 1928991262367091968146462204360), (Int.ofNat 937712294149156940327343290639), (Int.ofNat 179186585661673087554177589506), (Int.negOfNat 17889395327088764280842612365), (Int.negOfNat 4996271808033058012511690019), (Int.negOfNat 609944537309220051110422), (Int.ofNat 50877667201380988608027286), (Int.ofNat 1479743596166170926653485), (Int.negOfNat 283453174219684137976588), (Int.negOfNat 13225473354252362278503), (Int.ofNat 980488218597190410887), (Int.ofNat 63118896794238046653), (Int.negOfNat 1705607433897011729), (Int.negOfNat 451196768078855832), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(238335048926011385189398470225977/351843720888320000000000000000000), (474052457028108381658463864605447/5629499534213120000000000000000000), (-3861300022520665433717783740087/11258999068426240000000000000000000), (-48224781559177299203661555109/281474976710656000000000000000000), (937712294149156940327343290639/11258999068426240000000000000000000), (89593292830836543777088794753/5629499534213120000000000000000000), (-3577879065417752856168522473/2251799813685248000000000000000000), (-4996271808033058012511690019/11258999068426240000000000000000000), (-304972268654610025555211/5629499534213120000000000000000000), (25438833600690494304013643/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial127.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial127.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial127.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 9511033969691283818906904889948598), (Int.ofNat 948301160269531604357915773156630), (Int.ofNat 13995524902929134689541882322736), (Int.ofNat 7361976115812526110238209597755), (Int.ofNat 468369428218891626689029371694), (Int.negOfNat 350286109689963275728331184444), (Int.negOfNat 53459182472762566785814351871), (Int.ofNat 2040122564048640736663746925), (Int.ofNat 752886157401806477069344635), (Int.ofNat 9179811332287229189337791), (Int.negOfNat 5282213541599437496542662), (Int.negOfNat 180791180807278075224791), (Int.ofNat 22743017821668029196205), (Int.ofNat 1162771652540550696043), (Int.negOfNat 63371695811703805096), (Int.negOfNat 4844960966543275441), (Int.ofNat 235305674651425054), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(4755516984845641909453452444974299/5629499534213120000000000000000000), (94830116026953160435791577315663/1125899906842624000000000000000000), (874720306433070918096367645171/703687441776640000000000000000000), (1472395223162505222047641919551/2251799813685248000000000000000000), (234184714109445813344514685847/5629499534213120000000000000000000), (-87571527422490818932082796111/2814749767106560000000000000000000), (-53459182472762566785814351871/11258999068426240000000000000000000), (81604902561945629466549877/450359962737049600000000000000000), (150577231480361295413868927/2251799813685248000000000000000000), (9179811332287229189337791/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial127.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial127.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial127.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 11515830463272455192194229629240350), (Int.ofNat 1071005354803442725571679388911341), (Int.ofNat 31253343145595737609583855889740), (Int.negOfNat 9000915812066247625486959058235), (Int.negOfNat 4865962492929656153755247160093), (Int.negOfNat 509958005691496508284072788271), (Int.ofNat 46713886683099449416215549650), (Int.ofNat 10051867335325993687083735945), (Int.negOfNat 58928715287897490154351242), (Int.negOfNat 88258668240339070446026857), (Int.negOfNat 1978210495181644531456842), (Int.ofNat 465571380189298138888841), (Int.ofNat 18470617207753612588778), (Int.negOfNat 1629416243513488772214), (Int.negOfNat 90888477214666040673), (Int.ofNat 3868511936959037371), (Int.ofNat 555746072078464391), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(230316609265449103843884592584807/225179981368524800000000000000000), (1071005354803442725571679388911341/11258999068426240000000000000000000), (1562667157279786880479192794487/562949953421312000000000000000000), (-1800183162413249525097391811647/2251799813685248000000000000000000), (-4865962492929656153755247160093/11258999068426240000000000000000000), (-509958005691496508284072788271/11258999068426240000000000000000000), (934277733661988988324310993/225179981368524800000000000000000), (2010373467065198737416747189/2251799813685248000000000000000000), (-29464357643948745077175621/5629499534213120000000000000000000), (-88258668240339070446026857/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial127.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial127.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial127.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 13620888205255182065690307724865475), (Int.ofNat 904704382946315365554304736276744), (Int.negOfNat 162886720735807110507444928638764), (Int.negOfNat 55812922243352023353081875867071), (Int.negOfNat 4775302521687984219574683920615), (Int.ofNat 689707145801170963987313494648), (Int.ofNat 122443533813468326572628266039), (Int.negOfNat 2783644907052465682587016646), (Int.negOfNat 1323214989776070577331078220), (Int.negOfNat 15690004644254664470420748), (Int.ofNat 8469800988512356096595817), (Int.ofNat 256707383236378832157223), (Int.negOfNat 35868490515108670651110), (Int.negOfNat 1589893134724056185986), (Int.ofNat 106086632660548594924), (Int.ofNat 6033047736289023716), (Int.negOfNat 321013713088336915), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(544835528210207282627612308994619/450359962737049600000000000000000), (113088047868289420694288092034593/1407374883553280000000000000000000), (-40721680183951777626861232159691/2814749767106560000000000000000000), (-55812922243352023353081875867071/11258999068426240000000000000000000), (-955060504337596843914936784123/2251799813685248000000000000000000), (86213393225146370498414186831/1407374883553280000000000000000000), (122443533813468326572628266039/11258999068426240000000000000000000), (-1391822453526232841293508323/5629499534213120000000000000000000), (-66160749488803528866553911/562949953421312000000000000000000), (-3922501161063666117605187/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial127.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial127.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial127.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 14285054842668304428260473034203458), (Int.negOfNat 493314407957775955263701130726393), (Int.negOfNat 532020437821741692621592552490166), (Int.negOfNat 50713959851346133941195305547155), (Int.ofNat 7263372002108165087803945661280), (Int.ofNat 1372628456052291701771181455998), (Int.negOfNat 45392472007246185144265871876), (Int.negOfNat 17756352778517051218595011186), (Int.negOfNat 67145787144616584279869988), (Int.ofNat 137246341116871956063544010), (Int.ofNat 3159093765839532404635803), (Int.negOfNat 697618128504360258951159), (Int.negOfNat 25202616857060190807927), (Int.ofNat 2480150980770237281893), (Int.ofNat 117517141575011836710), (Int.negOfNat 6550358484079639145), (Int.negOfNat 631726029932435663), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(7142527421334152214130236517101729/5629499534213120000000000000000000), (-493314407957775955263701130726393/11258999068426240000000000000000000), (-266010218910870846310796276245083/5629499534213120000000000000000000), (-10142791970269226788239061109431/2251799813685248000000000000000000), (45396075013176031798774660383/70368744177664000000000000000000), (686314228026145850885590727999/5629499534213120000000000000000000), (-11348118001811546286066467969/2814749767106560000000000000000000), (-8878176389258525609297505593/5629499534213120000000000000000000), (-16786446786154146069967497/2814749767106560000000000000000000), (13724634111687195606354401/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial127.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial127.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial127.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 10919647533704529578177204453508300), (Int.negOfNat 2904140398226464567623099110548130), (Int.negOfNat 574471870275944904489829446237392), (Int.ofNat 45726330773128229724071273338929), (Int.ofNat 13783309133286673749977550361150), (Int.negOfNat 413799251235207531124444287742), (Int.negOfNat 209845242843881132499395351739), (Int.negOfNat 44888573528411054630011722), (Int.ofNat 1969946970767645815031120509), (Int.ofNat 36013446101356747355967872), (Int.negOfNat 12050066732909128356120531), (Int.negOfNat 365752832306121982143275), (Int.ofNat 51055306161890799186916), (Int.ofNat 2041477343799413585808), (Int.negOfNat 156517406317854377751), (Int.negOfNat 8031987165384783699), (Int.ofNat 406721751525248776), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(109196475337045295781772044535083/112589990684262400000000000000000), (-290414039822646456762309911054813/1125899906842624000000000000000000), (-35904491892246556530614340389837/703687441776640000000000000000000), (45726330773128229724071273338929/11258999068426240000000000000000000), (275666182665733474999551007223/225179981368524800000000000000000), (-206899625617603765562222143871/5629499534213120000000000000000000), (-209845242843881132499395351739/11258999068426240000000000000000000), (-22444286764205527315005861/5629499534213120000000000000000000), (1969946970767645815031120509/11258999068426240000000000000000000), (281355047666849588718499/87960930222080000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial127.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial127.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial127.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 3373655311181765631913195248219537), (Int.negOfNat 4283624626297455166452028278064130), (Int.negOfNat 49260738974425712885384822140399), (Int.ofNat 109369891553859470101134503578236), (Int.negOfNat 776784405989654977656821976401), (Int.negOfNat 2082892213719964357619363578199), (Int.negOfNat 8203477967267316660924388315), (Int.ofNat 24599917768680605065892174246), (Int.ofNat 419700860057642802211974131), (Int.negOfNat 184133607174362843662995938), (Int.negOfNat 4975235272164259987336656), (Int.ofNat 934613411497911820794252), (Int.ofNat 32624340380371348121015), (Int.negOfNat 3399992434460474813983), (Int.negOfNat 142618271990481674945), (Int.ofNat 9015806252755386525), (Int.ofNat 707705987786406935), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(3373655311181765631913195248219537/11258999068426240000000000000000000), (-428362462629745516645202827806413/1125899906842624000000000000000000), (-49260738974425712885384822140399/11258999068426240000000000000000000), (27342472888464867525283625894559/2814749767106560000000000000000000), (-776784405989654977656821976401/11258999068426240000000000000000000), (-2082892213719964357619363578199/11258999068426240000000000000000000), (-1640695593453463332184877663/2251799813685248000000000000000000), (12299958884340302532946087123/5629499534213120000000000000000000), (419700860057642802211974131/11258999068426240000000000000000000), (-92066803587181421831497969/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial127.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial127.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial127.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 4592125009094089310495522582689258), (Int.negOfNat 3350280475229429045818201289905616), (Int.ofNat 436120955204906347810403715074524), (Int.ofNat 32031177207451491899621038187234), (Int.negOfNat 15506916997088833576070325806944), (Int.negOfNat 308541064972318049352639470216), (Int.ofNat 257664233237584030441350756513), (Int.ofNat 5366601656707230305630327895), (Int.negOfNat 2456800204041033226195280041), (Int.negOfNat 65161468863182229726602203), (Int.ofNat 15196714207754193997044277), (Int.ofNat 487594120391949655886463), (Int.negOfNat 65718227041291024305412), (Int.negOfNat 2444517166761382197015), (Int.ofNat 209884543710329476956), (Int.ofNat 8633074150957105468), (Int.negOfNat 517756442580151061), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-2296062504547044655247761291344629/5629499534213120000000000000000000), (-209392529701839315363637580619101/703687441776640000000000000000000), (109030238801226586952600928768631/2814749767106560000000000000000000), (16015588603725745949810519093617/5629499534213120000000000000000000), (-484591156159026049252197681467/351843720888320000000000000000000), (-38567633121539756169079933777/1407374883553280000000000000000000), (257664233237584030441350756513/11258999068426240000000000000000000), (1073320331341446061126065579/2251799813685248000000000000000000), (-2456800204041033226195280041/11258999068426240000000000000000000), (-65161468863182229726602203/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial127.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial127.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial127.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial127.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial127.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial127.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial127.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial127.reflect := by
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

end Bin127
end
end ErdosOverlap.OuterNumerics
