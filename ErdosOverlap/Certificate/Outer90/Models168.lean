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

/-! # Exact integer weighted outer models for source bin 168

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin168

def weightDenominator : ℤ := (Int.ofNat 50000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 2152507078216935500)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 8726741361199261000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 5963869201840722000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 2437508707478211000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 4301777423008655500)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 3501192196241558500)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 2466157170163250000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 1739896497023198000)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 933264310846960000)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 539388450487429950)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial168.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial168.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 44743756312051040000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 17280551995397750000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 5697961099363612000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 4600257480790798000)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 2307505487478327500)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 864467186294195000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 7758519533897424)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 188817319183244765)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 180845147813800615)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial168.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial168.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 44743756312051040000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 17280551995397750000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 5697961099363612000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 4600257480790798000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 2307505487478327500)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 864467186294195000)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 7758519533897424)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 188817319183244765)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 180845147813800615)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial168.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial168.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial168.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 20051998683609447619446636961524378), (Int.ofNat 19173202806462248157618054253321056), (Int.ofNat 1953728598899757864432984733132894), (Int.negOfNat 451598257547734389218113850663310), (Int.negOfNat 60634920765907306878057247928651), (Int.ofNat 7674549894514051911652772530026), (Int.ofNat 1035248945504942658318489847666), (Int.negOfNat 87192739722713643488358911088), (Int.negOfNat 10946668192091396767604167474), (Int.ofNat 688653817594046197935921935), (Int.ofNat 78214692846549700647306525), (Int.negOfNat 3947864410674971584339792), (Int.negOfNat 401892966029264095614559), (Int.ofNat 17019635447916895549081), (Int.ofNat 1556186125333891543957), (Int.negOfNat 56099989108117707437), (Int.negOfNat 4904094769350158205), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-10025999341804723809723318480762189/28147497671065600000000000000000000), (599162587701945254925564195416283/1759218604441600000000000000000000), (976864299449878932216492366566447/28147497671065600000000000000000000), (-45159825754773438921811385066331/5629499534213120000000000000000000), (-60634920765907306878057247928651/56294995342131200000000000000000000), (3837274947257025955826386265013/28147497671065600000000000000000000), (517624472752471329159244923833/28147497671065600000000000000000000), (-5449546232669602718022431943/3518437208883200000000000000000000), (-5473334096045698383802083737/28147497671065600000000000000000000), (137730763518809239587184387/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial168.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial168.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial168.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial168 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 21824678157620951877662800131055700), (Int.ofNat 20393014540633662530785273833050754), (Int.negOfNat 1422945999443602429996549621365093), (Int.negOfNat 527802589157310596816407825370327), (Int.ofNat 45169084644745947099065637770190), (Int.ofNat 9737804781172141261740192598753), (Int.negOfNat 763277449287246358702557159552), (Int.negOfNat 116683011132044417657958124006), (Int.ofNat 8073258029217732903729104841), (Int.ofNat 947463236649981749022227732), (Int.negOfNat 58288248681948377912223762), (Int.negOfNat 5496452154692432243408637), (Int.ofNat 303608257711303452559317), (Int.ofNat 23780523127070748635145), (Int.negOfNat 1191344873250165628520), (Int.negOfNat 78682799061637127699), (Int.ofNat 3796785553820522425), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(218246781576209518776628001310557/562949953421312000000000000000000), (10196507270316831265392636916525377/28147497671065600000000000000000000), (-1422945999443602429996549621365093/56294995342131200000000000000000000), (-527802589157310596816407825370327/56294995342131200000000000000000000), (4516908464474594709906563777019/5629499534213120000000000000000000), (9737804781172141261740192598753/56294995342131200000000000000000000), (-5963105072556612177363727809/439804651110400000000000000000000), (-58341505566022208828979062003/28147497671065600000000000000000000), (8073258029217732903729104841/56294995342131200000000000000000000), (236865809162495437255556933/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial168.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial168.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial168.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial168 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 53669514780890509574114760436420459), (Int.ofNat 10403309502483438426645965471041071), (Int.negOfNat 2970245949048079191093572701718237), (Int.ofNat 54068911686774716669422929514605), (Int.ofNat 75971667948432300987835466840556), (Int.negOfNat 4291359567751755301314052293697), (Int.negOfNat 1110953003944859804293475964381), (Int.ofNat 73623883115612352170935113530), (Int.ofNat 10484562689066257561035853050), (Int.negOfNat 716363162615396702761079168), (Int.negOfNat 69057130736677895248340410), (Int.ofNat 4642831775487980875670879), (Int.ofNat 334380825436119438530364), (Int.negOfNat 21631257692089953958064), (Int.negOfNat 1235313130386764086255), (Int.ofNat 76155922153181189053), (Int.ofNat 3466774565701668970), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(53669514780890509574114760436420459/56294995342131200000000000000000000), (10403309502483438426645965471041071/56294995342131200000000000000000000), (-2970245949048079191093572701718237/56294995342131200000000000000000000), (10813782337354943333884585902921/11258999068426240000000000000000000), (18992916987108075246958866710139/14073748835532800000000000000000000), (-4291359567751755301314052293697/56294995342131200000000000000000000), (-1110953003944859804293475964381/56294995342131200000000000000000000), (7362388311561235217093511353/5629499534213120000000000000000000), (209691253781325151220717061/1125899906842624000000000000000000), (-5596587207932786740320931/439804651110400000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial168.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial168.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial168.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial168 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 64046504567907182035905407393138417), (Int.ofNat 1087409138391469893813702203058563), (Int.negOfNat 1368133392849209057311489224061803), (Int.ofNat 367767892691434988625131684541817), (Int.negOfNat 4828681107477715108055088628264), (Int.negOfNat 8579327907201396749762802536467), (Int.ofNat 463553976871384608297360855100), (Int.ofNat 102137050087416431390011565485), (Int.negOfNat 7120447734439653129455364044), (Int.negOfNat 786110163265647204260357299), (Int.ofNat 60622745444164381535620171), (Int.ofNat 4291896322635586189267545), (Int.negOfNat 344566010519002924098186), (Int.negOfNat 17550364952671866272740), (Int.ofNat 1420104717910457296582), (Int.ofNat 54418295234938742000), (Int.negOfNat 4339320997261924270), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(64046504567907182035905407393138417/56294995342131200000000000000000000), (1087409138391469893813702203058563/56294995342131200000000000000000000), (-1368133392849209057311489224061803/56294995342131200000000000000000000), (367767892691434988625131684541817/56294995342131200000000000000000000), (-603585138434714388506886078533/7036874417766400000000000000000000), (-8579327907201396749762802536467/56294995342131200000000000000000000), (4635539768713846082973608551/562949953421312000000000000000000), (20427410017483286278002313097/11258999068426240000000000000000000), (-1780111933609913282363841011/14073748835532800000000000000000000), (-786110163265647204260357299/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial168.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial168.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial168.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial168 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 63379720035176720155946491115102803), (Int.negOfNat 686767018919939531619496106737895), (Int.ofNat 200539910011931772149204869210165), (Int.ofNat 101414386598892248003391944974021), (Int.negOfNat 44407296461287930455648843153257), (Int.ofNat 1364710652176818692831937026498), (Int.ofNat 811825398961212757616969074617), (Int.negOfNat 54103094888373047552360162981), (Int.negOfNat 7841694354252117877813241522), (Int.ofNat 665115395389314255436890139), (Int.ofNat 49530063015962763393840311), (Int.negOfNat 4786042133056033413391387), (Int.negOfNat 224571330572971921298711), (Int.ofNat 23561879238190169609567), (Int.ofNat 772644628369141842162), (Int.negOfNat 86516915594912772783), (Int.negOfNat 1848609214239379120), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(63379720035176720155946491115102803/56294995342131200000000000000000000), (-137353403783987906323899221347579/11258999068426240000000000000000000), (40107982002386354429840973842033/11258999068426240000000000000000000), (101414386598892248003391944974021/56294995342131200000000000000000000), (-44407296461287930455648843153257/56294995342131200000000000000000000), (682355326088409346415968513249/28147497671065600000000000000000000), (811825398961212757616969074617/56294995342131200000000000000000000), (-54103094888373047552360162981/56294995342131200000000000000000000), (-3920847177126058938906620761/28147497671065600000000000000000000), (665115395389314255436890139/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial168.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial168.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial168.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial168 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 62996219622281757659077218006473989), (Int.ofNat 145838932976794709991646083179068), (Int.ofNat 345927491699579719360503071490), (Int.negOfNat 109597250211610128323938028960062), (Int.negOfNat 2856253107828223132023086292013), (Int.ofNat 4633159389653001323950497816956), (Int.negOfNat 289006815170710182743122476944), (Int.negOfNat 64427617879768090556276220699), (Int.ofNat 5994259308899781775954091451), (Int.ofNat 497682652582289248230885105), (Int.negOfNat 57435770521777969174220221), (Int.negOfNat 2537481943616117265408999), (Int.ofNat 346283353085848428773044), (Int.ofNat 9317050835815545141490), (Int.negOfNat 1475940108032451068785), (Int.negOfNat 25458111550989484101), (Int.ofNat 4881856440703326115), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(62996219622281757659077218006473989/56294995342131200000000000000000000), (36459733244198677497911520794767/14073748835532800000000000000000000), (34592749169957971936050307149/5629499534213120000000000000000000), (-54798625105805064161969014480031/28147497671065600000000000000000000), (-2856253107828223132023086292013/56294995342131200000000000000000000), (1158289847413250330987624454239/14073748835532800000000000000000000), (-18062925948169386421445154809/3518437208883200000000000000000000), (-64427617879768090556276220699/56294995342131200000000000000000000), (5994259308899781775954091451/56294995342131200000000000000000000), (99536530516457849646177021/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial168.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial168.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial168.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial168 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 62490047878917829492319525883422182), (Int.negOfNat 966073626750129158243609651675081), (Int.negOfNat 455465644210009045572505961396182), (Int.negOfNat 16972989654757796523287686464875), (Int.ofNat 15982049152326064864742494702237), (Int.negOfNat 1059650279570459141886888432547), (Int.negOfNat 394328712399858774024054557440), (Int.ofNat 43747430367293370614175316041), (Int.ofNat 4101825457596005825364621601), (Int.negOfNat 589053638038432878427049041), (Int.negOfNat 24209323500226161901525982), (Int.ofNat 4475807024506946407776418), (Int.ofNat 92046315662034314637955), (Int.negOfNat 22746645625505083284751), (Int.negOfNat 234132363284162152877), (Int.ofNat 85728449731268156283), (Int.ofNat 230443862777089270), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(31245023939458914746159762941711091/28147497671065600000000000000000000), (-966073626750129158243609651675081/56294995342131200000000000000000000), (-227732822105004522786252980698091/28147497671065600000000000000000000), (-135783917238062372186301491719/450359962737049600000000000000000), (15982049152326064864742494702237/56294995342131200000000000000000000), (-1059650279570459141886888432547/56294995342131200000000000000000000), (-308069306562389667206292623/43980465111040000000000000000000), (43747430367293370614175316041/56294995342131200000000000000000000), (4101825457596005825364621601/56294995342131200000000000000000000), (-589053638038432878427049041/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial168.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial168.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial168.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial168 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 58803153779867067465925552967336515), (Int.negOfNat 2618300194877292787339071511317684), (Int.negOfNat 319261211491315581115912578548877), (Int.ofNat 33907968386661236872891421672433), (Int.negOfNat 3938901238681517646427477929140), (Int.negOfNat 1527756196033630166872630670688), (Int.ofNat 267001717456648165628686930274), (Int.ofNat 24811749370852936350979254930), (Int.negOfNat 5136115233259107761909375733), (Int.negOfNat 175795211667315390417988996), (Int.ofNat 50452733348992434169308203), (Int.ofNat 613561950809457396691687), (Int.negOfNat 311804104190487413736732), (Int.negOfNat 538960984272830194845), (Int.ofNat 1346415489748890837572), (Int.negOfNat 5622540883334404398), (Int.negOfNat 4885003433657298010), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(11760630755973413493185110593467303/11258999068426240000000000000000000), (-654575048719323196834767877829421/14073748835532800000000000000000000), (-319261211491315581115912578548877/56294995342131200000000000000000000), (33907968386661236872891421672433/56294995342131200000000000000000000), (-196945061934075882321373896457/2814749767106560000000000000000000), (-47742381126050942714769708459/1759218604441600000000000000000000), (133500858728324082814343465137/28147497671065600000000000000000000), (2481174937085293635097925493/5629499534213120000000000000000000), (-5136115233259107761909375733/56294995342131200000000000000000000), (-43948802916828847604497249/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial168.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial168.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial168.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial168 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 52467772494619653843112554120744830), (Int.negOfNat 3679741487308623039753768640426728), (Int.negOfNat 261249776841463248107735172733143), (Int.negOfNat 11481059593151144265950708282859), (Int.negOfNat 2044695078712391010814981085297), (Int.ofNat 1499604772537747953219226583928), (Int.ofNat 82012302674935692244178113364), (Int.negOfNat 38407583258115965207969368440), (Int.negOfNat 659017337783477069125177373), (Int.ofNat 492199904283045567954857326), (Int.negOfNat 517175936488040041324117), (Int.negOfNat 3763927617832801020898287), (Int.ofNat 37532450682961084294048), (Int.ofNat 19341371832943690005185), (Int.negOfNat 284012166343776543628), (Int.negOfNat 73071755497572062622), (Int.ofNat 1210023333825371860), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(5246777249461965384311255412074483/5629499534213120000000000000000000), (-459967685913577879969221080053341/7036874417766400000000000000000000), (-261249776841463248107735172733143/56294995342131200000000000000000000), (-11481059593151144265950708282859/56294995342131200000000000000000000), (-2044695078712391010814981085297/56294995342131200000000000000000000), (187450596567218494152403322991/7036874417766400000000000000000000), (20503075668733923061044528341/14073748835532800000000000000000000), (-960189581452899130199234211/1407374883553280000000000000000000), (-659017337783477069125177373/56294995342131200000000000000000000), (246099952141522783977428663/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial168.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial168.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial168.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial168 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 43987122149183142241876842461332141), (Int.negOfNat 4809019352507746707886979660507968), (Int.negOfNat 264386767075256492996904648296942), (Int.ofNat 25067023724795606318163260032773), (Int.ofNat 8209838451154138235579783885167), (Int.negOfNat 151228750145079239382662459208), (Int.negOfNat 250047616563795886354613272350), (Int.ofNat 4398704274466150196702278069), (Int.ofNat 4125745419167035971922292861), (Int.negOfNat 97093987650440173872522189), (Int.negOfNat 39527460336388388056604002), (Int.ofNat 1086300243421944444054082), (Int.ofNat 244578063204962928411535), (Int.negOfNat 7240229620722196631189), (Int.negOfNat 1062212900608491887977), (Int.ofNat 33124054276829943337), (Int.ofNat 4167916828310039340), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(43987122149183142241876842461332141/56294995342131200000000000000000000), (-75140927382933542310734057195437/879609302220800000000000000000000), (-132193383537628246498452324148471/28147497671065600000000000000000000), (25067023724795606318163260032773/56294995342131200000000000000000000), (8209838451154138235579783885167/56294995342131200000000000000000000), (-18903593768134904922832807401/7036874417766400000000000000000000), (-5000952331275917727092265447/1125899906842624000000000000000000), (4398704274466150196702278069/56294995342131200000000000000000000), (4125745419167035971922292861/56294995342131200000000000000000000), (-97093987650440173872522189/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial168.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial168.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial168.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial168 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 33624119801237123320199605243419772), (Int.negOfNat 5357367701320163741584645736509954), (Int.ofNat 20433870895854331117699262912334), (Int.ofNat 53487050447486280983937732024333), (Int.negOfNat 3302314009765666842964276104104), (Int.negOfNat 1394899757390148573315836924972), (Int.ofNat 103781971705292684414347178866), (Int.ofNat 29225759983991729634573820209), (Int.negOfNat 1832035927169804393807408109), (Int.negOfNat 354553305427055266545437535), (Int.ofNat 19883401162319572034497599), (Int.ofNat 2678672921877234028236899), (Int.negOfNat 141269407596308441632036), (Int.negOfNat 13741651458752151228530), (Int.ofNat 697982691568254918415), (Int.ofNat 51048877493005999721), (Int.negOfNat 2291947227754203655), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(8406029950309280830049901310854943/14073748835532800000000000000000000), (-2678683850660081870792322868254977/28147497671065600000000000000000000), (10216935447927165558849631456167/28147497671065600000000000000000000), (53487050447486280983937732024333/56294995342131200000000000000000000), (-412789251220708355370534513013/7036874417766400000000000000000000), (-348724939347537143328959231243/14073748835532800000000000000000000), (51890985852646342207173589433/28147497671065600000000000000000000), (29225759983991729634573820209/56294995342131200000000000000000000), (-1832035927169804393807408109/56294995342131200000000000000000000), (-70910661085411053309087507/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial168.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial168.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial168.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial168 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 23331300048557354845621201685062112), (Int.negOfNat 4820599394871859529234490165975616), (Int.ofNat 190432294053620519682299990108908), (Int.negOfNat 545777505872548661823550416028), (Int.negOfNat 5964336712740805578185655769787), (Int.ofNat 991455071712276575993529854642), (Int.ofNat 165174435377814117680361184577), (Int.negOfNat 22627623554557355928186991029), (Int.negOfNat 2617745733988385364379483882), (Int.ofNat 283185036429813281641079191), (Int.ofNat 24587151254085232616655431), (Int.negOfNat 2286848433969095946781713), (Int.negOfNat 150880797056136727879391), (Int.ofNat 12762923960205963115673), (Int.ofNat 651975245084671443462), (Int.negOfNat 51997034921854621337), (Int.negOfNat 2549751476847749490), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(729103126517417338925662552658191/1759218604441600000000000000000000), (-75321865544872805144288908843369/879609302220800000000000000000000), (47608073513405129920574997527227/14073748835532800000000000000000000), (-136444376468137165455887604007/14073748835532800000000000000000000), (-5964336712740805578185655769787/56294995342131200000000000000000000), (495727535856138287996764927321/28147497671065600000000000000000000), (165174435377814117680361184577/56294995342131200000000000000000000), (-22627623554557355928186991029/56294995342131200000000000000000000), (-1308872866994192682189741941/28147497671065600000000000000000000), (283185036429813281641079191/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial168.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial168.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial168.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial168 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 14390931055003240396457606407817133), (Int.negOfNat 4157316554686862623046266964164239), (Int.ofNat 144590855424687446359546416818249), (Int.ofNat 2253762618635979257249028391506), (Int.ofNat 5954792861759996109293076289916), (Int.ofNat 591037599991173532225767785957), (Int.negOfNat 211457908250383945554202878095), (Int.negOfNat 14433337006277757407848433495), (Int.ofNat 3295347966023606521069509716), (Int.ofNat 175516295895568880653084229), (Int.negOfNat 31519512775662021599243949), (Int.negOfNat 1311077665257091305642045), (Int.ofNat 203812388573075837827594), (Int.ofNat 6640457354140311184280), (Int.negOfNat 943268370384773026918), (Int.negOfNat 23912662326262542820), (Int.ofNat 2834482671195605500), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(14390931055003240396457606407817133/56294995342131200000000000000000000), (-4157316554686862623046266964164239/56294995342131200000000000000000000), (144590855424687446359546416818249/56294995342131200000000000000000000), (1126881309317989628624514195753/28147497671065600000000000000000000), (1488698215439999027323269072479/14073748835532800000000000000000000), (591037599991173532225767785957/56294995342131200000000000000000000), (-42291581650076789110840575619/11258999068426240000000000000000000), (-2886667401255551481569686699/11258999068426240000000000000000000), (823836991505901630267377429/14073748835532800000000000000000000), (175516295895568880653084229/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial168.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial168.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial168.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial168 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 6772399969458799506915816392716036), (Int.negOfNat 3357529727758026143262904392791461), (Int.ofNat 294190853303994508955622633343344), (Int.ofNat 37951161878153603022037168835032), (Int.negOfNat 916925039932686747493609444034), (Int.negOfNat 1599804311975426086572791459943), (Int.negOfNat 39037186581232713216439446491), (Int.ofNat 31844775487705311913376081080), (Int.ofNat 747784740561005097310081510), (Int.negOfNat 371952803070411548002232962), (Int.negOfNat 7082885972776957887706330), (Int.ofNat 2845222261610486444337821), (Int.ofNat 42150036916841469274244), (Int.negOfNat 15250008163922757633576), (Int.negOfNat 173372893788627698255), (Int.ofNat 60443936852758301567), (Int.ofNat 931586125385459640), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(1693099992364699876728954098179009/14073748835532800000000000000000000), (-3357529727758026143262904392791461/56294995342131200000000000000000000), (18386928331499656809726414583959/3518437208883200000000000000000000), (4743895234769200377754646104379/7036874417766400000000000000000000), (-458462519966343373746804722017/28147497671065600000000000000000000), (-1599804311975426086572791459943/56294995342131200000000000000000000), (-39037186581232713216439446491/56294995342131200000000000000000000), (796119387192632797834402027/1407374883553280000000000000000000), (74778474056100509731008151/5629499534213120000000000000000000), (-185976401535205774001116481/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial168.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial168.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial168.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial168 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 1473426048917916382415202670877432), (Int.negOfNat 1876002243415419973518053952592069), (Int.ofNat 383563041015418900620124165612096), (Int.negOfNat 22437220948860057016625380783044), (Int.negOfNat 10978119766787436612608992347953), (Int.ofNat 218128166960063055659080913681), (Int.ofNat 258017999308154621511745417158), (Int.negOfNat 2112841544474264410797334184), (Int.negOfNat 3745103354472958632755222219), (Int.ofNat 19878700477935240106651738), (Int.ofNat 34577101235667610290582658), (Int.negOfNat 159009335908181857081763), (Int.negOfNat 217829727079895369867263), (Int.ofNat 991003808914456084715), (Int.ofNat 988351141308807387880), (Int.negOfNat 5761678895782066481), (Int.negOfNat 3377018114637007345), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(184178256114739547801900333859679/7036874417766400000000000000000000), (-1876002243415419973518053952592069/56294995342131200000000000000000000), (5993172515865920322189440087689/879609302220800000000000000000000), (-5609305237215014254156345195761/14073748835532800000000000000000000), (-10978119766787436612608992347953/56294995342131200000000000000000000), (218128166960063055659080913681/56294995342131200000000000000000000), (129008999654077310755872708579/28147497671065600000000000000000000), (-264105193059283051349666773/7036874417766400000000000000000000), (-3745103354472958632755222219/56294995342131200000000000000000000), (9939350238967620053325869/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial168.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial168.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial168.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial168 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 1077165503648443576928280181911862), (Int.negOfNat 899872538607020625665447956623960), (Int.ofNat 57179606083521977746059736292461), (Int.negOfNat 67540864989177824495352421322852), (Int.ofNat 2410018139302443800429455490515), (Int.ofNat 1752478159314287830137472938338), (Int.negOfNat 75767775604102650074981402024), (Int.negOfNat 31820916781354361927134128622), (Int.ofNat 1118227815673295607344017066), (Int.ofNat 361700448412191282683694095), (Int.negOfNat 10348569806052942526931755), (Int.negOfNat 2722193728547553781906108), (Int.ofNat 65860368671117918982161), (Int.ofNat 14432993948440985516859), (Int.negOfNat 303985447763859494543), (Int.negOfNat 57010240367496681683), (Int.ofNat 867424373890630825), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-538582751824221788464140090955931/28147497671065600000000000000000000), (-22496813465175515641636198915599/1407374883553280000000000000000000), (57179606083521977746059736292461/56294995342131200000000000000000000), (-16885216247294456123838105330713/14073748835532800000000000000000000), (482003627860488760085891098103/11258999068426240000000000000000000), (876239079657143915068736469169/28147497671065600000000000000000000), (-9470971950512831259372675253/7036874417766400000000000000000000), (-15910458390677180963567064311/28147497671065600000000000000000000), (559113907836647803672008533/28147497671065600000000000000000000), (72340089682438256536738819/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial168.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial168.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial168.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial168 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 3102346033921069322308265161093636), (Int.negOfNat 1291231730078351776347616165150581), (Int.negOfNat 186113513736261379380711584283622), (Int.negOfNat 4418405856948744103517573000322), (Int.ofNat 8948766819680232251242634486287), (Int.negOfNat 752520153654739405510143977086), (Int.negOfNat 221274455410447844611290543676), (Int.ofNat 16884202659817352111012562678), (Int.ofNat 3189067398728737366580083434), (Int.negOfNat 198257328138167306157391405), (Int.negOfNat 29221743293442912955035945), (Int.ofNat 1504334358076571153759792), (Int.ofNat 183385421594372483852639), (Int.negOfNat 7997860212383138643041), (Int.negOfNat 832885051823232649657), (Int.ofNat 32277685374878819917), (Int.ofNat 2659931509289748675), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-775586508480267330577066290273409/14073748835532800000000000000000000), (-1291231730078351776347616165150581/56294995342131200000000000000000000), (-93056756868130689690355792141811/28147497671065600000000000000000000), (-2209202928474372051758786500161/28147497671065600000000000000000000), (8948766819680232251242634486287/56294995342131200000000000000000000), (-376260076827369702755071988543/28147497671065600000000000000000000), (-55318613852611961152822635919/14073748835532800000000000000000000), (8442101329908676055506281339/28147497671065600000000000000000000), (1594533699364368683290041717/28147497671065600000000000000000000), (-39651465627633461231478281/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial168.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial168.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial168.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial168 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 6356822834394213023405214202844492), (Int.negOfNat 1894788157842764459169062328762828), (Int.negOfNat 95297038114062862677031894849678), (Int.ofNat 15403601311237092915816316305813), (Int.negOfNat 4662576628908597625250071613623), (Int.negOfNat 1136467768073144526833439177458), (Int.ofNat 171654784286698134212129059542), (Int.ofNat 22719940267477003928329340416), (Int.negOfNat 2656960236382041322583825881), (Int.negOfNat 260331210970901843511388262), (Int.ofNat 24825277416548466090023342), (Int.ofNat 1969667320359557713533637), (Int.negOfNat 156214242292992657482237), (Int.negOfNat 10521768845044304844185), (Int.ofNat 706091634757302062820), (Int.ofNat 42776186900670575219), (Int.negOfNat 2307891570493091955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-1589205708598553255851303550711123/14073748835532800000000000000000000), (-473697039460691114792265582190707/14073748835532800000000000000000000), (-47648519057031431338515947424839/28147497671065600000000000000000000), (15403601311237092915816316305813/56294995342131200000000000000000000), (-4662576628908597625250071613623/56294995342131200000000000000000000), (-568233884036572263416719588729/28147497671065600000000000000000000), (85827392143349067106064529771/28147497671065600000000000000000000), (44374883334916023297518243/109951162777600000000000000000000), (-2656960236382041322583825881/56294995342131200000000000000000000), (-130165605485450921755694131/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial168.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial168.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial168.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial168 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 10502217357824567792281418568819422), (Int.negOfNat 2291292264299606620456863891562891), (Int.negOfNat 154861112711754196964202281462321), (Int.negOfNat 32884173651673787028849156392152), (Int.negOfNat 2997810755260268535443355375022), (Int.ofNat 1356674056170831416712639256472), (Int.ofNat 118822809890356239948336326391), (Int.negOfNat 27798882763771521313127969120), (Int.negOfNat 1784098080128113101987461010), (Int.ofNat 328644084070176209561042638), (Int.ofNat 16688323736487203603886830), (Int.negOfNat 2502899666775175313557879), (Int.negOfNat 107300355010705804809444), (Int.ofNat 13266196991609292929024), (Int.ofNat 496706136300248351955), (Int.negOfNat 52333618419942301533), (Int.negOfNat 1222611305641259440), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-5251108678912283896140709284409711/28147497671065600000000000000000000), (-2291292264299606620456863891562891/56294995342131200000000000000000000), (-154861112711754196964202281462321/56294995342131200000000000000000000), (-4110521706459223378606144549019/7036874417766400000000000000000000), (-1498905377630134267721677687511/28147497671065600000000000000000000), (169584257021353927089079907059/7036874417766400000000000000000000), (118822809890356239948336326391/56294995342131200000000000000000000), (-173743017273572008207049807/351843720888320000000000000000000), (-178409808012811310198746101/5629499534213120000000000000000000), (164322042035088104780521319/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial168.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial168.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial168.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial168 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 15968101550795535623696726694343996), (Int.negOfNat 3283397094303522616911317462495463), (Int.negOfNat 307309000665220083913799627865721), (Int.negOfNat 443056467665125732253667075679), (Int.ofNat 9351700011271106845825442576323), (Int.ofNat 365115837908482498513469348596), (Int.negOfNat 233451830999448423678272282140), (Int.negOfNat 7349368005387286231392643895), (Int.ofNat 3577827836616188351254240084), (Int.ofNat 88607215496738213655256829), (Int.negOfNat 33796296671363182407377751), (Int.negOfNat 724334787617222667223545), (Int.ofNat 213940180336388656924106), (Int.ofNat 4183864319928887486780), (Int.negOfNat 966174299832141120882), (Int.negOfNat 18511683073972189520), (Int.ofNat 2850427013934493800), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-3992025387698883905924181673585999/14073748835532800000000000000000000), (-3283397094303522616911317462495463/56294995342131200000000000000000000), (-307309000665220083913799627865721/56294995342131200000000000000000000), (-443056467665125732253667075679/56294995342131200000000000000000000), (9351700011271106845825442576323/56294995342131200000000000000000000), (91278959477120624628367337149/14073748835532800000000000000000000), (-11672591549972421183913614107/2814749767106560000000000000000000), (-1469873601077457246278528779/11258999068426240000000000000000000), (894456959154047087813560021/14073748835532800000000000000000000), (88607215496738213655256829/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial168.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial168.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial168.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial168 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 23621320828756892299761551424431975), (Int.negOfNat 4233909357763850458046365276092439), (Int.negOfNat 110859689892097271788389625255026), (Int.ofNat 53869935696605163646503123227937), (Int.ofNat 845164796828782009628549174603), (Int.negOfNat 1544053791540837952432712908658), (Int.ofNat 12462519143651421783426607373), (Int.ofNat 31833399941555286313443645571), (Int.negOfNat 189480331901060300632766518), (Int.negOfNat 385025696483983080373574609), (Int.ofNat 837646634061373763333269), (Int.ofNat 2976930899749985795187387), (Int.ofNat 2087723213293014170791), (Int.negOfNat 15920946719758409175527), (Int.negOfNat 45122219780990157862), (Int.ofNat 62694611861673885263), (Int.negOfNat 395554045821030410), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-944852833150275691990462056977279/2251799813685248000000000000000000), (-4233909357763850458046365276092439/56294995342131200000000000000000000), (-55429844946048635894194812627513/28147497671065600000000000000000000), (53869935696605163646503123227937/56294995342131200000000000000000000), (845164796828782009628549174603/56294995342131200000000000000000000), (-772026895770418976216356454329/28147497671065600000000000000000000), (12462519143651421783426607373/56294995342131200000000000000000000), (31833399941555286313443645571/56294995342131200000000000000000000), (-94740165950530150316383259/28147497671065600000000000000000000), (-385025696483983080373574609/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial168.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial168.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial168.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial168 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 32132872432600864015684216758907205), (Int.negOfNat 4111777844275068585143926604634361), (Int.ofNat 131479993268038366256155386667240), (Int.ofNat 16414629652566306928269534691756), (Int.negOfNat 6567343984899772530863218780528), (Int.ofNat 508290379773621935449859681250), (Int.ofNat 221746520370892796303178462934), (Int.negOfNat 11733914532438510507742131891), (Int.negOfNat 3637266538995864217547730491), (Int.ofNat 124595672527666927963159365), (Int.ofNat 35423192407187103886187801), (Int.negOfNat 813064751188157145160001), (Int.negOfNat 228577389765252041269964), (Int.ofNat 3581286136055464047470), (Int.ofNat 1050383619178382843085), (Int.negOfNat 10448500609977068379), (Int.negOfNat 3392962457375895645), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-6426574486520172803136843351781441/11258999068426240000000000000000000), (-4111777844275068585143926604634361/56294995342131200000000000000000000), (3286999831700959156403884666681/1407374883553280000000000000000000), (4103657413141576732067383672939/14073748835532800000000000000000000), (-410458999056235783178951173783/3518437208883200000000000000000000), (81326460763779509671977549/9007199254740992000000000000000), (110873260185446398151589231467/28147497671065600000000000000000000), (-11733914532438510507742131891/56294995342131200000000000000000000), (-3637266538995864217547730491/56294995342131200000000000000000000), (24919134505533385592631873/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial168.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial168.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial168.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial168 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 39776147115631731337705174482213338), (Int.negOfNat 3524326149720138922297553498252781), (Int.ofNat 152775552578430396508412319715287), (Int.ofNat 7753591075949659457507486365902), (Int.ofNat 5378592352023429586148487153922), (Int.ofNat 1045917336617598174123971610657), (Int.negOfNat 171154282583331558797877532550), (Int.negOfNat 27253069324300869626827297631), (Int.ofNat 2426543857941510155176940439), (Int.ofNat 351508168295214279436664511), (Int.negOfNat 20589084833530148973999598), (Int.negOfNat 2820911833677475391159418), (Int.ofNat 116077842998760842520965), (Int.ofNat 15461403402244325653711), (Int.negOfNat 465525093634618921423), (Int.negOfNat 61906145998029268763), (Int.ofNat 2013719397283320260), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-19888073557815865668852587241106669/28147497671065600000000000000000000), (-3524326149720138922297553498252781/56294995342131200000000000000000000), (152775552578430396508412319715287/56294995342131200000000000000000000), (3876795537974829728753743182951/28147497671065600000000000000000000), (2689296176011714793074243576961/28147497671065600000000000000000000), (1045917336617598174123971610657/56294995342131200000000000000000000), (-3423085651666631175957550651/1125899906842624000000000000000000), (-27253069324300869626827297631/56294995342131200000000000000000000), (2426543857941510155176940439/56294995342131200000000000000000000), (351508168295214279436664511/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial168.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial168.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial168.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial168 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 46045809011121326887134815372738731), (Int.negOfNat 2606302428096785260529833964757118), (Int.ofNat 358327197634512081601630741929327), (Int.ofNat 55792440858341779389646120285828), (Int.ofNat 1696522001302183590864973758498), (Int.negOfNat 1734685821188934493697179491418), (Int.negOfNat 145833221453119584094686196214), (Int.ofNat 31874805062410900500126060660), (Int.ofNat 2746823061828019528192594773), (Int.negOfNat 346114125482937939217135474), (Int.negOfNat 28866832525390255440551783), (Int.ofNat 2412202178346361136372313), (Int.ofNat 195879471881003721320652), (Int.negOfNat 11626506106117344679115), (Int.negOfNat 926300292790026451872), (Int.ofNat 41529153044300956878), (Int.ofNat 3396109450329867540), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-46045809011121326887134815372738731/56294995342131200000000000000000000), (-1303151214048392630264916982378559/28147497671065600000000000000000000), (358327197634512081601630741929327/56294995342131200000000000000000000), (13948110214585444847411530071457/14073748835532800000000000000000000), (848261000651091795432486879249/28147497671065600000000000000000000), (-867342910594467246848589745709/28147497671065600000000000000000000), (-72916610726559792047343098107/28147497671065600000000000000000000), (1593740253120545025006303033/2814749767106560000000000000000000), (2746823061828019528192594773/56294995342131200000000000000000000), (-173057062741468969608567737/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial168.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial168.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial168.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial168 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 49411882445065887192415000865596984), (Int.negOfNat 599791802037093397458255122715484), (Int.ofNat 584517271822808924888946975989993), (Int.negOfNat 2768089494248923143901544908960), (Int.negOfNat 14060802553334704202958162245356), (Int.negOfNat 420620761468024915442189928229), (Int.ofNat 322583896301434088630687198626), (Int.ofNat 14371710568402601724565634030), (Int.negOfNat 4558093481066753498592597667), (Int.negOfNat 223413261671417706244107796), (Int.ofNat 39710454033674600507079697), (Int.ofNat 2018715663166007933656287), (Int.negOfNat 230272229558403194675968), (Int.negOfNat 11871623007019592999145), (Int.ofNat 952092314070571557928), (Int.ofNat 49249451764333175102), (Int.negOfNat 3454186593885781390), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-6176485305633235899051875108199623/7036874417766400000000000000000000), (-149947950509273349364563780678871/14073748835532800000000000000000000), (584517271822808924888946975989993/56294995342131200000000000000000000), (-17300559339055769649384655681/351843720888320000000000000000000), (-3515200638333676050739540561339/14073748835532800000000000000000000), (-420620761468024915442189928229/56294995342131200000000000000000000), (161291948150717044315343599313/28147497671065600000000000000000000), (1437171056840260172456563403/5629499534213120000000000000000000), (-4558093481066753498592597667/56294995342131200000000000000000000), (-55853315417854426561026949/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial168.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial168.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial168.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial168 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 48512726919790082034494535856657476), (Int.ofNat 1284877156164052806380678188438666), (Int.ofNat 275177389432072491996310901074422), (Int.negOfNat 81120335823130483759895464568385), (Int.negOfNat 307220634981915439829580966431), (Int.ofNat 2518940947290497066381472808649), (Int.ofNat 11026292127267935777029639340), (Int.negOfNat 48608098184994124383727778659), (Int.negOfNat 867104713964456618973155901), (Int.ofNat 545593337755414780993552659), (Int.ofNat 14364069896722896051498582), (Int.negOfNat 3860912215587469644103082), (Int.negOfNat 118986756693020719274455), (Int.ofNat 18828104757696158502149), (Int.ofNat 624351869438348562277), (Int.negOfNat 69030666437796495817), (Int.negOfNat 2679022844982608870), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-12128181729947520508623633964164369/14073748835532800000000000000000000), (642438578082026403190339094219333/28147497671065600000000000000000000), (137588694716036245998155450537211/28147497671065600000000000000000000), (-16224067164626096751979092913677/11258999068426240000000000000000000), (-307220634981915439829580966431/56294995342131200000000000000000000), (2518940947290497066381472808649/56294995342131200000000000000000000), (551314606363396788851481967/2814749767106560000000000000000000), (-48608098184994124383727778659/56294995342131200000000000000000000), (-867104713964456618973155901/56294995342131200000000000000000000), (545593337755414780993552659/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial168.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial168.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial168.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial168 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 45420987468666555615842675743935586), (Int.ofNat 1584564838268725267647224415976110), (Int.negOfNat 46408847216215768099159444717479), (Int.negOfNat 6847544677573832188121451003974), (Int.ofNat 13184392709676361302158383880436), (Int.negOfNat 724142314673932274709449904303), (Int.negOfNat 411389679636456624024493185856), (Int.ofNat 8692471517723701664477459201), (Int.ofNat 6334696730711747676923548149), (Int.ofNat 5598815981737570266179005), (Int.negOfNat 56096124484312959604792179), (Int.negOfNat 661308799553727760359899), (Int.ofNat 325898181843313632352956), (Int.ofNat 5650796237390156159490), (Int.negOfNat 1350756918719193092715), (Int.negOfNat 27226573759767112201), (Int.ofNat 4536110487814613185), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-22710493734333277807921337871967793/28147497671065600000000000000000000), (158456483826872526764722441597611/5629499534213120000000000000000000), (-46408847216215768099159444717479/56294995342131200000000000000000000), (-3423772338786916094060725501987/28147497671065600000000000000000000), (3296098177419090325539595970109/14073748835532800000000000000000000), (-724142314673932274709449904303/56294995342131200000000000000000000), (-6427963744319634750382706029/879609302220800000000000000000000), (8692471517723701664477459201/56294995342131200000000000000000000), (6334696730711747676923548149/56294995342131200000000000000000000), (1119763196347514053235801/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial168.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial168.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial168.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial168 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 42328145001679623502896913751972701), (Int.ofNat 1611848622282864294241998784478972), (Int.ofNat 88842877769793878103683756322029), (Int.ofNat 19236970577653989336745473852836), (Int.negOfNat 9929013440279788418251341199613), (Int.negOfNat 2519863203771199061846911833507), (Int.ofNat 244733446139155544543158134048), (Int.ofNat 61776721573254624515469454619), (Int.negOfNat 1988776612905637078724631078), (Int.negOfNat 712486418109535778813296661), (Int.ofNat 6310982231945464330597989), (Int.ofNat 5008449623304668121329713), (Int.ofNat 9568268400112270285311), (Int.negOfNat 24244246666694518561633), (Int.negOfNat 182791393499980727762), (Int.ofNat 87903647082821173817), (Int.ofNat 1060857493520319020), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-42328145001679623502896913751972701/56294995342131200000000000000000000), (402962155570716073560499696119743/14073748835532800000000000000000000), (88842877769793878103683756322029/56294995342131200000000000000000000), (4809242644413497334186368463209/14073748835532800000000000000000000), (-9929013440279788418251341199613/56294995342131200000000000000000000), (-2519863203771199061846911833507/56294995342131200000000000000000000), (7647920191848610766973691689/1759218604441600000000000000000000), (61776721573254624515469454619/56294995342131200000000000000000000), (-994388306452818539362315539/28147497671065600000000000000000000), (-712486418109535778813296661/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial168.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial168.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial168.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial168 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 38811967317687935028276851861665948), (Int.ofNat 1749820683243394342015122487158414), (Int.negOfNat 142007196570905029187102107906386), (Int.negOfNat 94329064751866290360782108147894), (Int.negOfNat 7957558647750093592821959947470), (Int.ofNat 3470885598194446908936894203742), (Int.ofNat 498648866344590041399274023085), (Int.negOfNat 42494670539746609784217314915), (Int.negOfNat 7952405308854366879913434756), (Int.ofNat 271103247995422989202369301), (Int.ofNat 68853531247091149162755529), (Int.negOfNat 1022979463563986875671955), (Int.negOfNat 392019716879748561375514), (Int.ofNat 2173332129039455909760), (Int.ofNat 1607127183034075251218), (Int.ofNat 90358593023655300), (Int.negOfNat 5078645931256015030), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-9702991829421983757069212965416487/14073748835532800000000000000000000), (874910341621697171007561243579207/28147497671065600000000000000000000), (-71003598285452514593551053953193/28147497671065600000000000000000000), (-47164532375933145180391054073947/28147497671065600000000000000000000), (-795755864775009359282195994747/5629499534213120000000000000000000), (1735442799097223454468447101871/28147497671065600000000000000000000), (99729773268918008279854804617/11258999068426240000000000000000000), (-8498934107949321956843462983/11258999068426240000000000000000000), (-1988101327213591719978358689/14073748835532800000000000000000000), (271103247995422989202369301/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial168.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial168.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial168.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial168 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 36626595806987958973903106113506838), (Int.ofNat 142388089996174462682293588710575), (Int.negOfNat 542435475053577883030669523733395), (Int.ofNat 25011466456111271452578347877095), (Int.ofNat 37793023568174435804356347474345), (Int.ofNat 3356548811847521392223756731993), (Int.negOfNat 610052580673339300786046887519), (Int.negOfNat 79017027600813955110690296670), (Int.ofNat 5247563424384360349169651450), (Int.ofNat 853618291040236479195871432), (Int.negOfNat 28972160837350118567280090), (Int.negOfNat 5751681966167084281666821), (Int.ofNat 112475032589880513228836), (Int.ofNat 27163886391668084862536), (Int.negOfNat 324184887020310967445), (Int.negOfNat 96350549013724854047), (Int.ofNat 557307857941970830), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-18313297903493979486951553056753419/28147497671065600000000000000000000), (5695523599846978507291743548423/2251799813685248000000000000000000), (-108487095010715576606133904746679/11258999068426240000000000000000000), (5002293291222254290515669575419/11258999068426240000000000000000000), (7558604713634887160871269494869/11258999068426240000000000000000000), (3356548811847521392223756731993/56294995342131200000000000000000000), (-610052580673339300786046887519/56294995342131200000000000000000000), (-7901702760081395511069029667/5629499534213120000000000000000000), (104951268487687206983393029/1125899906842624000000000000000000), (106702286380029559899483929/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial168.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial168.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial168.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial168 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 37646789744498744150204787702890305), (Int.negOfNat 394714010045845628798539132285056), (Int.ofNat 596530851927046741107131977558175), (Int.ofNat 333084590610300344372841282693545), (Int.ofNat 21340918099425010108710441216416), (Int.negOfNat 6913669974980765294890568502341), (Int.negOfNat 725177009059810159266178647148), (Int.ofNat 75225338904065562194459988594), (Int.ofNat 9679157359349825588661479259), (Int.negOfNat 531369146081016269634801268), (Int.negOfNat 77087044815348888248901238), (Int.ofNat 2678626897658287035540763), (Int.ofNat 419934582723366741086183), (Int.negOfNat 10196091726880423795755), (Int.negOfNat 1680074905627480222180), (Int.ofNat 29583982629020954001), (Int.ofNat 5621181374697416875), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-7529357948899748830040957540578061/11258999068426240000000000000000000), (-3083703203483168974988586970977/439804651110400000000000000000000), (23861234077081869644285279102327/2251799813685248000000000000000000), (66616918122060068874568256538709/11258999068426240000000000000000000), (666903690607031565897201288013/1759218604441600000000000000000000), (-6913669974980765294890568502341/56294995342131200000000000000000000), (-181294252264952539816544661787/14073748835532800000000000000000000), (37612669452032781097229994297/28147497671065600000000000000000000), (9679157359349825588661479259/56294995342131200000000000000000000), (-132842286520254067408700317/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial168.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial168.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial168.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial168 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 33299848904534791191665054736839768), (Int.ofNat 6021039495935619749814972101611725), (Int.ofNat 2444745827394587494523156563295417), (Int.ofNat 166823644264738572508714564506800), (Int.negOfNat 62420155453551656479076258585257), (Int.negOfNat 6536644838832180579277254294053), (Int.ofNat 856971255565821007494665210419), (Int.ofNat 102577409776960168460654253212), (Int.negOfNat 7601662979397408925462639026), (Int.negOfNat 952440453381814161342322565), (Int.ofNat 47727999896614495463203175), (Int.ofNat 5965592550597447600686108), (Int.negOfNat 223313732280566876018241), (Int.negOfNat 27078548137436018490819), (Int.ofNat 806984520468002000243), (Int.ofNat 92916852528463234163), (Int.negOfNat 2356318357218061295), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-4162481113066848898958131842104971/7036874417766400000000000000000000), (240841579837424789992598884064469/2251799813685248000000000000000000), (2444745827394587494523156563295417/56294995342131200000000000000000000), (417059110661846431271786411267/140737488355328000000000000000000), (-62420155453551656479076258585257/56294995342131200000000000000000000), (-6536644838832180579277254294053/56294995342131200000000000000000000), (856971255565821007494665210419/56294995342131200000000000000000000), (25644352444240042115163563303/14073748835532800000000000000000000), (-3800831489698704462731319513/28147497671065600000000000000000000), (-190488090676362832268464513/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial168.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial168.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial168.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial168.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial168 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial168 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial168 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 48112100085557621825880441152704722), (Int.negOfNat 8267922343711069733157275096063756), (Int.ofNat 2879362519028566495501146956907106), (Int.negOfNat 147994848284440795374131411623990), (Int.negOfNat 64725917794277018289004666197949), (Int.ofNat 6483020111869240818247177272774), (Int.ofNat 862105453686271965979027748034), (Int.negOfNat 102497674720258006370799281212), (Int.negOfNat 7607946551548601391489048026), (Int.ofNat 952367272620411499113695565), (Int.ofNat 47732841244031740758535175), (Int.negOfNat 5965544839643832874910108), (Int.negOfNat 223313732280566876018241), (Int.ofNat 27078548137436018490819), (Int.ofNat 806984520468002000243), (Int.negOfNat 92916852528463234163), (Int.negOfNat 2356318357218061295), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-24056050042778810912940220576352361/28147497671065600000000000000000000), (-2066980585927767433289318774015939/14073748835532800000000000000000000), (1439681259514283247750573478453553/28147497671065600000000000000000000), (-14799484828444079537413141162399/5629499534213120000000000000000000), (-64725917794277018289004666197949/56294995342131200000000000000000000), (3241510055934620409123588636387/28147497671065600000000000000000000), (431052726843135982989513874017/28147497671065600000000000000000000), (-25624418680064501592699820303/14073748835532800000000000000000000), (-3803973275774300695744524013/28147497671065600000000000000000000), (190473454524082299822739113/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial168.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial168.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial168.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 55101980521659839470868009028646200), (Int.ofNat 35184017128389204930160046092646), (Int.ofNat 1085766294171020098621360053682793), (Int.negOfNat 333992336616559506759887549134473), (Int.ofNat 18822020252982191198014539197110), (Int.ofNat 6925430958952369892008656306247), (Int.negOfNat 719662656379905202613787253148), (Int.negOfNat 75251853107618955591500107594), (Int.ofNat 9672467936670355202124063259), (Int.ofNat 531398211940809175267886268), (Int.negOfNat 77081908913593476523296238), (Int.negOfNat 2678644789265892557706763), (Int.ofNat 419934582723366741086183), (Int.ofNat 10196091726880423795755), (Int.negOfNat 1680074905627480222180), (Int.negOfNat 29583982629020954001), (Int.ofNat 5621181374697416875), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-275509902608299197354340045143231/281474976710656000000000000000000), (17592008564194602465080023046323/28147497671065600000000000000000000), (1085766294171020098621360053682793/56294995342131200000000000000000000), (-333992336616559506759887549134473/56294995342131200000000000000000000), (1882202025298219119801453919711/5629499534213120000000000000000000), (6925430958952369892008656306247/56294995342131200000000000000000000), (-179915664094976300653446813287/14073748835532800000000000000000000), (-37625926553809477795750053797/28147497671065600000000000000000000), (9672467936670355202124063259/56294995342131200000000000000000000), (132849552985202293816971567/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial168.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial168.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial168.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 52890744950764351919918200633947859), (Int.ofNat 1365507001974166884460712567123929), (Int.negOfNat 116865346428189273976088058726063), (Int.negOfNat 44744260831595423536370800249505), (Int.ofNat 35707865647779804506553533930144), (Int.negOfNat 3283740483409794822971328952803), (Int.negOfNat 605622297630740155322476554519), (Int.ofNat 78892429013003709408702039670), (Int.ofNat 5242275159884943634907180450), (Int.negOfNat 853495382124834583675635432), (Int.negOfNat 28968128689521930498889090), (Int.ofNat 5751604435867460352280821), (Int.ofNat 112475032589880513228836), (Int.negOfNat 27163886391668084862536), (Int.negOfNat 324184887020310967445), (Int.ofNat 96350549013724854047), (Int.ofNat 557307857941970830), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-52890744950764351919918200633947859/56294995342131200000000000000000000), (1365507001974166884460712567123929/56294995342131200000000000000000000), (-116865346428189273976088058726063/56294995342131200000000000000000000), (-8948852166319084707274160049901/11258999068426240000000000000000000), (1115870801493118890829797935317/1759218604441600000000000000000000), (-3283740483409794822971328952803/56294995342131200000000000000000000), (-605622297630740155322476554519/56294995342131200000000000000000000), (7889242901300370940870203967/5629499534213120000000000000000000), (104845503197698872698143609/1125899906842624000000000000000000), (-106686922765604322959454429/7036874417766400000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial168.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial168.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial168.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 50546674475655732012214056135594917), (Int.ofNat 1163450685417138186769322047127937), (Int.ofNat 121917713525861772281021891686003), (Int.ofNat 61457652750374428302785954551083), (Int.negOfNat 9089080627316120896590113784636), (Int.negOfNat 3357471557953219623780355764033), (Int.ofNat 500837331744536845377984447700), (Int.ofNat 42306560025052320806675402915), (Int.negOfNat 7954875411563691622219000756), (Int.negOfNat 270920404563948516412348301), (Int.ofNat 68855356763314656164006529), (Int.ofNat 1022866150049151901953955), (Int.negOfNat 392019716879748561375514), (Int.negOfNat 2173332129039455909760), (Int.ofNat 1607127183034075251218), (Int.negOfNat 90358593023655300), (Int.negOfNat 5078645931256015030), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-50546674475655732012214056135594917/56294995342131200000000000000000000), (1163450685417138186769322047127937/56294995342131200000000000000000000), (121917713525861772281021891686003/56294995342131200000000000000000000), (61457652750374428302785954551083/56294995342131200000000000000000000), (-2272270156829030224147528446159/14073748835532800000000000000000000), (-3357471557953219623780355764033/56294995342131200000000000000000000), (5008373317445368453779844477/562949953421312000000000000000000), (8461312005010464161335080583/11258999068426240000000000000000000), (-1988718852890922905554750189/14073748835532800000000000000000000), (-270920404563948516412348301/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial168.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial168.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial168.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 47457940733798914652329542281757703), (Int.ofNat 1935863674370424692900751852285995), (Int.ofNat 137851166816883495300436473328035), (Int.negOfNat 56382604652975433503014757571321), (Int.negOfNat 9849767809796055928907784023243), (Int.ofNat 2643010751676435646175203739502), (Int.ofNat 244138951211058102738234783383), (Int.negOfNat 61976904989788662395374870619), (Int.negOfNat 1987786029088381803024677078), (Int.ofNat 712679089818673378745078661), (Int.ofNat 6310112517414622449148989), (Int.negOfNat 5008574864557906776491713), (Int.ofNat 9568268400112270285311), (Int.ofNat 24244246666694518561633), (Int.negOfNat 182791393499980727762), (Int.negOfNat 87903647082821173817), (Int.ofNat 1060857493520319020), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-47457940733798914652329542281757703/56294995342131200000000000000000000), (387172734874084938580150370457199/11258999068426240000000000000000000), (27570233363376699060087294665607/11258999068426240000000000000000000), (-56382604652975433503014757571321/56294995342131200000000000000000000), (-9849767809796055928907784023243/56294995342131200000000000000000000), (1321505375838217823087601869751/28147497671065600000000000000000000), (244138951211058102738234783383/56294995342131200000000000000000000), (-61976904989788662395374870619/56294995342131200000000000000000000), (-993893014544190901512338539/28147497671065600000000000000000000), (712679089818673378745078661/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial168.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial168.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial168.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 43551345192323625463629962553449889), (Int.ofNat 1725618296955603347540473786923732), (Int.negOfNat 208795216116983333438385050248990), (Int.negOfNat 24942651803985583329741199263738), (Int.ofNat 14405262354816861720286642205913), (Int.ofNat 824162196297667009108065783544), (Int.negOfNat 414550996304378331876884849856), (Int.negOfNat 8850518806921729965796634201), (Int.ofNat 6338844353383021725165387149), (Int.negOfNat 5448875976581247325647005), (Int.negOfNat 56099432983222471217895179), (Int.ofNat 661213377646498308807899), (Int.ofNat 325898181843313632352956), (Int.negOfNat 5650796237390156159490), (Int.negOfNat 1350756918719193092715), (Int.ofNat 27226573759767112201), (Int.ofNat 4536110487814613185), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-43551345192323625463629962553449889/56294995342131200000000000000000000), (431404574238900836885118446730933/14073748835532800000000000000000000), (-20879521611698333343838505024899/5629499534213120000000000000000000), (-12471325901992791664870599631869/28147497671065600000000000000000000), (14405262354816861720286642205913/56294995342131200000000000000000000), (103020274537208376138508222943/7036874417766400000000000000000000), (-6477359317255911435576325779/879609302220800000000000000000000), (-8850518806921729965796634201/56294995342131200000000000000000000), (6338844353383021725165387149/56294995342131200000000000000000000), (-1089775195316249465129401/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial168.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial168.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial168.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 40904072289250052825840607001294982), (Int.ofNat 1040674361550412459655819114438881), (Int.negOfNat 41504537276602552859666660166018), (Int.ofNat 62511758680249303813891010041475), (Int.ofNat 1685117299554011482002282250063), (Int.negOfNat 2468001682754520429933467579453), (Int.ofNat 6205215993968174867384810340), (Int.ofNat 48534381022576216704592153659), (Int.negOfNat 860962278893865193360242901), (Int.negOfNat 545526739424624020974675659), (Int.ofNat 14359238286419638819390582), (Int.ofNat 3860876432372258599771082), (Int.negOfNat 118986756693020719274455), (Int.negOfNat 18828104757696158502149), (Int.ofNat 624351869438348562277), (Int.ofNat 69030666437796495817), (Int.negOfNat 2679022844982608870), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-20452036144625026412920303500647491/28147497671065600000000000000000000), (1040674361550412459655819114438881/56294995342131200000000000000000000), (-20752268638301276429833330083009/28147497671065600000000000000000000), (2500470347209972152555640401659/2251799813685248000000000000000000), (1685117299554011482002282250063/56294995342131200000000000000000000), (-2468001682754520429933467579453/56294995342131200000000000000000000), (310260799698408743369240517/2814749767106560000000000000000000), (48534381022576216704592153659/56294995342131200000000000000000000), (-860962278893865193360242901/56294995342131200000000000000000000), (-545526739424624020974675659/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial168.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial168.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial168.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 38534530022786739384607988007969815), (Int.ofNat 1502190388520880695511781310973284), (Int.ofNat 206879795131459718151690895820977), (Int.ofNat 1334422244876157516226997289767), (Int.negOfNat 11861895625283453703825791866460), (Int.ofNat 410361041776278299666417378788), (Int.ofNat 317446805282298108124268470626), (Int.negOfNat 14342345399684149636887342030), (Int.negOfNat 4551654859854111500801368667), (Int.ofNat 223378929196579745104813796), (Int.ofNat 39705432455806650619155697), (Int.negOfNat 2018685843819998730046287), (Int.negOfNat 230272229558403194675968), (Int.ofNat 11871623007019592999145), (Int.ofNat 952092314070571557928), (Int.negOfNat 49249451764333175102), (Int.negOfNat 3454186593885781390), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-7706906004557347876921597601593963/11258999068426240000000000000000000), (375547597130220173877945327743321/14073748835532800000000000000000000), (206879795131459718151690895820977/56294995342131200000000000000000000), (1334422244876157516226997289767/56294995342131200000000000000000000), (-593094781264172685191289593323/2814749767106560000000000000000000), (102590260444069574916604344697/14073748835532800000000000000000000), (158723402641149054062134235313/28147497671065600000000000000000000), (-1434234539968414963688734203/5629499534213120000000000000000000), (-4551654859854111500801368667/56294995342131200000000000000000000), (55844732299144936276203449/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial168.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial168.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial168.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 34851147850278849653255380692785530), (Int.ofNat 2049524667708676623506932120253628), (Int.ofNat 22838860444246681948142706863143), (Int.negOfNat 40839454002412789523523283661541), (Int.ofNat 3499835132830914839909780023097), (Int.ofNat 1668023410806169899159035594172), (Int.negOfNat 149877526882171669107618110264), (Int.negOfNat 31751999099866859249605212660), (Int.ofNat 2751790931354572353900775773), (Int.ofNat 345989021067981870451369474), (Int.negOfNat 28870672380906474618231783), (Int.negOfNat 2412118684177535366264313), (Int.ofNat 195879471881003721320652), (Int.ofNat 11626506106117344679115), (Int.negOfNat 926300292790026451872), (Int.negOfNat 41529153044300956878), (Int.ofNat 3396109450329867540), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-3485114785027884965325538069278553/5629499534213120000000000000000000), (512381166927169155876733030063407/14073748835532800000000000000000000), (22838860444246681948142706863143/56294995342131200000000000000000000), (-40839454002412789523523283661541/56294995342131200000000000000000000), (3499835132830914839909780023097/56294995342131200000000000000000000), (417005852701542474789758898543/14073748835532800000000000000000000), (-18734690860271458638452263783/7036874417766400000000000000000000), (-1587599954993342962480260633/2814749767106560000000000000000000), (2751790931354572353900775773/56294995342131200000000000000000000), (172994510533990935225684737/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial168.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial168.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial168.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 30890893028929052372002892895000141), (Int.ofNat 1856687200805107979645735787039268), (Int.negOfNat 55928164728198764156193504702458), (Int.ofNat 18389261413442299581175695013727), (Int.ofNat 6312020384955394877420536234233), (Int.negOfNat 1148850681815960772899974404792), (Int.negOfNat 173018559650670060641934968550), (Int.ofNat 27434137359297107177828901631), (Int.ofNat 2428690745458167534017082439), (Int.negOfNat 351689020965577858339578511), (Int.negOfNat 20590684598973752275102598), (Int.ofNat 2821031111061512205599418), (Int.ofNat 116077842998760842520965), (Int.negOfNat 15461403402244325653711), (Int.negOfNat 465525093634618921423), (Int.ofNat 61906145998029268763), (Int.ofNat 2013719397283320260), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-30890893028929052372002892895000141/56294995342131200000000000000000000), (464171800201276994911433946759817/14073748835532800000000000000000000), (-27964082364099382078096752351229/28147497671065600000000000000000000), (18389261413442299581175695013727/56294995342131200000000000000000000), (6312020384955394877420536234233/56294995342131200000000000000000000), (-143606335226995096612496800599/7036874417766400000000000000000000), (-3460371193013401212838699371/1125899906842624000000000000000000), (27434137359297107177828901631/56294995342131200000000000000000000), (2428690745458167534017082439/56294995342131200000000000000000000), (-351689020965577858339578511/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial168.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial168.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial168.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 27197022992976310448715021581167472), (Int.ofNat 1944398237576217431290352664494054), (Int.ofNat 93478246007488390412693301344966), (Int.ofNat 12884282393100795004465030403167), (Int.negOfNat 6722748201691927939773539283896), (Int.negOfNat 617797543832196419516062218428), (Int.ofNat 222532488228461190776221425934), (Int.ofNat 11922381758321485179714962891), (Int.negOfNat 3638505237064275048906498491), (Int.negOfNat 124782072025610757383376365), (Int.ofNat 35424250202660245312201801), (Int.ofNat 813184028572193959600001), (Int.negOfNat 228577389765252041269964), (Int.negOfNat 3581286136055464047470), (Int.ofNat 1050383619178382843085), (Int.ofNat 10448500609977068379), (Int.negOfNat 3392962457375895645), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-1699813937061019403044688848822967/3518437208883200000000000000000000), (972199118788108715645176332247027/28147497671065600000000000000000000), (46739123003744195206346650672483/28147497671065600000000000000000000), (12884282393100795004465030403167/56294995342131200000000000000000000), (-840343525211490992471692410487/7036874417766400000000000000000000), (-154449385958049104879015554607/14073748835532800000000000000000000), (111266244114230595388110712967/28147497671065600000000000000000000), (11922381758321485179714962891/56294995342131200000000000000000000), (-3638505237064275048906498491/56294995342131200000000000000000000), (-24956414405122151476675273/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial168.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial168.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial168.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 22943762977390498488752795060871612), (Int.ofNat 2252609846534554512414494826986116), (Int.ofNat 14753979941315011245434455952792), (Int.negOfNat 29966447982403648214141387839472), (Int.negOfNat 307501831184332786143770703313), (Int.ofNat 1458890798616864803585491029358), (Int.ofNat 15628325725525764119695113323), (Int.negOfNat 31689962379743259259871592571), (Int.negOfNat 193731822979185074082053518), (Int.ofNat 384885252416142865690289609), (Int.ofNat 841078049476847796703269), (Int.negOfNat 2976841441711958184357387), (Int.ofNat 2087723213293014170791), (Int.ofNat 15920946719758409175527), (Int.negOfNat 45122219780990157862), (Int.negOfNat 62694611861673885263), (Int.negOfNat 395554045821030410), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-5735940744347624622188198765217903/14073748835532800000000000000000000), (563152461633638628103623706746529/14073748835532800000000000000000000), (1844247492664376405679306994099/7036874417766400000000000000000000), (-1872902998900228013383836739967/3518437208883200000000000000000000), (-307501831184332786143770703313/56294995342131200000000000000000000), (729445399308432401792745514679/28147497671065600000000000000000000), (15628325725525764119695113323/56294995342131200000000000000000000), (-31689962379743259259871592571/56294995342131200000000000000000000), (-96865911489592537041026759/28147497671065600000000000000000000), (384885252416142865690289609/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial168.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial168.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial168.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 18580408207641843727114857276953233), (Int.ofNat 2048363179716164609288871222049939), (Int.negOfNat 71903483443767111048606291217849), (Int.ofNat 12297227977205134764574066359194), (Int.ofNat 7572235975860349278147954488884), (Int.negOfNat 402398139920890747528938970457), (Int.negOfNat 228835731359033557567137146705), (Int.ofNat 7408267598939925004976059895), (Int.ofNat 3571767017993792425272407084), (Int.negOfNat 88663080803149043715005829), (Int.negOfNat 33791466509557435162876751), (Int.ofNat 724370570832433711555545), (Int.ofNat 213940180336388656924106), (Int.negOfNat 4183864319928887486780), (Int.negOfNat 966174299832141120882), (Int.ofNat 18511683073972189520), (Int.ofNat 2850427013934493800), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-18580408207641843727114857276953233/56294995342131200000000000000000000), (2048363179716164609288871222049939/56294995342131200000000000000000000), (-71903483443767111048606291217849/56294995342131200000000000000000000), (6148613988602567382287033179597/28147497671065600000000000000000000), (1893058993965087319536988622221/14073748835532800000000000000000000), (-402398139920890747528938970457/56294995342131200000000000000000000), (-45767146271806711513427429341/11258999068426240000000000000000000), (1481653519787985000995211979/11258999068426240000000000000000000), (892941754498448106318101771/14073748835532800000000000000000000), (-88663080803149043715005829/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial168.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial168.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial168.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 14577499466754423830717558966029636), (Int.ofNat 2081111411638413184318903024900461), (Int.ofNat 107116095041702323779133737751756), (Int.ofNat 29771814580214240905186755565568), (Int.negOfNat 4863587234635200582392545003066), (Int.negOfNat 1336403738023590351142679364557), (Int.ofNat 123563747574952505850708263391), (Int.ofNat 27757521623054240386183244120), (Int.negOfNat 1790269309471545496192685010), (Int.negOfNat 328600251062235501286347638), (Int.ofNat 16693219062729287972685830), (Int.ofNat 2502869847429166109947879), (Int.negOfNat 107300355010705804809444), (Int.negOfNat 13266196991609292929024), (Int.ofNat 496706136300248351955), (Int.ofNat 52333618419942301533), (Int.negOfNat 1222611305641259440), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-3644374866688605957679389741507409/14073748835532800000000000000000000), (2081111411638413184318903024900461/56294995342131200000000000000000000), (26779023760425580944783434437939/14073748835532800000000000000000000), (14537018837995234816985720491/27487790694400000000000000000000), (-2431793617317600291196272501533/28147497671065600000000000000000000), (-1336403738023590351142679364557/56294995342131200000000000000000000), (123563747574952505850708263391/56294995342131200000000000000000000), (693938040576356009654581103/1407374883553280000000000000000000), (-179026930947154549619268501/5629499534213120000000000000000000), (-164300125531117750643173819/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial168.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial168.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial168.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 9858363890349668650213145881067532), (Int.ofNat 2637970142056377874872988606339669), (Int.ofNat 105948234136118276833719510603304), (Int.negOfNat 31906721119378612193375622153356), (Int.negOfNat 6059445498707630058774059813147), (Int.ofNat 1207517067882274783206593139319), (Int.ofNat 175170832744099953002084147542), (Int.negOfNat 22849241664322715263137049416), (Int.negOfNat 2661518624104033745946277881), (Int.ofNat 260462270054437207402630262), (Int.ofNat 24828886871790229097765342), (Int.negOfNat 1969756778397585324363637), (Int.negOfNat 156214242292992657482237), (Int.ofNat 10521768845044304844185), (Int.ofNat 706091634757302062820), (Int.negOfNat 42776186900670575219), (Int.negOfNat 2307891570493091955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-2464590972587417162553286470266883/14073748835532800000000000000000000), (2637970142056377874872988606339669/56294995342131200000000000000000000), (13243529267014784604214938825413/7036874417766400000000000000000000), (-7976680279844653048343905538339/14073748835532800000000000000000000), (-6059445498707630058774059813147/56294995342131200000000000000000000), (1207517067882274783206593139319/56294995342131200000000000000000000), (87585416372049976501042073771/28147497671065600000000000000000000), (-2856155208040339407892131177/7036874417766400000000000000000000), (-2661518624104033745946277881/56294995342131200000000000000000000), (130231135027218603701315131/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial168.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial168.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial168.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 4464435935042780881550812737868838), (Int.ofNat 2602954311683462524374426088407560), (Int.negOfNat 110978433755852284538327262649161), (Int.negOfNat 19934946321263849797726632476248), (Int.ofNat 8432617225689190883514753200385), (Int.ofNat 853149207795109155382077220462), (Int.negOfNat 219980319060760722398001537676), (Int.negOfNat 17064591312381288801836919678), (Int.ofNat 3187392421806730397492790434), (Int.ofNat 198438995811012326715475405), (Int.negOfNat 29220418876355221191107945), (Int.negOfNat 1504453635460607968199792), (Int.ofNat 183385421594372483852639), (Int.ofNat 7997860212383138643041), (Int.negOfNat 832885051823232649657), (Int.negOfNat 32277685374878819917), (Int.ofNat 2659931509289748675), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-2232217967521390440775406368934419/28147497671065600000000000000000000), (65073857792086563109360652210189/1407374883553280000000000000000000), (-110978433755852284538327262649161/56294995342131200000000000000000000), (-2491868290157981224715829059531/7036874417766400000000000000000000), (1686523445137838176702950640077/11258999068426240000000000000000000), (426574603897554577691038610231/28147497671065600000000000000000000), (-54995079765190180599500384419/14073748835532800000000000000000000), (-8532295656190644400918459839/28147497671065600000000000000000000), (1593696210903365198746395217/28147497671065600000000000000000000), (39687799162202465343095081/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial168.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial168.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial168.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 284924397476588653457399936786636), (Int.ofNat 2211595120213592626471886114385481), (Int.negOfNat 17955473896154213805298881768578), (Int.ofNat 43187512810943329161942217448722), (Int.ofNat 2926167733297513417794038834013), (Int.negOfNat 1651849105173886618883733011814), (Int.negOfNat 77061911953789772288270408024), (Int.ofNat 31640528128790425236309771622), (Int.ofNat 1119902792595302576431310066), (Int.negOfNat 361518780739346262125610095), (Int.negOfNat 10349894223140634290859755), (Int.ofNat 2722074451163516967466108), (Int.ofNat 65860368671117918982161), (Int.negOfNat 14432993948440985516859), (Int.negOfNat 303985447763859494543), (Int.ofNat 57010240367496681683), (Int.ofNat 867424373890630825), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(71231099369147163364349984196659/14073748835532800000000000000000000), (2211595120213592626471886114385481/56294995342131200000000000000000000), (-8977736948077106902649440884289/28147497671065600000000000000000000), (21593756405471664580971108724361/28147497671065600000000000000000000), (2926167733297513417794038834013/56294995342131200000000000000000000), (-825924552586943309441866505907/28147497671065600000000000000000000), (-9632738994223721536033801003/7036874417766400000000000000000000), (15820264064395212618154885811/28147497671065600000000000000000000), (559951396297651288215655033/28147497671065600000000000000000000), (-72303756147869252425122019/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial168.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial168.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial168.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 4974967104882051482538677250275592), (Int.ofNat 2619184227632717906379909458390628), (Int.ofNat 182317768765666293600366572513878), (Int.ofNat 5934101140678848713660249870387), (Int.negOfNat 9581250896985746296880239381877), (Int.negOfNat 147078867148810713235904277442), (Int.ofNat 254501950850752802721790329158), (Int.ofNat 1983540147628553075989625184), (Int.negOfNat 3740544966750966209392770219), (Int.negOfNat 19747641394399876215409738), (Int.ofNat 34573491780425847282840658), (Int.ofNat 158919877870154246251763), (Int.negOfNat 217829727079895369867263), (Int.negOfNat 991003808914456084715), (Int.ofNat 988351141308807387880), (Int.ofNat 5761678895782066481), (Int.negOfNat 3377018114637007345), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(621870888110256435317334656284449/7036874417766400000000000000000000), (654796056908179476594977364597657/14073748835532800000000000000000000), (91158884382833146800183286256939/28147497671065600000000000000000000), (5934101140678848713660249870387/56294995342131200000000000000000000), (-9581250896985746296880239381877/56294995342131200000000000000000000), (-73539433574405356617952138721/28147497671065600000000000000000000), (127250975425376401360895164579/28147497671065600000000000000000000), (61985629613392283624675787/1759218604441600000000000000000000), (-3740544966750966209392770219/56294995342131200000000000000000000), (-9873820697199938107704869/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial168.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial168.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial168.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 10847682078406074587882073897383822), (Int.ofNat 3147348875101695523418552412486891), (Int.ofNat 32213645550674210609796466173721), (Int.negOfNat 41063520949641101021921157149548), (Int.ofNat 948851439448156462410782719722), (Int.ofNat 1620074630122273573161645974028), (Int.negOfNat 43778124265828979118811383491), (Int.negOfNat 31886136628422592840320806080), (Int.ofNat 753955969904437491515305510), (Int.ofNat 371996636078352256276927962), (Int.negOfNat 7087781299019042256505330), (Int.negOfNat 2845252080956495647947821), (Int.ofNat 42150036916841469274244), (Int.ofNat 15250008163922757633576), (Int.negOfNat 173372893788627698255), (Int.negOfNat 60443936852758301567), (Int.ofNat 931586125385459640), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(5423841039203037293941036948691911/28147497671065600000000000000000000), (3147348875101695523418552412486891/56294995342131200000000000000000000), (32213645550674210609796466173721/56294995342131200000000000000000000), (-10265880237410275255480289287387/14073748835532800000000000000000000), (474425719724078231205391359861/28147497671065600000000000000000000), (405018657530568393290411493507/14073748835532800000000000000000000), (-43778124265828979118811383491/56294995342131200000000000000000000), (-99644176963820602626002519/175921860444160000000000000000000), (75395596990443749151530551/5629499534213120000000000000000000), (185998318039176128138463981/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial168.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial168.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial168.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 17003237711876850218730612738066996), (Int.ofNat 2922282640104554897248050809030163), (Int.negOfNat 90814661796811219346970051888079), (Int.ofNat 9600408890891401173714136447579), (Int.ofNat 7734256897173690839296395766577), (Int.negOfNat 628319902003974932918671692196), (Int.negOfNat 216074007891160501960965614760), (Int.ofNat 14492236599830396181431849495), (Int.ofNat 3301408784646002447051342716), (Int.negOfNat 175572161201979710712833229), (Int.negOfNat 31524342937467768843744949), (Int.ofNat 1311113448472302349974045), (Int.ofNat 203812388573075837827594), (Int.negOfNat 6640457354140311184280), (Int.negOfNat 943268370384773026918), (Int.ofNat 23912662326262542820), (Int.ofNat 2834482671195605500), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(4250809427969212554682653184516749/14073748835532800000000000000000000), (2922282640104554897248050809030163/56294995342131200000000000000000000), (-90814661796811219346970051888079/56294995342131200000000000000000000), (9600408890891401173714136447579/56294995342131200000000000000000000), (7734256897173690839296395766577/56294995342131200000000000000000000), (-157079975500993733229667923049/14073748835532800000000000000000000), (-5401850197279012549024140369/1407374883553280000000000000000000), (2898447319966079236286369899/11258999068426240000000000000000000), (825352196161500611762835679/14073748835532800000000000000000000), (-175572161201979710712833229/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial168.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial168.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial168.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 22653742197228048520653130040733275), (Int.ofNat 2839299883647187093342077498530639), (Int.ofNat 64818624220049414959082006399926), (Int.ofNat 24449265220031715423784534614163), (Int.negOfNat 4811670084742520287140042038503), (Int.negOfNat 1076618064636217836155273957342), (Int.ofNat 162008628795939775344092678627), (Int.ofNat 22771061116369382981759044029), (Int.negOfNat 2613494242910260590930196882), (Int.negOfNat 283325480497653496324364191), (Int.ofNat 24583719838669758583285431), (Int.ofNat 2286937892007123557611713), (Int.negOfNat 150880797056136727879391), (Int.negOfNat 12762923960205963115673), (Int.ofNat 651975245084671443462), (Int.ofNat 51997034921854621337), (Int.negOfNat 2549751476847749490), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(906149687889121940826125201629331/2251799813685248000000000000000000), (2839299883647187093342077498530639/56294995342131200000000000000000000), (32409312110024707479541003199963/28147497671065600000000000000000000), (24449265220031715423784534614163/56294995342131200000000000000000000), (-4811670084742520287140042038503/56294995342131200000000000000000000), (-538309032318108918077636978671/28147497671065600000000000000000000), (162008628795939775344092678627/56294995342131200000000000000000000), (22771061116369382981759044029/56294995342131200000000000000000000), (-1306747121455130295465098441/28147497671065600000000000000000000), (-283325480497653496324364191/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial168.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial168.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial168.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 28688270361657850629312353282421605), (Int.ofNat 3189988094624453913577861250053761), (Int.ofNat 58435618155794266138673139330460), (Int.negOfNat 24188138401926376387822260666656), (Int.negOfNat 3146909792966466469375223939272), (Int.ofNat 1285392593332344448261764068250), (Int.ofNat 102996003847724289941304215866), (Int.negOfNat 29037292758108754962600989209), (Int.negOfNat 1830797229101393562448640109), (Int.ofNat 354366905929111437125220535), (Int.ofNat 19882343366846430608483599), (Int.negOfNat 2678553644493197213796899), (Int.negOfNat 141269407596308441632036), (Int.ofNat 13741651458752151228530), (Int.ofNat 697982691568254918415), (Int.negOfNat 51048877493005999721), (Int.negOfNat 2291947227754203655), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(5737654072331570125862470656484321/11258999068426240000000000000000000), (3189988094624453913577861250053761/56294995342131200000000000000000000), (2921780907789713306933656966523/2814749767106560000000000000000000), (-755879325060199262119445645833/1759218604441600000000000000000000), (-393363724120808308671902992409/7036874417766400000000000000000000), (5141570373329377793047056273/225179981368524800000000000000000), (51498001923862144970652107933/28147497671065600000000000000000000), (-29037292758108754962600989209/56294995342131200000000000000000000), (-1830797229101393562448640109/56294995342131200000000000000000000), (70873381185822287425044107/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial168.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial168.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial168.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 35101868062528642554875484672155038), (Int.ofNat 3141380403592245990397938884948381), (Int.negOfNat 55683049769761486565160943776487), (Int.ofNat 1075828764560852723590061169298), (Int.ofNat 7276410418225429136214565379178), (Int.ofNat 48295404948051995998142677243), (Int.negOfNat 248183339496457384510555836350), (Int.negOfNat 4217636239469912645700674069), (Int.ofNat 4123598531650378593082150861), (Int.ofNat 96913134980076594969608189), (Int.negOfNat 39525860570944784755501002), (Int.negOfNat 1086180966037907629614082), (Int.ofNat 244578063204962928411535), (Int.ofNat 7240229620722196631189), (Int.negOfNat 1062212900608491887977), (Int.negOfNat 33124054276829943337), (Int.ofNat 4167916828310039340), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(17550934031264321277437742336077519/28147497671065600000000000000000000), (3141380403592245990397938884948381/56294995342131200000000000000000000), (-55683049769761486565160943776487/56294995342131200000000000000000000), (537914382280426361795030584649/28147497671065600000000000000000000), (3638205209112714568107282689589/28147497671065600000000000000000000), (48295404948051995998142677243/56294995342131200000000000000000000), (-4963666789929147690211116727/1125899906842624000000000000000000), (-4217636239469912645700674069/56294995342131200000000000000000000), (4123598531650378593082150861/56294995342131200000000000000000000), (96913134980076594969608189/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial168.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial168.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial168.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 41273111333819717651361219581897131), (Int.ofNat 3122963726915402928726064301396818), (Int.ofNat 74238560347715849205497544157473), (Int.ofNat 26434046449120228974722771117372), (Int.negOfNat 3848008210238799858851736599198), (Int.negOfNat 1566267182921267389730432366782), (Int.ofNat 86056608103987777257110027414), (Int.ofNat 38530389220660006458490216440), (Int.negOfNat 663985207310029894833358373), (Int.negOfNat 492325008698001636720623326), (Int.negOfNat 513336080971820863644117), (Int.ofNat 3764011112001626791006287), (Int.ofNat 37532450682961084294048), (Int.negOfNat 19341371832943690005185), (Int.negOfNat 284012166343776543628), (Int.ofNat 73071755497572062622), (Int.ofNat 1210023333825371860), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(41273111333819717651361219581897131/56294995342131200000000000000000000), (1561481863457701464363032150698409/28147497671065600000000000000000000), (74238560347715849205497544157473/56294995342131200000000000000000000), (6608511612280057243680692779343/14073748835532800000000000000000000), (-1924004105119399929425868299599/28147497671065600000000000000000000), (-783133591460633694865216183391/28147497671065600000000000000000000), (43028304051993888628555013707/28147497671065600000000000000000000), (963259730516500161462255411/1407374883553280000000000000000000), (-663985207310029894833358373/56294995342131200000000000000000000), (-246162504349000818360311663/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial168.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial168.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial168.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 47925801357616275653660620414290784), (Int.ofNat 3520698781352160033838527766805284), (Int.ofNat 58376265199297970590810159853907), (Int.negOfNat 35341635635976355195955208796040), (Int.negOfNat 6137808166723665148595605834744), (Int.ofNat 1517496476342261613038895704229), (Int.ofNat 272138808475784146135105658274), (Int.negOfNat 24782384202134484263300962930), (Int.negOfNat 5142553854471749759700604733), (Int.ofNat 175760879192477429278694996), (Int.ofNat 50457754926860384057232203), (Int.negOfNat 613532131463448193081687), (Int.negOfNat 311804104190487413736732), (Int.ofNat 538960984272830194845), (Int.ofNat 1346415489748890837572), (Int.ofNat 5622540883334404398), (Int.negOfNat 4885003433657298010), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(1497681292425508614176894387946587/1759218604441600000000000000000000), (880174695338040008459631941701321/14073748835532800000000000000000000), (58376265199297970590810159853907/56294995342131200000000000000000000), (-883540890899408879898880219901/1407374883553280000000000000000000), (-767226020840458143574450729343/7036874417766400000000000000000000), (1517496476342261613038895704229/56294995342131200000000000000000000), (136069404237892073067552829137/28147497671065600000000000000000000), (-2478238420213448426330096293/5629499534213120000000000000000000), (-5142553854471749759700604733/56294995342131200000000000000000000), (43940219798119357319673749/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial168.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial168.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial168.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 54881393248385927427324733582133276), (Int.ofNat 3291625144453742907859997757548534), (Int.negOfNat 138783717501508430620859996357422), (Int.negOfNat 1635587488065832143277924800915), (Int.ofNat 13989711217789843671110854453431), (Int.ofNat 1110589544105461685935367157351), (Int.negOfNat 389507636266559013114409728440), (Int.negOfNat 43821147529711278293310941041), (Int.ofNat 4095683022525414399751708601), (Int.ofNat 589120236369223638445926041), (Int.negOfNat 24204491889922904669417982), (Int.negOfNat 4475842807722157452108418), (Int.ofNat 92046315662034314637955), (Int.ofNat 22746645625505083284751), (Int.negOfNat 234132363284162152877), (Int.negOfNat 85728449731268156283), (Int.ofNat 230443862777089270), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(13720348312096481856831183395533319/14073748835532800000000000000000000), (1645812572226871453929998878774267/28147497671065600000000000000000000), (-69391858750754215310429998178711/28147497671065600000000000000000000), (-327117497613166428655584960183/11258999068426240000000000000000000), (13989711217789843671110854453431/56294995342131200000000000000000000), (1110589544105461685935367157351/56294995342131200000000000000000000), (-9737690906663975327860243211/1407374883553280000000000000000000), (-43821147529711278293310941041/56294995342131200000000000000000000), (4095683022525414399751708601/56294995342131200000000000000000000), (589120236369223638445926041/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial168.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial168.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial168.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 61126577345925153916087902039030786), (Int.ofNat 3164344202236921239984889690444590), (Int.ofNat 162732296392849332054917405818479), (Int.ofNat 77807053730125639382194051690274), (Int.negOfNat 4077122752978967490240314411336), (Int.negOfNat 4533139508029628707151180632397), (Int.negOfNat 285845498502788474890730812944), (Int.ofNat 64269570590570062254957045699), (Int.ofNat 5990111686228507727712252451), (Int.negOfNat 497532712577132925290353105), (Int.negOfNat 57432462022868457561117221), (Int.ofNat 2537386521708887813856999), (Int.ofNat 346283353085848428773044), (Int.negOfNat 9317050835815545141490), (Int.negOfNat 1475940108032451068785), (Int.ofNat 25458111550989484101), (Int.ofNat 4881856440703326115), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(30563288672962576958043951019515393/28147497671065600000000000000000000), (316434420223692123998488969044459/5629499534213120000000000000000000), (162732296392849332054917405818479/56294995342131200000000000000000000), (38903526865062819691097025845137/28147497671065600000000000000000000), (-509640344122370936280039301417/7036874417766400000000000000000000), (-4533139508029628707151180632397/56294995342131200000000000000000000), (-17865343656424279680670675809/3518437208883200000000000000000000), (64269570590570062254957045699/56294995342131200000000000000000000), (5990111686228507727712252451/56294995342131200000000000000000000), (-99506542515426585058070621/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial168.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial168.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial168.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 68509515767263317417141532481712601), (Int.ofNat 4234479315565048651986147051169228), (Int.ofNat 151531620965680525085800715129371), (Int.negOfNat 138560020674188127450254481723136), (Int.negOfNat 44486542091776273730423981575687), (Int.negOfNat 1241563104272683123733266812493), (Int.ofNat 812419893888948509126264824052), (Int.ofNat 53902911471839009672454746981), (Int.negOfNat 7842684938069373153513195522), (Int.negOfNat 664922723680176655505108139), (Int.ofNat 49530932730493605275289311), (Int.ofNat 4785916891802794758229387), (Int.negOfNat 224571330572971921298711), (Int.negOfNat 23561879238190169609567), (Int.ofNat 772644628369141842162), (Int.ofNat 86516915594912772783), (Int.negOfNat 1848609214239379120), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(68509515767263317417141532481712601/56294995342131200000000000000000000), (1058619828891262162996536762792307/14073748835532800000000000000000000), (151531620965680525085800715129371/56294995342131200000000000000000000), (-541250080758547372852556569231/219902325555200000000000000000000), (-44486542091776273730423981575687/56294995342131200000000000000000000), (-1241563104272683123733266812493/56294995342131200000000000000000000), (203104973472237127281566206013/14073748835532800000000000000000000), (53902911471839009672454746981/56294995342131200000000000000000000), (-3921342469034686576756597761/28147497671065600000000000000000000), (-664922723680176655505108139/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial168.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial168.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial168.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 75781211725829106569515566597015548), (Int.ofNat 1825862230264024929892440738914686), (Int.negOfNat 1632058302945219748000694053056614), (Int.negOfNat 400639304692969864620227443243606), (Int.negOfNat 3697159127925058467308812928330), (Int.ofNat 8692741947442986152518639670858), (Int.ofNat 461365511471799494614278031715), (Int.negOfNat 102325160602110720367553477485), (Int.negOfNat 7117977631730328387149798044), (Int.ofNat 786293006697121677050378299), (Int.ofNat 60620919927940874534369171), (Int.negOfNat 4292009636150421162985545), (Int.negOfNat 344566010519002924098186), (Int.ofNat 17550364952671866272740), (Int.ofNat 1420104717910457296582), (Int.negOfNat 54418295234938742000), (Int.negOfNat 4339320997261924270), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(18945302931457276642378891649253887/14073748835532800000000000000000000), (912931115132012464946220369457343/28147497671065600000000000000000000), (-816029151472609874000347026528307/28147497671065600000000000000000000), (-200319652346484932310113721621803/28147497671065600000000000000000000), (-369715912792505846730881292833/5629499534213120000000000000000000), (4346370973721493076259319835429/28147497671065600000000000000000000), (92273102294359898922855606343/11258999068426240000000000000000000), (-20465032120422144073510695497/11258999068426240000000000000000000), (-1779494407932582096787449511/14073748835532800000000000000000000), (786293006697121677050378299/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial168.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial168.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial168.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 69933663924613222885551243566448438), (Int.negOfNat 8895414410516024464870839317402575), (Int.negOfNat 3395816077673152640000575787009605), (Int.negOfNat 73801706062324582612887952601195), (Int.ofNat 78056825868836085583398250121055), (Int.ofNat 4364167896190960520434468254407), (Int.negOfNat 1115383286987458949757046297381), (Int.negOfNat 73748481703422597872923370530), (Int.ofNat 10489850953565674275298324050), (Int.ofNat 716486071530798598281315168), (Int.negOfNat 69061162884506083316731410), (Int.negOfNat 4642909305787604805056879), (Int.ofNat 334380825436119438530364), (Int.ofNat 21631257692089953958064), (Int.negOfNat 1235313130386764086255), (Int.negOfNat 76155922153181189053), (Int.ofNat 3466774565701668970), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(34966831962306611442775621783224219/28147497671065600000000000000000000), (-355816576420640978594833572696103/2251799813685248000000000000000000), (-679163215534630528000115157401921/11258999068426240000000000000000000), (-14760341212464916522577590520239/11258999068426240000000000000000000), (15611365173767217116679650024211/11258999068426240000000000000000000), (4364167896190960520434468254407/56294995342131200000000000000000000), (-1115383286987458949757046297381/56294995342131200000000000000000000), (-7374848170342259787292337053/5629499534213120000000000000000000), (209797019071313485505966481/1125899906842624000000000000000000), (22390189735337456196291099/1759218604441600000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial168.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial168.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial168.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 39279868934723473905916509012408005), (Int.negOfNat 20752544533553166090755569897151744), (Int.negOfNat 1912181441687280248627997707952675), (Int.ofNat 526894843151073139012468301145455), (Int.ofNat 47687982491205563934754130210484), (Int.negOfNat 9726043797201260472517031090759), (Int.negOfNat 768791801967151315354948553552), (Int.ofNat 116656496928491024260918005006), (Int.ofNat 8079947451897203290266520841), (Int.negOfNat 947434170790188843389142732), (Int.negOfNat 58293384583703789637828762), (Int.ofNat 5496434263084826721242637), (Int.ofNat 303608257711303452559317), (Int.negOfNat 23780523127070748635145), (Int.negOfNat 1191344873250165628520), (Int.ofNat 78682799061637127699), (Int.ofNat 3796785553820522425), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(7855973786944694781183301802481601/11258999068426240000000000000000000), (-81064627084192055042013944910749/219902325555200000000000000000000), (-76487257667491209945119908318107/2251799813685248000000000000000000), (105378968630214627802493660229091/11258999068426240000000000000000000), (11921995622801390983688532552621/14073748835532800000000000000000000), (-9726043797201260472517031090759/56294995342131200000000000000000000), (-48049487622946957209684284597/3518437208883200000000000000000000), (58328248464245512130459002503/28147497671065600000000000000000000), (8079947451897203290266520841/56294995342131200000000000000000000), (-236858542697547210847285683/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial168.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial168.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial168.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 5239747502648368894878153121077632), (Int.negOfNat 21420085654238605410517311387058525), (Int.ofNat 1519111907266184436531155827075983), (Int.ofNat 470427053528061403360608449225200), (Int.negOfNat 58329158425190501480823978943943), (Int.negOfNat 7728174621478093115216142336747), (Int.ofNat 1030114747384853390129754911281), (Int.ofNat 87272474779415805578213883088), (Int.negOfNat 10940384619940204301577758474), (Int.negOfNat 688726998355448860164548935), (Int.ofNat 78209851499132455351974525), (Int.ofNat 3947912121628586310115792), (Int.negOfNat 401892966029264095614559), (Int.negOfNat 17019635447916895549081), (Int.ofNat 1556186125333891543957), (Int.ofNat 56099989108117707437), (Int.negOfNat 4904094769350158205), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-40935527364440381991235571258419/439804651110400000000000000000000), (-856803426169544216420692455482341/2251799813685248000000000000000000), (1519111907266184436531155827075983/56294995342131200000000000000000000), (1176067633820153508401521123063/140737488355328000000000000000000), (-58329158425190501480823978943943/56294995342131200000000000000000000), (-7728174621478093115216142336747/56294995342131200000000000000000000), (1030114747384853390129754911281/56294995342131200000000000000000000), (5454529673713487848638367693/3518437208883200000000000000000000), (-5470192309970102150788879237/28147497671065600000000000000000000), (-137745399671089772032909787/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial168.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial168.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial168.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial168.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial168.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial168.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial168.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial168.reflect := by
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

end Bin168
end
end ErdosOverlap.OuterNumerics
