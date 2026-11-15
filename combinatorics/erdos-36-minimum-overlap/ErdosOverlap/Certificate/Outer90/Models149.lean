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

/-! # Exact integer weighted outer models for source bin 149

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin149

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 2468065356576409000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 2438707485128515700)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 2163575028310898400)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 1475908740841410400)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 951437044525920400)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 543409172654868700)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 324723423536473100)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 494221844946857240)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 170840930525095500)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial149.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial149.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9628205614658065000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 2256479400083964700)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1468687551159670000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 926893114586169700)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 298680825303526200)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 50510677371913950)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 117071859446180060)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 103786021078765940)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 3442862260758243)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial149.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial149.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9628205614658065000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 2256479400083964700)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1468687551159670000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 926893114586169700)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 298680825303526200)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 50510677371913950)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 117071859446180060)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 103786021078765940)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 3442862260758243)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial149.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial149.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial149.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 8601792612284908850257721245582489), (Int.ofNat 4876334394895017707842455454983481), (Int.ofNat 927431427865178097046266701982700), (Int.negOfNat 161021446849644369686698157084797), (Int.negOfNat 27186805986270964520687561544661), (Int.ofNat 3279976762530679675280908942397), (Int.ofNat 427739059916766472441770541317), (Int.negOfNat 40746967357828841733580291247), (Int.negOfNat 4194890923719804211669471752), (Int.ofNat 333559485355776807832355416), (Int.ofNat 27912040555381090035902987), (Int.negOfNat 1923774012069212423818072), (Int.negOfNat 133969120678381260070211), (Int.ofNat 8228458969859885576731), (Int.ofNat 485265042296850493625), (Int.negOfNat 26926929007011833375), (Int.negOfNat 1431555345086551222), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-8601792612284908850257721245582489/11258999068426240000000000000000000), (4876334394895017707842455454983481/11258999068426240000000000000000000), (9274314278651780970462667019827/112589990684262400000000000000000), (-161021446849644369686698157084797/11258999068426240000000000000000000), (-27186805986270964520687561544661/11258999068426240000000000000000000), (3279976762530679675280908942397/11258999068426240000000000000000000), (427739059916766472441770541317/11258999068426240000000000000000000), (-40746967357828841733580291247/11258999068426240000000000000000000), (-524361365464975526458683969/1407374883553280000000000000000000), (41694935669472100979044427/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial149.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial149.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial149.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial149 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 3263681420883904542358638476145513), (Int.ofNat 6106685738883170937102446422836002), (Int.negOfNat 359227457081961856109007458653087), (Int.negOfNat 207085810626065483007599613084983), (Int.ofNat 16795115172453049034355797832435), (Int.ofNat 3940979627035496477157801735150), (Int.negOfNat 328871252330827711619915573943), (Int.negOfNat 45524009989966421161383919271), (Int.ofNat 3639291896282852881055724931), (Int.ofNat 347835622953155073210667511), (Int.negOfNat 26281429230211327110358402), (Int.negOfNat 1876652454196824837261775), (Int.ofNat 134571647984429853699095), (Int.ofNat 7520805882664644076417), (Int.negOfNat 516443762870092972968), (Int.negOfNat 23058176646661548003), (Int.ofNat 1600093786586792772), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(3263681420883904542358638476145513/11258999068426240000000000000000000), (3053342869441585468551223211418001/5629499534213120000000000000000000), (-359227457081961856109007458653087/11258999068426240000000000000000000), (-207085810626065483007599613084983/11258999068426240000000000000000000), (3359023034490609806871159566487/2251799813685248000000000000000000), (78819592540709929543156034703/225179981368524800000000000000000), (-328871252330827711619915573943/11258999068426240000000000000000000), (-45524009989966421161383919271/11258999068426240000000000000000000), (3639291896282852881055724931/11258999068426240000000000000000000), (347835622953155073210667511/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial149.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial149.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial149.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial149 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 12752494541423597109896651990044402), (Int.ofNat 2958306194176575241800348703183725), (Int.negOfNat 985123505395726759536188330691872), (Int.ofNat 14727013339972293898669616107121), (Int.ofNat 28791126447621190460720704581130), (Int.negOfNat 1749740079104669343208844775788), (Int.negOfNat 431743534420553093695225443574), (Int.ofNat 31635645239699054602477492207), (Int.ofNat 3955348205012007633861199888), (Int.negOfNat 305761748231696373281894703), (Int.negOfNat 24445451802059207048286862), (Int.ofNat 1932919657091467562568403), (Int.ofNat 108890123450078410193820), (Int.negOfNat 8755920507079956877240), (Int.negOfNat 366565404429321418445), (Int.ofNat 29963796445862706857), (Int.ofNat 915589691250506479), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(6376247270711798554948325995022201/5629499534213120000000000000000000), (118332247767063009672013948127349/450359962737049600000000000000000), (-30785109543616461235505885334121/351843720888320000000000000000000), (14727013339972293898669616107121/11258999068426240000000000000000000), (2879112644762119046072070458113/1125899906842624000000000000000000), (-437435019776167335802211193947/2814749767106560000000000000000000), (-215871767210276546847612721787/5629499534213120000000000000000000), (31635645239699054602477492207/11258999068426240000000000000000000), (247209262813250477116324993/703687441776640000000000000000000), (-305761748231696373281894703/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial149.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial149.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial149.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial149 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 15228348446849312746312799451027029), (Int.negOfNat 89604228097917117260867225394784), (Int.negOfNat 422655187163394816332833054498444), (Int.ofNat 128863277898509837975286206550192), (Int.negOfNat 2792340808821040395225321286311), (Int.negOfNat 3249786755705951719758796697330), (Int.ofNat 199438918370492858455809807263), (Int.ofNat 39320040737081458750119982028), (Int.negOfNat 2938959169531337733723421138), (Int.negOfNat 290960233691965523614972794), (Int.ofNat 24080844824897169325857129), (Int.ofNat 1468103588598030513564433), (Int.negOfNat 132094611754177421222162), (Int.negOfNat 5399251564165931617796), (Int.ofNat 527717093712911661402), (Int.ofNat 14581559045941579418), (Int.negOfNat 1589765199804518043), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(15228348446849312746312799451027029/11258999068426240000000000000000000), (-2800132128059909914402100793587/351843720888320000000000000000000), (-105663796790848704083208263624611/2814749767106560000000000000000000), (8053954868656864873455387909387/703687441776640000000000000000000), (-2792340808821040395225321286311/11258999068426240000000000000000000), (-324978675570595171975879669733/1125899906842624000000000000000000), (199438918370492858455809807263/11258999068426240000000000000000000), (9830010184270364687529995507/2814749767106560000000000000000000), (-1469479584765668866861710569/5629499534213120000000000000000000), (-145480116845982761807486397/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial149.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial149.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial149.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial149 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 14257677636082211545891803222097579), (Int.negOfNat 530839344066024566688346448017378), (Int.ofNat 91515578382062350145027085803077), (Int.ofNat 24047562390869722662274847220256), (Int.negOfNat 16411532775584304277886094410134), (Int.ofNat 766133862720206534530176600635), (Int.ofNat 319280474087837803796486018664), (Int.negOfNat 22426050893708368915914625042), (Int.negOfNat 3063929318963975864557969264), (Int.ofNat 255594360675390257931963768), (Int.ofNat 18199045660611686121582301), (Int.negOfNat 1754334078686151602414755), (Int.negOfNat 74065928509340254141911), (Int.ofNat 8329431264605107468435), (Int.ofNat 218645725433120014074), (Int.negOfNat 29770839664737413921), (Int.negOfNat 403066899675219979), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(14257677636082211545891803222097579/11258999068426240000000000000000000), (-265419672033012283344173224008689/5629499534213120000000000000000000), (91515578382062350145027085803077/11258999068426240000000000000000000), (751486324714678833196088975633/351843720888320000000000000000000), (-8205766387792152138943047205067/5629499534213120000000000000000000), (153226772544041306906035320127/2251799813685248000000000000000000), (39910059260979725474560752333/1407374883553280000000000000000000), (-11213025446854184457957312521/5629499534213120000000000000000000), (-191495582435248491534873079/703687441776640000000000000000000), (31949295084423782241495471/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial149.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial149.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial149.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial149 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 13533298244439529221455973547206653), (Int.negOfNat 291306156388953544735590052317300), (Int.negOfNat 39384268351928539073380494487976), (Int.negOfNat 41989906246383107456235680973677), (Int.ofNat 1890591333685032493092592021327), (Int.ofNat 1946601470732525343323386926095), (Int.negOfNat 133331670045532720058206703707), (Int.negOfNat 27351011196637426727616903786), (Int.ofNat 2270574758113916582552172145), (Int.ofNat 202955270413031073750264738), (Int.negOfNat 20257970658359968102523945), (Int.negOfNat 941646737487024469378991), (Int.ofNat 116870707113015733472656), (Int.ofNat 2930358157147128909558), (Int.negOfNat 481595656750536523091), (Int.negOfNat 6156840252923057793), (Int.ofNat 1579436613022243314), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(13533298244439529221455973547206653/11258999068426240000000000000000000), (-2913061563889535447355900523173/112589990684262400000000000000000), (-4923033543991067384172561810997/1407374883553280000000000000000000), (-41989906246383107456235680973677/11258999068426240000000000000000000), (1890591333685032493092592021327/11258999068426240000000000000000000), (389320294146505068664677385219/2251799813685248000000000000000000), (-133331670045532720058206703707/11258999068426240000000000000000000), (-13675505598318713363808451893/5629499534213120000000000000000000), (454114951622783316510434429/2251799813685248000000000000000000), (101477635206515536875132369/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial149.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial149.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial149.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial149 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 12538399162670937035140259378249194), (Int.negOfNat 771666675779646601457388410334685), (Int.negOfNat 135848492296867349761078789415424), (Int.ofNat 19171928769886912082140446627258), (Int.ofNat 8763122934925493645232973092446), (Int.negOfNat 703376718046212095138118317150), (Int.negOfNat 200362320863819670649788888101), (Int.ofNat 16855072081749691407750511508), (Int.ofNat 1987939360646213556656996343), (Int.negOfNat 200811464436174693062703670), (Int.negOfNat 10970600249624392444550610), (Int.ofNat 1442325574438095527251452), (Int.ofNat 36446418996620262866705), (Int.negOfNat 7062240921785169418867), (Int.negOfNat 65671185072916908561), (Int.ofNat 25843226574095254371), (Int.negOfNat 109455891900066521), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(6269199581335468517570129689124597/5629499534213120000000000000000000), (-154333335155929320291477682066937/2251799813685248000000000000000000), (-265329086517319042502107010577/21990232555520000000000000000000), (9585964384943456041070223313629/5629499534213120000000000000000000), (4381561467462746822616486546223/5629499534213120000000000000000000), (-14067534360924241902762366343/225179981368524800000000000000000), (-200362320863819670649788888101/11258999068426240000000000000000000), (4213768020437422851937627877/2814749767106560000000000000000000), (1987939360646213556656996343/11258999068426240000000000000000000), (-20081146443617469306270367/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial149.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial149.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial149.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial149 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 10712481352912306460846151102894164), (Int.negOfNat 890232621212426726244489162711247), (Int.ofNat 99020159190108565990337809521969), (Int.ofNat 40899986849772483785187327461161), (Int.negOfNat 4240629529216318877956340604684), (Int.negOfNat 1250581733712271839329575689194), (Int.ofNat 108390966220516099986156487391), (Int.ofNat 16988278185747939052086821239), (Int.negOfNat 1692422384480240064507162455), (Int.negOfNat 116106162553988608276290975), (Int.ofNat 15433509583143815621718401), (Int.ofNat 423002875631035323633567), (Int.negOfNat 91482778030591691564824), (Int.negOfNat 577803879090715053887), (Int.ofNat 382753293089726169656), (Int.negOfNat 2366831731457540872), (Int.negOfNat 1398267095714873085), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(2678120338228076615211537775723541/2814749767106560000000000000000000), (-890232621212426726244489162711247/11258999068426240000000000000000000), (99020159190108565990337809521969/11258999068426240000000000000000000), (40899986849772483785187327461161/11258999068426240000000000000000000), (-1060157382304079719489085151171/2814749767106560000000000000000000), (-625290866856135919664787844597/5629499534213120000000000000000000), (108390966220516099986156487391/11258999068426240000000000000000000), (16988278185747939052086821239/11258999068426240000000000000000000), (-338484476896048012901432491/2251799813685248000000000000000000), (-4644246502159544331051639/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial149.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial149.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial149.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial149 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 9556063065974448351389987206459887), (Int.negOfNat 212596012778870405806669548826939), (Int.ofNat 176644119226848572563741378330618), (Int.negOfNat 19604606694774712918970292029367), (Int.negOfNat 7636055464051377961506014366865), (Int.ofNat 612725283385488840511134859277), (Int.ofNat 131505986734637675033137812931), (Int.negOfNat 11983587502673188652006620399), (Int.negOfNat 1125907993604171251552731895), (Int.ofNat 140314872946998380525689755), (Int.ofNat 4660150686151893938915981), (Int.negOfNat 1027291521180287623974467), (Int.negOfNat 3615310675278946559444), (Int.ofNat 5120905931117555884827), (Int.negOfNat 63694028456162281844), (Int.negOfNat 18908273127913397548), (Int.ofNat 444252028428741035), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(9556063065974448351389987206459887/11258999068426240000000000000000000), (-212596012778870405806669548826939/11258999068426240000000000000000000), (88322059613424286281870689165309/5629499534213120000000000000000000), (-19604606694774712918970292029367/11258999068426240000000000000000000), (-1527211092810275592301202873373/2251799813685248000000000000000000), (612725283385488840511134859277/11258999068426240000000000000000000), (131505986734637675033137812931/11258999068426240000000000000000000), (-11983587502673188652006620399/11258999068426240000000000000000000), (-225181598720834250310546379/2251799813685248000000000000000000), (28062974589399676105137951/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial149.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial149.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial149.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial149 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 9584709771759027915737538912258616), (Int.ofNat 82452750375618295861839534792949), (Int.negOfNat 53068128038097576038669665605911), (Int.negOfNat 43087984349857074492977748905760), (Int.ofNat 2351427991748129350935081646602), (Int.ofNat 971051782460610163885414017760), (Int.negOfNat 66784472591919335564032453561), (Int.negOfNat 10327482703205353467837979548), (Int.ofNat 1039253338832936143180510903), (Int.ofNat 50593630286599370561834290), (Int.negOfNat 9663522408213974767971630), (Int.negOfNat 17211138921727883005552), (Int.ofNat 58436198040902751613485), (Int.negOfNat 1242391127418592652773), (Int.negOfNat 248107311029743283561), (Int.ofNat 8460603329828388549), (Int.ofNat 1049699510143165599), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(1198088721469878489467192364032327/1407374883553280000000000000000000), (82452750375618295861839534792949/11258999068426240000000000000000000), (-53068128038097576038669665605911/11258999068426240000000000000000000), (-269299902186606715581110930661/70368744177664000000000000000000), (1175713995874064675467540823301/5629499534213120000000000000000000), (6069073640378813524283837611/70368744177664000000000000000000), (-66784472591919335564032453561/11258999068426240000000000000000000), (-2581870675801338366959494887/2814749767106560000000000000000000), (1039253338832936143180510903/11258999068426240000000000000000000), (5059363028659937056183429/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial149.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial149.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial149.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial149 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 9256021513971636782573307300919863), (Int.negOfNat 510262630603379269065697150259770), (Int.negOfNat 198458625456961221142657745252379), (Int.ofNat 87831990835452502564795658342), (Int.ofNat 6407259430881104419202171599055), (Int.negOfNat 203431395505429084097278400455), (Int.negOfNat 90678755050754336311619653747), (Int.ofNat 5471431627315203355204249646), (Int.ofNat 560765433265081184321855185), (Int.negOfNat 70130036148891559785332518), (Int.negOfNat 321266169335149832313825), (Int.ofNat 536367700765539867596691), (Int.negOfNat 18837247384559736197824), (Int.negOfNat 2728896671602597048498), (Int.ofNat 150197167683842731009), (Int.ofNat 9653590888066053513), (Int.negOfNat 604764372171561806), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(9256021513971636782573307300919863/11258999068426240000000000000000000), (-51026263060337926906569715025977/1125899906842624000000000000000000), (-198458625456961221142657745252379/11258999068426240000000000000000000), (43915995417726251282397829171/5629499534213120000000000000000000), (1281451886176220883840434319811/2251799813685248000000000000000000), (-40686279101085816819455680091/2251799813685248000000000000000000), (-90678755050754336311619653747/11258999068426240000000000000000000), (2735715813657601677602124823/5629499534213120000000000000000000), (112153086653016236864371037/2251799813685248000000000000000000), (-35065018074445779892666259/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial149.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial149.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial149.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial149 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 7533375978125051602103240204458184), (Int.negOfNat 1128828026037981307228941749069438), (Int.negOfNat 77826528470085719763576262566245), (Int.ofNat 32406852391677427553382074167430), (Int.ofNat 824642067412700612214154755083), (Int.negOfNat 711498156480200253858431393312), (Int.ofNat 6870943236372916823523909324), (Int.ofNat 6169222520410887082811136082), (Int.negOfNat 278476971838078950284161424), (Int.negOfNat 11247886812836197313692388), (Int.ofNat 3230247225378498590255721), (Int.negOfNat 219421649469195952105245), (Int.negOfNat 21133929623661004076491), (Int.ofNat 2250826553711733044005), (Int.ofNat 91392295642664674874), (Int.negOfNat 11719206770858250699), (Int.negOfNat 537176718567879099), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(941671997265631450262905025557273/1407374883553280000000000000000000), (-564414013018990653614470874534719/5629499534213120000000000000000000), (-15565305694017143952715252513249/2251799813685248000000000000000000), (3240685239167742755338207416743/1125899906842624000000000000000000), (824642067412700612214154755083/11258999068426240000000000000000000), (-22234317390006257933075981041/351843720888320000000000000000000), (1717735809093229205880977331/2814749767106560000000000000000000), (3084611260205443541405568041/5629499534213120000000000000000000), (-17404810739879934392760089/703687441776640000000000000000000), (-2811971703209049328423097/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial149.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial149.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial149.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial149 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 5215250106592696806964546496037437), (Int.negOfNat 1077997584949772951331886611388298), (Int.ofNat 84760014643349401206627818649453), (Int.ofNat 14577351813959221784828601644684), (Int.negOfNat 4475593827499769108325952751049), (Int.negOfNat 240048720598752689617044472470), (Int.ofNat 61385824089800592573122518060), (Int.ofNat 1768232510985171263984758312), (Int.negOfNat 256212488441283648348054778), (Int.negOfNat 4383946707370709709980726), (Int.negOfNat 1722713346512412134188691), (Int.negOfNat 19504437753532370951733), (Int.ofNat 28101079347285791720318), (Int.ofNat 186629992427936818636), (Int.negOfNat 179533395813348877998), (Int.negOfNat 310852906474643138), (Int.ofNat 594435785389287077), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(5215250106592696806964546496037437/11258999068426240000000000000000000), (-538998792474886475665943305694149/5629499534213120000000000000000000), (84760014643349401206627818649453/11258999068426240000000000000000000), (3644337953489805446207150411171/2814749767106560000000000000000000), (-4475593827499769108325952751049/11258999068426240000000000000000000), (-24004872059875268961704447247/1125899906842624000000000000000000), (3069291204490029628656125903/562949953421312000000000000000000), (221029063873146407998094789/1407374883553280000000000000000000), (-128106244220641824174027389/5629499534213120000000000000000000), (-2191973353685354854990363/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial149.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial149.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial149.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial149 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 3439708250693249620282356964493634), (Int.negOfNat 714154780506573985178974273527614), (Int.ofNat 61028959645880780156974340951302), (Int.negOfNat 20524303749838616198493871065450), (Int.negOfNat 3022989838103916030583460047566), (Int.ofNat 509752586019487626535432763965), (Int.ofNat 49990966133253087543469352166), (Int.negOfNat 4062624761291781327052885347), (Int.negOfNat 473537916712535313226319452), (Int.negOfNat 2253574060576347420859977), (Int.ofNat 3103473918989590898971918), (Int.ofNat 269951467480836901516897), (Int.negOfNat 15715230512865749345900), (Int.negOfNat 2336147809459859845200), (Int.ofNat 64328326883679454455), (Int.ofNat 11878829300401159463), (Int.ofNat 24653926992592599), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(1719854125346624810141178482246817/5629499534213120000000000000000000), (-357077390253286992589487136763807/5629499534213120000000000000000000), (30514479822940390078487170475651/5629499534213120000000000000000000), (-410486074996772323969877421309/225179981368524800000000000000000), (-1511494919051958015291730023783/5629499534213120000000000000000000), (101950517203897525307086552793/2251799813685248000000000000000000), (24995483066626543771734676083/5629499534213120000000000000000000), (-4062624761291781327052885347/11258999068426240000000000000000000), (-118384479178133828306579863/2814749767106560000000000000000000), (-2253574060576347420859977/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial149.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial149.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial149.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial149 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 2061825018659536574813557274017066), (Int.negOfNat 764979510331338117653225210725877), (Int.negOfNat 85437676510710855073817515020195), (Int.negOfNat 19398643453195221031341889392074), (Int.ofNat 3447373100583390577451209578013), (Int.ofNat 582439843181270025067606212590), (Int.negOfNat 48383716220860707287423857683), (Int.negOfNat 8168511787565474819140803669), (Int.ofNat 200947064210665107001404171), (Int.ofNat 72119270109624216586614409), (Int.ofNat 1494373212678140447427518), (Int.negOfNat 453245500654577149377025), (Int.negOfNat 23781499443175262909985), (Int.ofNat 2156848714544222676643), (Int.ofNat 151693104101990094032), (Int.negOfNat 8296622545314938277), (Int.negOfNat 584107198607012348), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(1030912509329768287406778637008533/5629499534213120000000000000000000), (-764979510331338117653225210725877/11258999068426240000000000000000000), (-17087535302142171014763503004039/2251799813685248000000000000000000), (-9699321726597610515670944696037/5629499534213120000000000000000000), (3447373100583390577451209578013/11258999068426240000000000000000000), (58243984318127002506760621259/1125899906842624000000000000000000), (-48383716220860707287423857683/11258999068426240000000000000000000), (-8168511787565474819140803669/11258999068426240000000000000000000), (200947064210665107001404171/11258999068426240000000000000000000), (72119270109624216586614409/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial149.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial149.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial149.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial149 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.ofNat 104668953537161804906413594771418), (Int.negOfNat 1195177953896539902122722775594190), (Int.negOfNat 88903066540405045539869614601484), (Int.ofNat 19911841743881359870580473141165), (Int.ofNat 4596255840511880841955737046018), (Int.negOfNat 451827511048294945460266891834), (Int.negOfNat 94292733479972912395137262723), (Int.ofNat 4158085083805697810557296387), (Int.ofNat 1091264783085321864831184388), (Int.negOfNat 8423483138468440150026136), (Int.negOfNat 8394654774691150281032993), (Int.negOfNat 144952018208286149295828), (Int.ofNat 46786491783603111258509), (Int.ofNat 1535901458182360717309), (Int.negOfNat 196516395934768975875), (Int.negOfNat 8434638828916414645), (Int.ofNat 484426002321935658), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(52334476768580902453206797385709/5629499534213120000000000000000000), (-119517795389653990212272277559419/1125899906842624000000000000000000), (-22225766635101261384967403650371/2814749767106560000000000000000000), (3982368348776271974116094628233/2251799813685248000000000000000000), (2298127920255940420977868523009/5629499534213120000000000000000000), (-225913755524147472730133445917/5629499534213120000000000000000000), (-94292733479972912395137262723/11258999068426240000000000000000000), (4158085083805697810557296387/11258999068426240000000000000000000), (272816195771330466207796097/2814749767106560000000000000000000), (-1052935392308555018753267/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial149.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial149.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial149.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial149 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 2428159014702803396603255964207524), (Int.negOfNat 1216100874536498112645518140100882), (Int.ofNat 86715171027645246234973613872533), (Int.ofNat 27631235691214441770355965372009), (Int.negOfNat 3339742757675393761413502572003), (Int.negOfNat 829109251216273667115935702337), (Int.ofNat 53069526752279036347152929563), (Int.ofNat 12839482241727171238106564147), (Int.negOfNat 371234454526627522260327628), (Int.negOfNat 122481787422981964297326716), (Int.ofNat 717925055290884964619273), (Int.ofNat 809867446365456583954372), (Int.ofNat 7517912708900468771371), (Int.negOfNat 3949073297732185568531), (Int.negOfNat 73185485932062433225), (Int.ofNat 15082429490305857975), (Int.ofNat 235539613035304862), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-607039753675700849150813991051881/2814749767106560000000000000000000), (-608050437268249056322759070050441/5629499534213120000000000000000000), (86715171027645246234973613872533/11258999068426240000000000000000000), (27631235691214441770355965372009/11258999068426240000000000000000000), (-3339742757675393761413502572003/11258999068426240000000000000000000), (-829109251216273667115935702337/11258999068426240000000000000000000), (53069526752279036347152929563/11258999068426240000000000000000000), (12839482241727171238106564147/11258999068426240000000000000000000), (-92808613631656880565081907/2814749767106560000000000000000000), (-30620446855745491074331679/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial149.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial149.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial149.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial149 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 4367533026045319427680571591789377), (Int.negOfNat 695574007437680322985639787973977), (Int.ofNat 126186128706839301619144665920179), (Int.negOfNat 17848655779652042473445479611623), (Int.negOfNat 5717904984432916319540555525544), (Int.ofNat 502174291956033766378723195980), (Int.ofNat 122882128894138824551027154243), (Int.negOfNat 6022142862879232952539150009), (Int.negOfNat 1482057199803376171259298131), (Int.ofNat 38370624657938745147560729), (Int.ofNat 11794449083909114783220602), (Int.negOfNat 120803592625407294433425), (Int.negOfNat 67201927831729476221495), (Int.negOfNat 16444163852106010297), (Int.ofNat 286969974503255136468), (Int.ofNat 2623031239695713843), (Int.negOfNat 819222138850610172), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-4367533026045319427680571591789377/11258999068426240000000000000000000), (-695574007437680322985639787973977/11258999068426240000000000000000000), (126186128706839301619144665920179/11258999068426240000000000000000000), (-17848655779652042473445479611623/11258999068426240000000000000000000), (-714738123054114539942569440693/1407374883553280000000000000000000), (25108714597801688318936159799/562949953421312000000000000000000), (122882128894138824551027154243/11258999068426240000000000000000000), (-6022142862879232952539150009/11258999068426240000000000000000000), (-1482057199803376171259298131/11258999068426240000000000000000000), (38370624657938745147560729/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial149.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial149.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial149.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial149 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 5465397254236092272702849080567937), (Int.negOfNat 528288742690497419896073705058679), (Int.negOfNat 54867753334289127954227144237617), (Int.negOfNat 29497050560794988245609038199942), (Int.ofNat 3630557349404020305693567468537), (Int.ofNat 969305525894207015376402841368), (Int.negOfNat 67549642411402170306514429406), (Int.negOfNat 15106097993332642568216502907), (Int.ofNat 692882162912069105485666292), (Int.ofNat 146847843087934365335217403), (Int.negOfNat 4339202028721496675663998), (Int.negOfNat 990290820258094150562703), (Int.ofNat 17381738843751417883720), (Int.ofNat 4898258887417620817440), (Int.negOfNat 44628211540775764055), (Int.negOfNat 18444020352693204557), (Int.ofNat 280426040800739881), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-5465397254236092272702849080567937/11258999068426240000000000000000000), (-528288742690497419896073705058679/11258999068426240000000000000000000), (-54867753334289127954227144237617/11258999068426240000000000000000000), (-14748525280397494122804519099971/5629499534213120000000000000000000), (3630557349404020305693567468537/11258999068426240000000000000000000), (121163190736775876922050355171/1407374883553280000000000000000000), (-33774821205701085153257214703/5629499534213120000000000000000000), (-15106097993332642568216502907/11258999068426240000000000000000000), (173220540728017276371416573/2814749767106560000000000000000000), (146847843087934365335217403/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial149.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial149.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial149.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial149 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 6894326018208173239998467788356631), (Int.negOfNat 926723992870918364250468541909907), (Int.negOfNat 91693079606246941643114242227629), (Int.ofNat 20978216326773426569094161995722), (Int.ofNat 6312796777559041712628812432893), (Int.negOfNat 564742357191590437903880941050), (Int.negOfNat 129946196329914639240467289763), (Int.ofNat 8661868496582547986848258352), (Int.ofNat 1564496174897676809549779538), (Int.negOfNat 79484468582731774440061646), (Int.negOfNat 12645861794179572922589129), (Int.ofNat 473452616554486036512767), (Int.ofNat 73339230953738532939362), (Int.negOfNat 1951500252109542827324), (Int.negOfNat 316580763129394632702), (Int.ofNat 5528862937487781642), (Int.ofNat 808893552068335443), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-6894326018208173239998467788356631/11258999068426240000000000000000000), (-926723992870918364250468541909907/11258999068426240000000000000000000), (-91693079606246941643114242227629/11258999068426240000000000000000000), (10489108163386713284547080997861/5629499534213120000000000000000000), (6312796777559041712628812432893/11258999068426240000000000000000000), (-11294847143831808758077618821/225179981368524800000000000000000), (-129946196329914639240467289763/11258999068426240000000000000000000), (541366781036409249178016147/703687441776640000000000000000000), (782248087448838404774889769/5629499534213120000000000000000000), (-39742234291365887220030823/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial149.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial149.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial149.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial149 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 8870647321426334858320934440466784), (Int.negOfNat 904635597547229342093495887790786), (Int.ofNat 117447139475516523498258012437481), (Int.ofNat 35159646673578610756127360314448), (Int.negOfNat 3416004816975599315545489681316), (Int.negOfNat 937329612790507775737550714858), (Int.ofNat 81327021298971452149391248616), (Int.ofNat 14128259872195430012497542442), (Int.negOfNat 1070012262055978089826861616), (Int.negOfNat 138548467747639498914607768), (Int.ofNat 8624338196381810562606159), (Int.ofNat 954725697797834341768955), (Int.negOfNat 46530586278945761889529), (Int.negOfNat 4825017836763053394835), (Int.ofNat 178622309060223009626), (Int.ofNat 18575786995104384721), (Int.negOfNat 792948832376026381), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-277207728794572964322529201264587/351843720888320000000000000000000), (-452317798773614671046747943895393/5629499534213120000000000000000000), (117447139475516523498258012437481/11258999068426240000000000000000000), (2197477917098663172257960019653/703687441776640000000000000000000), (-854001204243899828886372420329/2814749767106560000000000000000000), (-468664806395253887868775357429/5629499534213120000000000000000000), (10165877662371431518673906077/1407374883553280000000000000000000), (7064129936097715006248771221/5629499534213120000000000000000000), (-66875766378498630614178851/703687441776640000000000000000000), (-17318558468454937364325971/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial149.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial149.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial149.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial149 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 10006824363253986793483675850558973), (Int.negOfNat 176646927508724185988209909562910), (Int.ofNat 198013720656615234738623116610750), (Int.negOfNat 11233417876782716945795897992358), (Int.negOfNat 5562001775898786701870249787766), (Int.ofNat 558392825966700362359427814328), (Int.ofNat 105637138453337384124941101907), (Int.negOfNat 11226735262399022051291049294), (Int.negOfNat 1271202650003422182978191045), (Int.ofNat 123210754357487440352800202), (Int.ofNat 10563056938980513365673845), (Int.negOfNat 851647873226918293651509), (Int.negOfNat 63428821784331354640756), (Int.ofNat 4046703341866903595362), (Int.ofNat 283771504073529566691), (Int.negOfNat 13628858306969830167), (Int.negOfNat 798564965286060714), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-10006824363253986793483675850558973/11258999068426240000000000000000000), (-17664692750872418598820990956291/1125899906842624000000000000000000), (792054882626460938954492466443/45035996273704960000000000000000), (-5616708938391358472897948996179/5629499534213120000000000000000000), (-2781000887949393350935124893883/5629499534213120000000000000000000), (69799103245837545294928476791/1407374883553280000000000000000000), (105637138453337384124941101907/11258999068426240000000000000000000), (-5613367631199511025645524647/5629499534213120000000000000000000), (-254240530000684436595638209/2251799813685248000000000000000000), (61605377178743720176400101/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial149.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial149.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial149.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial149 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 9723983876016517552545766896886182), (Int.ofNat 361572404123467339976932866493171), (Int.ofNat 57989059187190497054085659846830), (Int.negOfNat 24273866784964127523445561251916), (Int.ofNat 2389389384929369792405172640340), (Int.ofNat 617027918186113582914543988313), (Int.negOfNat 90900649586843092286368621479), (Int.negOfNat 9246605714078451988783258608), (Int.ofNat 1428231625340835315410960837), (Int.ofNat 94261692536795363965990270), (Int.negOfNat 12856621481667900712483050), (Int.negOfNat 691073304031900407537152), (Int.ofNat 75358146419999258326035), (Int.ofNat 3697951565501549353567), (Int.negOfNat 311837817228910597639), (Int.negOfNat 14972897327998698271), (Int.ofNat 1305471623951312881), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-4861991938008258776272883448443091/5629499534213120000000000000000000), (361572404123467339976932866493171/11258999068426240000000000000000000), (5798905918719049705408565984683/1125899906842624000000000000000000), (-6068466696241031880861390312979/2814749767106560000000000000000000), (119469469246468489620258632017/562949953421312000000000000000000), (617027918186113582914543988313/11258999068426240000000000000000000), (-90900649586843092286368621479/11258999068426240000000000000000000), (-577912857129903249298953663/703687441776640000000000000000000), (1428231625340835315410960837/11258999068426240000000000000000000), (9426169253679536396599027/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial149.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial149.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial149.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial149 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 8911700206639358991200666179792451), (Int.ofNat 408077617211376811554914131828986), (Int.negOfNat 6144700790311171469158203589950), (Int.ofNat 2648951477904506753103827314722), (Int.ofNat 2304828859633618991564913691623), (Int.negOfNat 536222394450181227167448206246), (Int.negOfNat 45462469572329162501630458891), (Int.ofNat 13348633529170479441123419341), (Int.ofNat 579195931533695441690602955), (Int.negOfNat 163050947572216835461554765), (Int.negOfNat 5540972872422895415048401), (Int.ofNat 1200379698568236738164333), (Int.ofNat 38028719904561670752524), (Int.negOfNat 5960747570532610012533), (Int.negOfNat 186554905263958597756), (Int.ofNat 21503083444277482632), (Int.ofNat 617395447978690485), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-8911700206639358991200666179792451/11258999068426240000000000000000000), (204038808605688405777457065914493/5629499534213120000000000000000000), (-122894015806223429383164071799/225179981368524800000000000000000), (1324475738952253376551913657361/5629499534213120000000000000000000), (2304828859633618991564913691623/11258999068426240000000000000000000), (-268111197225090613583724103123/5629499534213120000000000000000000), (-45462469572329162501630458891/11258999068426240000000000000000000), (13348633529170479441123419341/11258999068426240000000000000000000), (115839186306739088338120591/2251799813685248000000000000000000), (-32610189514443367092310953/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial149.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial149.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial149.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial149 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 8080353310283306552740221101442020), (Int.ofNat 443597537232660705027976698464905), (Int.ofNat 20484516924109697140712437239713), (Int.negOfNat 30681016750815691036609851010), (Int.negOfNat 2077505400281764674795402444704), (Int.negOfNat 37137116033176757604639230757), (Int.ofNat 96701789725140567538043280449), (Int.ofNat 420291649727651979427629499), (Int.negOfNat 1729659670969124716835871885), (Int.negOfNat 15536769755385511419793255), (Int.ofNat 16529085105390295225400379), (Int.ofNat 221935114410435076162567), (Int.negOfNat 99984078545571349055596), (Int.negOfNat 1647707164324478078227), (Int.ofNat 422192319034734025644), (Int.ofNat 8037943881816841448), (Int.negOfNat 1640267760479987395), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-404017665514165327637011055072101/562949953421312000000000000000000), (88719507446532141005595339692981/2251799813685248000000000000000000), (20484516924109697140712437239713/11258999068426240000000000000000000), (-3068101675081569103660985101/1125899906842624000000000000000000), (-64922043758805146087356326397/351843720888320000000000000000000), (-37137116033176757604639230757/11258999068426240000000000000000000), (96701789725140567538043280449/11258999068426240000000000000000000), (420291649727651979427629499/11258999068426240000000000000000000), (-345931934193824943367174377/2251799813685248000000000000000000), (-3107353951077102283958651/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial149.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial149.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial149.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial149 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 7140085161822635835661934485142808), (Int.ofNat 472748990314797816349892826423937), (Int.negOfNat 12021140061446326767030615898312), (Int.negOfNat 5359794634780426396536513640398), (Int.ofNat 1689747098879698066328273548812), (Int.ofNat 481998558582803531857938746323), (Int.negOfNat 48698455989345769703186676239), (Int.negOfNat 14976117781976185859342064132), (Int.ofNat 482326819479829261904362097), (Int.ofNat 196626696383438531480379650), (Int.negOfNat 1937664245153313916348470), (Int.negOfNat 1482428998625220776553048), (Int.negOfNat 359082082355086462385), (Int.ofNat 7444051680545126350493), (Int.ofNat 43123361601228292361), (Int.negOfNat 27596855042648330309), (Int.negOfNat 268827862406982999), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-892510645227829479457741810642851/1407374883553280000000000000000000), (472748990314797816349892826423937/11258999068426240000000000000000000), (-1502642507680790845878826987289/1407374883553280000000000000000000), (-2679897317390213198268256820199/5629499534213120000000000000000000), (422436774719924516582068387203/2814749767106560000000000000000000), (481998558582803531857938746323/11258999068426240000000000000000000), (-48698455989345769703186676239/11258999068426240000000000000000000), (-3744029445494046464835516033/2814749767106560000000000000000000), (482326819479829261904362097/11258999068426240000000000000000000), (3932533927668770629607593/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial149.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial149.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial149.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial149 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 6247904647666913418987696224257613), (Int.ofNat 437839979285238133951435362270050), (Int.ofNat 14889802010124445647733689083195), (Int.ofNat 13090880132093619903140499155603), (Int.ofNat 641503698301933210118315568407), (Int.negOfNat 804977147904268012998588382225), (Int.negOfNat 99060553048135813765012758933), (Int.ofNat 12150308460715879710160503554), (Int.ofNat 2005658819740076087227822495), (Int.negOfNat 89599557251412621884632082), (Int.negOfNat 19478538749858562587434035), (Int.ofNat 388543916472601283917809), (Int.ofNat 117735193545967357200364), (Int.negOfNat 1021826565128448355502), (Int.negOfNat 497418923609414892909), (Int.ofNat 1216738358030502587), (Int.ofNat 1800780104222808166), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-6247904647666913418987696224257613/11258999068426240000000000000000000), (8756799585704762679028707245401/225179981368524800000000000000000), (2977960402024889129546737816639/2251799813685248000000000000000000), (13090880132093619903140499155603/11258999068426240000000000000000000), (641503698301933210118315568407/11258999068426240000000000000000000), (-32199085916170720519943535289/450359962737049600000000000000000), (-99060553048135813765012758933/11258999068426240000000000000000000), (6075154230357939855080251777/5629499534213120000000000000000000), (401131763948015217445564499/2251799813685248000000000000000000), (-44799778625706310942316041/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial149.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial149.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial149.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial149 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 5227769396210131228079615402432816), (Int.ofNat 598798194211560858004434296669304), (Int.ofNat 31798901137186116329520161074497), (Int.negOfNat 20179416026947249553341778119016), (Int.negOfNat 8296071464271554742146445318253), (Int.negOfNat 389655588786671571575669521411), (Int.ofNat 182134145409372690724660479833), (Int.ofNat 17354711156915871503348620598), (Int.negOfNat 1799590455009410695856040576), (Int.negOfNat 227422354867687446581470852), (Int.ofNat 10734068536374861374632879), (Int.ofNat 1680156838378655666352845), (Int.negOfNat 43588516562229491712109), (Int.negOfNat 8316898884419031093225), (Int.ofNat 127707707063196973826), (Int.ofNat 30206011636605246259), (Int.negOfNat 243694929168303501), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-326735587263133201754975962652051/703687441776640000000000000000000), (74849774276445107250554287083663/1407374883553280000000000000000000), (31798901137186116329520161074497/11258999068426240000000000000000000), (-2522427003368406194167722264877/1407374883553280000000000000000000), (-8296071464271554742146445318253/11258999068426240000000000000000000), (-389655588786671571575669521411/11258999068426240000000000000000000), (182134145409372690724660479833/11258999068426240000000000000000000), (8677355578457935751674310299/5629499534213120000000000000000000), (-14059300429761021061375317/87960930222080000000000000000000), (-56855588716921861645367713/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial149.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial149.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial149.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial149 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 4196303811752269862075044728451235), (Int.ofNat 227644368784795743592897658012087), (Int.negOfNat 268287256700141949813935427636653), (Int.negOfNat 67492949233271237939721742387590), (Int.ofNat 869111823713202504223838738677), (Int.ofNat 2118348818801531536171025061390), (Int.ofNat 127391004550846279339519899720), (Int.negOfNat 26927066364561577494344500012), (Int.negOfNat 2383499492706198341393413602), (Int.ofNat 201972618265337619930532826), (Int.ofNat 21763668128907431205520651), (Int.negOfNat 1031622899598181459402367), (Int.negOfNat 126903269450619082617258), (Int.ofNat 3870804847812831218564), (Int.ofNat 525094008885924489898), (Int.negOfNat 10884199763158386062), (Int.negOfNat 1790451517440533437), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-839260762350453972415008945690247/2251799813685248000000000000000000), (227644368784795743592897658012087/11258999068426240000000000000000000), (-268287256700141949813935427636653/11258999068426240000000000000000000), (-6749294923327123793972174238759/1125899906842624000000000000000000), (869111823713202504223838738677/11258999068426240000000000000000000), (211834881880153153617102506139/1125899906842624000000000000000000), (3184775113771156983487997493/281474976710656000000000000000000), (-6731766591140394373586125003/2814749767106560000000000000000000), (-1191749746353099170696706801/5629499534213120000000000000000000), (100986309132668809965266413/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial149.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial149.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial149.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial149 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 5268195456282187599064965265494119), (Int.negOfNat 1447623222605439111123583786440260), (Int.negOfNat 473566159878165604098757879504896), (Int.ofNat 26589792344523542772497206636736), (Int.ofNat 20536075224205443345637915510749), (Int.ofNat 858436135828819806339941781618), (Int.negOfNat 329231559080655994004913613066), (Int.negOfNat 23120498609562960033103357333), (Int.ofNat 3048896394993066498171798852), (Int.ofNat 259143102155391203888091917), (Int.negOfNat 18974557546804187521018618), (Int.negOfNat 1778168823006363708074297), (Int.ofNat 85815787623731178308600), (Int.ofNat 8462057539438323570320), (Int.negOfNat 296091060648978229255), (Int.negOfNat 30040910742611681923), (Int.ofNat 756217720743590001), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-5268195456282187599064965265494119/11258999068426240000000000000000000), (-72381161130271955556179189322013/562949953421312000000000000000000), (-57808369125752637219086655213/1374389534720000000000000000000), (415465505383180355820268853699/175921860444160000000000000000000), (20536075224205443345637915510749/11258999068426240000000000000000000), (429218067914409903169970890809/5629499534213120000000000000000000), (-164615779540327997002456806533/5629499534213120000000000000000000), (-23120498609562960033103357333/11258999068426240000000000000000000), (762224098748266624542949713/2814749767106560000000000000000000), (259143102155391203888091917/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial149.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial149.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial149.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial149 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 9512080743763382059762702627887782), (Int.negOfNat 2366947023330368733386958005908978), (Int.ofNat 159356852032209918341666959635023), (Int.ofNat 166093399840514349488339649731628), (Int.ofNat 7035896919314011716985069666516), (Int.negOfNat 3340613015730406504004281988873), (Int.negOfNat 220703349728235536052227309097), (Int.ofNat 38305209820562440141767071769), (Int.ofNat 2901052408848088200143921009), (Int.negOfNat 290620198986308336260982309), (Int.negOfNat 23102772162208572522232578), (Int.ofNat 1573979401057433697580125), (Int.ofNat 125877200246652560533025), (Int.negOfNat 6397087179010891385043), (Int.negOfNat 501750748459866987732), (Int.ofNat 19816398638484440577), (Int.ofNat 1780122930658258708), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-4756040371881691029881351313943891/5629499534213120000000000000000000), (-1183473511665184366693479002954489/5629499534213120000000000000000000), (159356852032209918341666959635023/11258999068426240000000000000000000), (41523349960128587372084912432907/2814749767106560000000000000000000), (1758974229828502929246267416629/2814749767106560000000000000000000), (-3340613015730406504004281988873/11258999068426240000000000000000000), (-220703349728235536052227309097/11258999068426240000000000000000000), (38305209820562440141767071769/11258999068426240000000000000000000), (2901052408848088200143921009/11258999068426240000000000000000000), (-290620198986308336260982309/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial149.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial149.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial149.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial149 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 12282773503023516949687378339667948), (Int.ofNat 198489766825951580993439016087279), (Int.ofNat 1033947038849740629092391816401091), (Int.ofNat 78254349572566842093016101452517), (Int.negOfNat 27040431862331816202417134127334), (Int.negOfNat 2187182310859633085125946467706), (Int.ofNat 396551047496567179622222505566), (Int.ofNat 31313053785470983298616700693), (Int.negOfNat 3752959466103436432156285988), (Int.negOfNat 281855155707052332721065704), (Int.ofNat 24650656674243328140947493), (Int.ofNat 1740947960158862453827228), (Int.negOfNat 118505351099780128872309), (Int.negOfNat 7809415619694849238729), (Int.ofNat 433801575633744812375), (Int.ofNat 26271996847590464005), (Int.negOfNat 1265297650058118258), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-3070693375755879237421844584916987/2814749767106560000000000000000000), (198489766825951580993439016087279/11258999068426240000000000000000000), (1033947038849740629092391816401091/11258999068426240000000000000000000), (78254349572566842093016101452517/11258999068426240000000000000000000), (-13520215931165908101208567063667/5629499534213120000000000000000000), (-1093591155429816542562973233853/5629499534213120000000000000000000), (198275523748283589811111252783/5629499534213120000000000000000000), (31313053785470983298616700693/11258999068426240000000000000000000), (-938239866525859108039071497/2814749767106560000000000000000000), (-35231894463381541590133213/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial149.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial149.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial149.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial149.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial149 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial149 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial149 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 13865134116449783192942067118988311), (Int.negOfNat 271249892216347053775709737488841), (Int.ofNat 1100029227111840605956223984858020), (Int.negOfNat 105233085758425125433898248456163), (Int.negOfNat 28519297257857879836319684710459), (Int.ofNat 2990110252784434875783336509763), (Int.ofNat 417142796085374752165364048523), (Int.negOfNat 41500907472969393282911173593), (Int.negOfNat 3924878909187766658192345488), (Int.ofNat 355434434373703452660967104), (Int.ofNat 25585741540752258396094093), (Int.negOfNat 2085449841186844996773728), (Int.negOfNat 122051975631535215508109), (Int.ofNat 8942671061167285794829), (Int.ofNat 443543278339839005375), (Int.negOfNat 29194507659418721905), (Int.negOfNat 1265297650058118258), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-13865134116449783192942067118988311/11258999068426240000000000000000000), (-271249892216347053775709737488841/11258999068426240000000000000000000), (55001461355592030297811199242901/562949953421312000000000000000000), (-105233085758425125433898248456163/11258999068426240000000000000000000), (-28519297257857879836319684710459/11258999068426240000000000000000000), (2990110252784434875783336509763/11258999068426240000000000000000000), (417142796085374752165364048523/11258999068426240000000000000000000), (-41500907472969393282911173593/11258999068426240000000000000000000), (-245304931824235416137021593/703687441776640000000000000000000), (5553663037089116447827611/175921860444160000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial149.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial149.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial149.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 11189423161932197168974165954909833), (Int.ofNat 2251065178661558815278353136819198), (Int.ofNat 90435858270776898134043768399647), (Int.negOfNat 175109231644659670451562298642137), (Int.ofNat 12071322092822130961694631884805), (Int.ofNat 3603547674693185004020119562010), (Int.negOfNat 314462953007139402536068168097), (Int.negOfNat 41535372761063088127692542769), (Int.ofNat 3785306970507747470078646309), (Int.ofNat 313574783980319385632880409), (Int.negOfNat 28196870607788431273292678), (Int.negOfNat 1680645764544434099953025), (Int.ofNat 145727846769383820030425), (Int.ofNat 6746814306159672913743), (Int.negOfNat 557927900731676834032), (Int.negOfNat 20790568909093859877), (Int.ofNat 1780122930658258708), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-11189423161932197168974165954909833/11258999068426240000000000000000000), (1125532589330779407639176568409599/5629499534213120000000000000000000), (90435858270776898134043768399647/11258999068426240000000000000000000), (-175109231644659670451562298642137/11258999068426240000000000000000000), (2414264418564426192338926376961/2251799813685248000000000000000000), (360354767469318500402011956201/1125899906842624000000000000000000), (-314462953007139402536068168097/11258999068426240000000000000000000), (-41535372761063088127692542769/11258999068426240000000000000000000), (3785306970507747470078646309/11258999068426240000000000000000000), (313574783980319385632880409/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial149.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial149.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial149.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 7442312786530088140573556816395402), (Int.ofNat 1111518423343740146712429190133395), (Int.negOfNat 477740094627568948413057070888528), (Int.ofNat 12268520361292122184072160199), (Int.ofNat 22683357511492173336165578812990), (Int.negOfNat 1591691960322686336367528134172), (Int.negOfNat 371238095488985655767205807266), (Int.ofNat 32406562386697826608307819033), (Int.ofNat 3449162424902636605870705152), (Int.negOfNat 326276977478061039695873617), (Int.negOfNat 21289542275756852821627218), (Int.ofNat 2092674521968458684941597), (Int.ofNat 94851517000497496788700), (Int.negOfNat 9496921783579208777120), (Int.negOfNat 321744211108359604155), (Int.ofNat 32313974707366993623), (Int.ofNat 756217720743590001), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-3721156393265044070286778408197701/5629499534213120000000000000000000), (222303684668748029342485838026679/2251799813685248000000000000000000), (-29858755914223059275816066930533/703687441776640000000000000000000), (12268520361292122184072160199/11258999068426240000000000000000000), (2268335751149217333616557881299/1125899906842624000000000000000000), (-397922990080671584091882033543/2814749767106560000000000000000000), (-185619047744492827883602903633/5629499534213120000000000000000000), (32406562386697826608307819033/11258999068426240000000000000000000), (6736645361137962120841221/21990232555520000000000000000000), (-326276977478061039695873617/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial149.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial149.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial149.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 6837051067225667281389783058896909), (Int.negOfNat 254825657289845798359058919038376), (Int.negOfNat 123425301262846888742295449635916), (Int.ofNat 80756977753514594906380668230768), (Int.negOfNat 4075925217139251094722247415449), (Int.negOfNat 2540487808857655525165823837830), (Int.ofNat 212270929203667524346966466577), (Int.ofNat 32496945730888257046419308612), (Int.negOfNat 3166914493382309200454830502), (Int.negOfNat 242916620757871045857450526), (Int.ofNat 26237102455410201449808751), (Int.ofNat 1224862106143202906734167), (Int.negOfNat 144264669428419030456358), (Int.negOfNat 4508030606498377832964), (Int.ofNat 574127245839931927998), (Int.ofNat 12183093457304278462), (Int.negOfNat 1790451517440533437), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-6837051067225667281389783058896909/11258999068426240000000000000000000), (-31853207161230724794882364879797/1407374883553280000000000000000000), (-30856325315711722185573862408979/2814749767106560000000000000000000), (5047311109594662181648791764423/703687441776640000000000000000000), (-4075925217139251094722247415449/11258999068426240000000000000000000), (-254048780885765552516582383783/1125899906842624000000000000000000), (212270929203667524346966466577/11258999068426240000000000000000000), (8124236432722064261604827153/2814749767106560000000000000000000), (-1583457246691154600227415251/5629499534213120000000000000000000), (-121458310378935522928725263/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial149.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial149.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial149.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 7324019575897093318712359601496499), (Int.negOfNat 61455297789769136427283588022502), (Int.ofNat 126370330330514051541346201417123), (Int.negOfNat 7851714914628948996898733524136), (Int.negOfNat 11786742364677959858464137376466), (Int.ofNat 1060303625874339498982977845125), (Int.ofNat 246496929270633485914002997576), (Int.negOfNat 25387312470699145353343742398), (Int.negOfNat 2413179858837946097948939176), (Int.ofNat 284067542555511412970691752), (Int.ofNat 14289108103925937103863779), (Int.negOfNat 1942504741933751995896045), (Int.negOfNat 57478569229195105548809), (Int.ofNat 9175319907872625014525), (Int.ofNat 166999241311110218926), (Int.negOfNat 32479075601360557959), (Int.negOfNat 243694929168303501), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-7324019575897093318712359601496499/11258999068426240000000000000000000), (-30727648894884568213641794011251/5629499534213120000000000000000000), (126370330330514051541346201417123/11258999068426240000000000000000000), (-981464364328618624612341690517/1407374883553280000000000000000000), (-5893371182338979929232068688233/5629499534213120000000000000000000), (8482429006994715991863822761/90071992547409920000000000000000), (30812116158829185739250374697/1407374883553280000000000000000000), (-12693656235349572676671871199/5629499534213120000000000000000000), (-301647482354743262243617397/1407374883553280000000000000000000), (35508442819438926621336469/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial149.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial149.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial149.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 7146856340063034454222609550326693), (Int.ofNat 91641635837895592646672358110620), (Int.negOfNat 79606406878412064102160273728784), (Int.negOfNat 37174460225578205006602515391723), (Int.ofNat 5046411039471615850639547950433), (Int.ofNat 1432367169680641486248831852265), (Int.negOfNat 170352984834156646922944248933), (Int.negOfNat 20060216988176725717646179254), (Int.ofNat 2636208345823430420085565495), (Int.ofNat 146744532553751265790124982), (Int.negOfNat 23003913400849105117847935), (Int.negOfNat 656189664365389524502609), (Int.ofNat 131282205775640651364064), (Int.ofNat 1901797736242435893602), (Int.negOfNat 535086840739645772509), (Int.negOfNat 3489802322785814287), (Int.ofNat 1800780104222808166), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-7146856340063034454222609550326693/11258999068426240000000000000000000), (4582081791894779632333617905531/562949953421312000000000000000000), (-4975400429900754006385017108049/703687441776640000000000000000000), (-37174460225578205006602515391723/11258999068426240000000000000000000), (5046411039471615850639547950433/11258999068426240000000000000000000), (286473433936128297249766370453/2251799813685248000000000000000000), (-170352984834156646922944248933/11258999068426240000000000000000000), (-10030108494088362858823089627/5629499534213120000000000000000000), (527241669164686084017113099/2251799813685248000000000000000000), (73372266276875632895062491/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial149.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial149.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial149.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 7465560703250385937756642967917954), (Int.negOfNat 435582066120318458734177994432675), (Int.negOfNat 116189333848466331793361448670056), (Int.ofNat 27148189082782616295767510487982), (Int.ofNat 6756166591521693103994554494154), (Int.negOfNat 1011583336478991058546550021330), (Int.negOfNat 136548265187342707164709527339), (Int.ofNat 21006680724432179932873474532), (Int.ofNat 1288415717264428968917141097), (Int.negOfNat 237937795118175762864604450), (Int.negOfNat 6525038890976167374767870), (Int.ofNat 1671059773959169952710948), (Int.ofNat 17416751728859396600415), (Int.negOfNat 8057011102475001171093), (Int.negOfNat 6884045623388565039), (Int.ofNat 28895748736794222709), (Int.negOfNat 268827862406982999), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-3732780351625192968878321483958977/5629499534213120000000000000000000), (-17423282644812738349367119777307/450359962737049600000000000000000), (-14523666731058291474170181083757/1407374883553280000000000000000000), (13574094541391308147883755243991/5629499534213120000000000000000000), (3378083295760846551997277247077/5629499534213120000000000000000000), (-101158333647899105854655002133/1125899906842624000000000000000000), (-136548265187342707164709527339/11258999068426240000000000000000000), (5251670181108044983218368633/2814749767106560000000000000000000), (1288415717264428968917141097/11258999068426240000000000000000000), (-4758755902363515257292089/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial149.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial149.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial149.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 8514414136284429281929023832020124), (Int.negOfNat 455340193898014600334802249270433), (Int.ofNat 110450260863067701665872581388111), (Int.ofNat 31649903361374171109757505537679), (Int.negOfNat 5204816059237405914255707039996), (Int.negOfNat 792094209126204859404949464766), (Int.ofNat 144058691060819161988609475649), (Int.ofNat 9515263419080338784236790001), (Int.negOfNat 2136423201059052573497461385), (Int.negOfNat 54336600657381948405667745), (Int.ofNat 18771190812976078589345479), (Int.ofNat 101200913116356855513233), (Int.negOfNat 108540444610554874567696), (Int.ofNat 591854299360708512127), (Int.ofNat 445897128952896561944), (Int.negOfNat 5440156493525056648), (Int.negOfNat 1640267760479987395), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-2128603534071107320482255958005031/2814749767106560000000000000000000), (-455340193898014600334802249270433/11258999068426240000000000000000000), (110450260863067701665872581388111/11258999068426240000000000000000000), (31649903361374171109757505537679/11258999068426240000000000000000000), (-1301204014809351478563926759999/2814749767106560000000000000000000), (-396047104563102429702474732383/5629499534213120000000000000000000), (144058691060819161988609475649/11258999068426240000000000000000000), (9515263419080338784236790001/11258999068426240000000000000000000), (-427284640211810514699492277/2251799813685248000000000000000000), (-10867320131476389681133549/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial149.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial149.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial149.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 8828836363837235941775065696590527), (Int.ofNat 166041918707198747453463931339939), (Int.ofNat 149168060444663921414813809473262), (Int.negOfNat 17134174797327994682104849007313), (Int.negOfNat 4186386861703852182793666652415), (Int.ofNat 813216840462528705453765992803), (Int.ofNat 60076855502566282033658179709), (Int.negOfNat 16443025075539354909521196041), (Int.negOfNat 359961825582102796330506745), (Int.ofNat 184216065712055013663494765), (Int.negOfNat 273261553261365043898301), (Int.negOfNat 1297002995829574395253933), (Int.ofNat 17755240146404599980924), (Int.ofNat 6275433874609307009333), (Int.negOfNat 130053029568612278356), (Int.negOfNat 22477253714886901932), (Int.ofNat 617395447978690485), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-8828836363837235941775065696590527/11258999068426240000000000000000000), (166041918707198747453463931339939/11258999068426240000000000000000000), (74584030222331960707406904736631/5629499534213120000000000000000000), (-17134174797327994682104849007313/11258999068426240000000000000000000), (-837277372340770436558733330483/2251799813685248000000000000000000), (813216840462528705453765992803/11258999068426240000000000000000000), (60076855502566282033658179709/11258999068426240000000000000000000), (-16443025075539354909521196041/11258999068426240000000000000000000), (-71992365116420559266101349/2251799813685248000000000000000000), (36843213142411002732698953/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial149.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial149.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial149.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 8076373368741627436264362276597976), (Int.ofNat 492405886431928205919474332091091), (Int.ofNat 14482087285387485226858548992031), (Int.negOfNat 17402379422171473944830516155720), (Int.ofNat 3231846738293110788437032739878), (Int.ofNat 326160561734903309019280407000), (Int.negOfNat 104463701303881999267705324079), (Int.negOfNat 1736030722704239611164352692), (Int.ofNat 1552961673706721905169099537), (Int.negOfNat 17860760203363922157103970), (Int.negOfNat 13568907768147614000887250), (Int.ofNat 339506737573627187782552), (Int.ofNat 78124081928343227066035), (Int.negOfNat 2551471558701249229667), (Int.negOfNat 319631179393785952039), (Int.ofNat 12050386516170440371), (Int.ofNat 1305471623951312881), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-1009546671092703429533045284574747/1407374883553280000000000000000000), (492405886431928205919474332091091/11258999068426240000000000000000000), (14482087285387485226858548992031/11258999068426240000000000000000000), (-435059485554286848620762903893/281474976710656000000000000000000), (1615923369146555394218516369939/5629499534213120000000000000000000), (326160561734903309019280407/11258999068426240000000000000000), (-104463701303881999267705324079/11258999068426240000000000000000000), (-434007680676059902791088173/2814749767106560000000000000000000), (1552961673706721905169099537/11258999068426240000000000000000000), (-1786076020336392215710397/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial149.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial149.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial149.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 7117237976615082886167833689705903), (Int.ofNat 451668034420091085748144590393930), (Int.negOfNat 9954306855384652046493654527781), (Int.ofNat 6313098127900794686092340495698), (Int.ofNat 1247496520299634227190811062225), (Int.negOfNat 506096316526418933984550577625), (Int.negOfNat 3559999676185268282249822693), (Int.ofNat 10889624171705164804689887994), (Int.negOfNat 298092509520879067321908745), (Int.negOfNat 121753245229048214282345202), (Int.ofNat 5098063940699420394436345), (Int.ofNat 846884012089861910549109), (Int.negOfNat 42383887091861187472256), (Int.negOfNat 4033685098255590108462), (Int.ofNat 224996564413427935591), (Int.ofNat 13628858306969830167), (Int.negOfNat 798564965286060714), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-7117237976615082886167833689705903/11258999068426240000000000000000000), (45166803442009108574814459039393/1125899906842624000000000000000000), (-9954306855384652046493654527781/11258999068426240000000000000000000), (3156549063950397343046170247849/5629499534213120000000000000000000), (49899860811985369087632442489/450359962737049600000000000000000), (-4048770532211351471876404621/90071992547409920000000000000000), (-3559999676185268282249822693/11258999068426240000000000000000000), (5444812085852582402344943997/5629499534213120000000000000000000), (-59618501904175813464381749/2251799813685248000000000000000000), (-60876622614524107141172601/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial149.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial149.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial149.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 6198415353138389094355421338099704), (Int.ofNat 490683847042831807047368401019038), (Int.ofNat 22823862914855582167687073960445), (Int.ofNat 497392389596030345855521997010), (Int.negOfNat 1705039464633875034218108225483), (Int.ofNat 47702608494012250161182627152), (Int.ofNat 60148295447828831274111032516), (Int.negOfNat 3447711831492930263490736842), (Int.negOfNat 904396409100658347694771616), (Int.ofNat 63237043931149657846354468), (Int.ofNat 7754899214794778599612159), (Int.negOfNat 605968791638416624173155), (Int.negOfNat 43292481831302883683429), (Int.ofNat 3684412158256264349635), (Int.ofNat 169854776624738235926), (Int.negOfNat 15653276183276126821), (Int.negOfNat 792948832376026381), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-774801919142298636794427667262463/1407374883553280000000000000000000), (245341923521415903523684200509519/5629499534213120000000000000000000), (4564772582971116433537414792089/2251799813685248000000000000000000), (49739238959603034585552199701/1125899906842624000000000000000000), (-1705039464633875034218108225483/11258999068426240000000000000000000), (2981413030875765635073914197/703687441776640000000000000000000), (15037073861957207818527758129/2814749767106560000000000000000000), (-1723855915746465131745368421/5629499534213120000000000000000000), (-28262387784395573365461613/351843720888320000000000000000000), (15809260982787414461588617/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial149.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial149.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial149.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 5144311625452670502826974472940397), (Int.ofNat 546458474443789039916127717514578), (Int.negOfNat 437090299474071429042551803813), (Int.negOfNat 4732708358411455281722319839084), (Int.ofNat 732193690407009658114826247289), (Int.ofNat 243757494551408222003594713750), (Int.negOfNat 31481631278393569777910432420), (Int.negOfNat 5212085433249279485505499752), (Int.ofNat 657602996468358124181058138), (Int.ofNat 56472959577476265888420246), (Int.negOfNat 7477229133942080762810429), (Int.negOfNat 369740022206035695389067), (Int.ofNat 53298597796706422818562), (Int.ofNat 1616504080726888980324), (Int.negOfNat 260403610857584786402), (Int.negOfNat 4554692666878362342), (Int.ofNat 808893552068335443), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-5144311625452670502826974472940397/11258999068426240000000000000000000), (273229237221894519958063858757289/5629499534213120000000000000000000), (-437090299474071429042551803813/11258999068426240000000000000000000), (-1183177089602863820430579959771/2814749767106560000000000000000000), (732193690407009658114826247289/11258999068426240000000000000000000), (195005995641126577602875771/9007199254740992000000000000000), (-1574081563919678488895521621/562949953421312000000000000000000), (-651510679156159935688187469/1407374883553280000000000000000000), (328801498234179062090529069/5629499534213120000000000000000000), (28236479788738132944210123/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial149.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial149.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial149.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 4073982263318820133561773022287314), (Int.ofNat 523231339325412599977378698490574), (Int.negOfNat 1472342426456127531775723613702), (Int.ofNat 4277144215445908688930896811970), (Int.ofNat 676660114768322042564477302766), (Int.negOfNat 228949680509314505894404706005), (Int.negOfNat 20138353993803603280962381806), (Int.ofNat 5722068513015232974133922707), (Int.ofNat 277601618622757078642384692), (Int.negOfNat 79086885558676502572200303), (Int.negOfNat 2029301463533993053994598), (Int.ofNat 673052762452262129482903), (Int.ofNat 8527569742659955694820), (Int.negOfNat 3854951834264787310040), (Int.negOfNat 19949231352003808455), (Int.ofNat 16170956387937892857), (Int.ofNat 280426040800739881), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-2036991131659410066780886511143657/5629499534213120000000000000000000), (261615669662706299988689349245287/5629499534213120000000000000000000), (-736171213228063765887861806851/5629499534213120000000000000000000), (427714421544590868893089681197/1125899906842624000000000000000000), (338330057384161021282238651383/5629499534213120000000000000000000), (-45789936101862901178880941201/2251799813685248000000000000000000), (-10069176996901801640481190903/5629499534213120000000000000000000), (5722068513015232974133922707/11258999068426240000000000000000000), (69400404655689269660596173/2814749767106560000000000000000000), (-79086885558676502572200303/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial149.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial149.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial149.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 2996218180982644122166734729017386), (Int.ofNat 570801017273040310628248572395557), (Int.ofNat 21254988505162889166343282475355), (Int.ofNat 584056746393366023845843407234), (Int.negOfNat 1226074072082082091068428176653), (Int.negOfNat 21870916975908959819617595070), (Int.ofNat 40729826010744921686117098643), (Int.ofNat 190290712888469607491169309), (Int.negOfNat 705239635460894980469593131), (Int.ofNat 2867550650591515328383271), (Int.ofNat 7311170801744516144780002), (Int.negOfNat 70387514790673920141375), (Int.negOfNat 49717216172884959730695), (Int.ofNat 641536754159816727797), (Int.ofNat 237287290702174752168), (Int.negOfNat 3921924933841606243), (Int.negOfNat 819222138850610172), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-1498109090491322061083367364508693/5629499534213120000000000000000000), (570801017273040310628248572395557/11258999068426240000000000000000000), (4250997701032577833268656495071/2251799813685248000000000000000000), (292028373196683011922921703617/5629499534213120000000000000000000), (-1226074072082082091068428176653/11258999068426240000000000000000000), (-2187091697590895981961759507/1125899906842624000000000000000000), (40729826010744921686117098643/11258999068426240000000000000000000), (190290712888469607491169309/11258999068426240000000000000000000), (-705239635460894980469593131/11258999068426240000000000000000000), (2867550650591515328383271/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial149.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial149.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial149.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 1782781652200653366783092089240418), (Int.ofNat 629070905508480338302967786603270), (Int.ofNat 2315404727887939344821861503204), (Int.negOfNat 4620329856546369009840944365245), (Int.ofNat 363432882115756661979195152062), (Int.ofNat 224978148386089609644572934874), (Int.negOfNat 12772860095600963248253119237), (Int.negOfNat 5129011108895066486418729747), (Int.ofNat 242412890275300250542278572), (Int.ofNat 66447948626627193837564816), (Int.negOfNat 2800266776035244066246127), (Int.negOfNat 546714175429633141083572), (Int.ofNat 21196330098647161413771), (Int.ofNat 3083242248876961891731), (Int.negOfNat 110351664592061321725), (Int.negOfNat 12809365525550546275), (Int.ofNat 235539613035304862), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-891390826100326683391546044620209/5629499534213120000000000000000000), (62907090550848033830296778660327/1125899906842624000000000000000000), (578851181971984836205465375801/2814749767106560000000000000000000), (-924065971309273801968188873049/2251799813685248000000000000000000), (181716441057878330989597576031/5629499534213120000000000000000000), (112489074193044804822286467437/5629499534213120000000000000000000), (-12772860095600963248253119237/11258999068426240000000000000000000), (-5129011108895066486418729747/11258999068426240000000000000000000), (60603222568825062635569643/2814749767106560000000000000000000), (4152996789164199614847801/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial149.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial149.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial149.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 540708408961852583002815281702356), (Int.ofNat 608147984868704399466646586287842), (Int.negOfNat 4503300240555342948362895942213), (Int.ofNat 3099064090784085509184268378271), (Int.ofNat 893080200722352734831837517163), (Int.negOfNat 152303591781908797963309187383), (Int.negOfNat 28450346632092912799731213923), (Int.ofNat 3552386049026406941130538013), (Int.ofNat 477617438283394092028578188), (Int.negOfNat 47610355657886330309735764), (Int.negOfNat 4876462943365021250167593), (Int.ofNat 408105289144109592166628), (Int.ofNat 33108074393856418616109), (Int.negOfNat 2401732507037584394109), (Int.negOfNat 159350217274770087375), (Int.ofNat 10707702793671726345), (Int.ofNat 484426002321935658), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-135177102240463145750703820425589/2814749767106560000000000000000000), (304073992434352199733323293143921/5629499534213120000000000000000000), (-4503300240555342948362895942213/11258999068426240000000000000000000), (3099064090784085509184268378271/11258999068426240000000000000000000), (893080200722352734831837517163/11258999068426240000000000000000000), (-152303591781908797963309187383/11258999068426240000000000000000000), (-28450346632092912799731213923/11258999068426240000000000000000000), (3552386049026406941130538013/11258999068426240000000000000000000), (119404359570848523007144547/2814749767106560000000000000000000), (-11902588914471582577433941/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial149.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial149.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial149.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 690510173600658366495507796072177), (Int.ofNat 640206520167155617165811630839257), (Int.ofNat 19493463691027830576195876031581), (Int.ofNat 2134044419934658825373673491263), (Int.negOfNat 1044457811766362856090674981136), (Int.negOfNat 102136468201070768830491612020), (Int.ofNat 33768586662533195577486197917), (Int.ofNat 2336659637574711474092822969), (Int.negOfNat 575870500131816083788300829), (Int.negOfNat 30881094801093956110670409), (Int.ofNat 5977651494842739085868118), (Int.ofNat 262054393238495934802225), (Int.negOfNat 41266211102019779400785), (Int.negOfNat 1531756124236511959143), (Int.ofNat 201375787903070478332), (Int.ofNat 6997728851169045877), (Int.negOfNat 584107198607012348), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(690510173600658366495507796072177/11258999068426240000000000000000000), (640206520167155617165811630839257/11258999068426240000000000000000000), (19493463691027830576195876031581/11258999068426240000000000000000000), (2134044419934658825373673491263/11258999068426240000000000000000000), (-65278613235397678505667186321/703687441776640000000000000000000), (-5106823410053538441524580601/562949953421312000000000000000000), (33768586662533195577486197917/11258999068426240000000000000000000), (2336659637574711474092822969/11258999068426240000000000000000000), (-575870500131816083788300829/11258999068426240000000000000000000), (-30881094801093956110670409/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial149.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial149.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial149.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 2048293259780943395053232692446337), (Int.ofNat 709097377142193699631363614906279), (Int.ofNat 7633548738099644954228096957817), (Int.negOfNat 4695602595510458014801946144298), (Int.negOfNat 69092603468234212661931130697), (Int.ofNat 230603259364982853137728791152), (Int.ofNat 2579677715654520517917304566), (Int.negOfNat 5321404719025628267029694853), (Int.negOfNat 58257372423223286383037852), (Int.ofNat 70014531589834210183877077), (Int.ofNat 793573353802087277302518), (Int.negOfNat 587189525286668922596697), (Int.negOfNat 6861061411774287157000), (Int.ofNat 3379454862612693352600), (Int.ofNat 39649346694907498855), (Int.negOfNat 14151893265156471163), (Int.ofNat 24653926992592599), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(2048293259780943395053232692446337/11258999068426240000000000000000000), (709097377142193699631363614906279/11258999068426240000000000000000000), (7633548738099644954228096957817/11258999068426240000000000000000000), (-2347801297755229007400973072149/5629499534213120000000000000000000), (-69092603468234212661931130697/11258999068426240000000000000000000), (14412703710311428321108049447/703687441776640000000000000000000), (1289838857827260258958652283/5629499534213120000000000000000000), (-5321404719025628267029694853/11258999068426240000000000000000000), (-14564343105805821595759463/2814749767106560000000000000000000), (70014531589834210183877077/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial149.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial149.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial149.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3465235713843716497814393763900751), (Int.ofNat 697732066523493162059998851366187), (Int.negOfNat 6495974663416305554397288834331), (Int.ofNat 1668156154390540329821104801398), (Int.ofNat 1105009259650775898440823531667), (Int.negOfNat 80936142041402954606506926590), (Int.negOfNat 37078740961713591164912822797), (Int.ofNat 1681550552348097237358000288), (Int.ofNat 650680689988035037020666622), (Int.negOfNat 18627562297884798841660674), (Int.negOfNat 6891346006749904293967391), (Int.ofNat 123217032101982712075433), (Int.ofNat 48141712504317901841118), (Int.negOfNat 521626163810590665636), (Int.negOfNat 235710548085158724298), (Int.ofNat 1285023177084062438), (Int.ofNat 594435785389287077), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(3465235713843716497814393763900751/11258999068426240000000000000000000), (697732066523493162059998851366187/11258999068426240000000000000000000), (-6495974663416305554397288834331/11258999068426240000000000000000000), (834078077195270164910552400699/5629499534213120000000000000000000), (1105009259650775898440823531667/11258999068426240000000000000000000), (-8093614204140295460650692659/1125899906842624000000000000000000), (-37078740961713591164912822797/11258999068426240000000000000000000), (52548454760878038667437509/351843720888320000000000000000000), (325340344994017518510333311/5629499534213120000000000000000000), (-9313781148942399420830337/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial149.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial149.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial149.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4861144009845229727706546303456264), (Int.ofNat 714876275534257762508423764132826), (Int.ofNat 16796748090482581084200827767719), (Int.ofNat 3250186671477470678914766520232), (Int.negOfNat 886323284930732445882007897404), (Int.negOfNat 178128847815866356184578597662), (Int.ofNat 28049669087515537698804125424), (Int.ofNat 4511325520291612666195669518), (Int.negOfNat 444092824793398692416251424), (Int.negOfNat 64063537003653643754560912), (Int.ofNat 4099686206965530553249721), (Int.ofNat 568178555628613669701045), (Int.negOfNat 24372034071303882282591), (Int.negOfNat 3391432232218522089205), (Int.ofNat 100159828078149448574), (Int.ofNat 14641717582686508599), (Int.negOfNat 537176718567879099), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(607643001230653715963318287932033/1407374883553280000000000000000000), (357438137767128881254211882066413/5629499534213120000000000000000000), (16796748090482581084200827767719/11258999068426240000000000000000000), (406273333934683834864345815029/1407374883553280000000000000000000), (-221580821232683111470501974351/2814749767106560000000000000000000), (-89064423907933178092289298831/5629499534213120000000000000000000), (1753104317969721106175257839/703687441776640000000000000000000), (2255662760145806333097834759/5629499534213120000000000000000000), (-13877900774793709138007857/351843720888320000000000000000000), (-4003971062728352734660057/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial149.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial149.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial149.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 6366435127341686050533609470363133), (Int.ofNat 785283737514810446332470923929990), (Int.ofNat 9509402054844169944998855232490), (Int.negOfNat 5008151739727897064620127074002), (Int.negOfNat 402238865312297562931948272074), (Int.ofNat 255727904945442911352006932312), (Int.ofNat 18518383078768316095571270853), (Int.negOfNat 5808542718009060601805410946), (Int.negOfNat 412344707217461931334427115), (Int.ofNat 71587545277330785855787518), (Int.ofNat 5143726828945943138923675), (Int.negOfNat 541131561902596250699091), (Int.negOfNat 39882182077029903366324), (Int.ofNat 2741914915213910535398), (Int.ofNat 208972107343944362109), (Int.negOfNat 9653590888066053513), (Int.negOfNat 604764372171561806), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(6366435127341686050533609470363133/11258999068426240000000000000000000), (78528373751481044633247092392999/1125899906842624000000000000000000), (950940205484416994499885523249/1125899906842624000000000000000000), (-2504075869863948532310063537001/5629499534213120000000000000000000), (-201119432656148781465974136037/5629499534213120000000000000000000), (31965988118180363919000866539/1407374883553280000000000000000000), (18518383078768316095571270853/11258999068426240000000000000000000), (-2904271359004530300902705473/5629499534213120000000000000000000), (-82468941443492386266885423/2251799813685248000000000000000000), (35793772638665392927893759/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial149.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial149.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial149.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 7937099264492388489903022943078902), (Int.ofNat 771525540179046334747107141555149), (Int.negOfNat 9561156136475188371306388511110), (Int.ofNat 1411738142734360429027817795996), (Int.ofNat 1508970638384020645559778199060), (Int.negOfNat 27863302539914280405682374793), (Int.negOfNat 53221420874880428582695750961), (Int.negOfNat 655153733577338132109631752), (Int.ofNat 914523290467049553422372203), (Int.ofNat 25807302046832071247052010), (Int.negOfNat 8951236121734261479567430), (Int.negOfNat 334355427536545336749048), (Int.ofNat 55670262532558782873485), (Int.ofNat 2388871134218892776673), (Int.negOfNat 240313948864867929161), (Int.negOfNat 11383114141656646449), (Int.ofNat 1049699510143165599), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(3968549632246194244951511471539451/5629499534213120000000000000000000), (771525540179046334747107141555149/11258999068426240000000000000000000), (-956115613647518837130638851111/1125899906842624000000000000000000), (352934535683590107256954448999/2814749767106560000000000000000000), (75448531919201032277988909953/562949953421312000000000000000000), (-27863302539914280405682374793/11258999068426240000000000000000000), (-53221420874880428582695750961/11258999068426240000000000000000000), (-81894216697167266513703969/1407374883553280000000000000000000), (914523290467049553422372203/11258999068426240000000000000000000), (2580730204683207124705201/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial149.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial149.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial149.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 9473199223178506962047732822859491), (Int.ofNat 786715548696171753111831389974374), (Int.ofNat 21331357991776399687923850298110), (Int.ofNat 5119383375357994828020829189878), (Int.negOfNat 1144839742717019069477847413583), (Int.negOfNat 335730837373107904823560727994), (Int.ofNat 25966661659742230497849174331), (Int.ofNat 8889195956304313183608843699), (Int.negOfNat 186750236488373013531622195), (Int.negOfNat 119149754807160202323749755), (Int.negOfNat 607560633009636432234119), (Int.ofNat 930668223918949966884867), (Int.ofNat 16658169082878124212156), (Int.negOfNat 4806219627040858888027), (Int.negOfNat 120195904151508601244), (Int.ofNat 17934102857303978248), (Int.ofNat 444252028428741035), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(9473199223178506962047732822859491/11258999068426240000000000000000000), (393357774348085876555915694987187/5629499534213120000000000000000000), (2133135799177639968792385029811/1125899906842624000000000000000000), (2559691687678997414010414594939/5629499534213120000000000000000000), (-1144839742717019069477847413583/11258999068426240000000000000000000), (-167865418686553952411780363997/5629499534213120000000000000000000), (25966661659742230497849174331/11258999068426240000000000000000000), (8889195956304313183608843699/11258999068426240000000000000000000), (-37350047297674602706324439/2251799813685248000000000000000000), (-23829950961432040464749951/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial149.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial149.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial149.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 11146542178916687357488160178494780), (Int.ofNat 878489964545406854078308203214615), (Int.ofNat 9054415251048040345724918935767), (Int.negOfNat 9280764505155980457444661490630), (Int.negOfNat 1113318870258735187879409181696), (Int.ofNat 421350408553546395847715934037), (Int.ofNat 61034064884837505535590292191), (Int.negOfNat 7052723116939948288422401739), (Int.negOfNat 1285658854390312207845572955), (Int.ofNat 46232792141221148450829975), (Int.ofNat 13191403875558032257773301), (Int.negOfNat 99866848104243391957767), (Int.negOfNat 82926411965608166052724), (Int.negOfNat 478048985873054512213), (Int.ofNat 359048483171563633356), (Int.ofNat 4964619119749325672), (Int.negOfNat 1398267095714873085), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(557327108945834367874408008924739/562949953421312000000000000000000), (175697992909081370815661640642923/2251799813685248000000000000000000), (9054415251048040345724918935767/11258999068426240000000000000000000), (-928076450515598045744466149063/1125899906842624000000000000000000), (-1087225459237046081913485529/10995116277760000000000000000000), (421350408553546395847715934037/11258999068426240000000000000000000), (61034064884837505535590292191/11258999068426240000000000000000000), (-7052723116939948288422401739/11258999068426240000000000000000000), (-257131770878062441569114591/2251799813685248000000000000000000), (1849311685648845938033199/450359962737049600000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial149.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial149.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial149.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 12863874704098185429159772972209248), (Int.ofNat 808833599972069128716267890661063), (Int.negOfNat 31680298509910405401864794466768), (Int.ofNat 2616465678126070438320768000958), (Int.ofNat 3696703442287192998917325881268), (Int.ofNat 173791940149890089693506869517), (Int.negOfNat 112512511665822733188266037001), (Int.negOfNat 10824509139293697334219101108), (Int.ofNat 1181850462861613849644217343), (Int.ofNat 159500365701437461678478870), (Int.negOfNat 6383225603801538986131210), (Int.negOfNat 1253694799104146351093552), (Int.ofNat 18670585185405779803905), (Int.ofNat 6449281499855294598267), (Int.negOfNat 15663777848300051161), (Int.negOfNat 24544332879949361971), (Int.negOfNat 109455891900066521), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(401996084503068294661242905381539/351843720888320000000000000000000), (808833599972069128716267890661063/11258999068426240000000000000000000), (-1980018656869400337616549654173/703687441776640000000000000000000), (1308232839063035219160384000479/5629499534213120000000000000000000), (924175860571798249729331470317/2814749767106560000000000000000000), (173791940149890089693506869517/11258999068426240000000000000000000), (-112512511665822733188266037001/11258999068426240000000000000000000), (-2706127284823424333554775277/2814749767106560000000000000000000), (1181850462861613849644217343/11258999068426240000000000000000000), (15950036570143746167847887/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial149.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial149.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial149.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 14432249936830936924166987903841253), (Int.ofNat 820787771510040850734008056275790), (Int.ofNat 55111940536710338440948612569445), (Int.ofNat 17906326152929679873157523410277), (Int.negOfNat 2514316007486779955168622609727), (Int.negOfNat 1319211448956593585834193348055), (Int.negOfNat 62039238259511886900275213707), (Int.ofNat 19441102669176580720131228086), (Int.ofNat 1640025232030562249694429145), (Int.negOfNat 145810295110692429844771838), (Int.negOfNat 16732596007369425572110045), (Int.ofNat 674000989594236228794191), (Int.ofNat 103323694883342439308956), (Int.negOfNat 2050386986033141371458), (Int.negOfNat 443927739620305643491), (Int.ofNat 3883776288167746093), (Int.ofNat 1579436613022243314), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(14432249936830936924166987903841253/11258999068426240000000000000000000), (82078777151004085073400805627579/1125899906842624000000000000000000), (11022388107342067688189722513889/2251799813685248000000000000000000), (17906326152929679873157523410277/11258999068426240000000000000000000), (-2514316007486779955168622609727/11258999068426240000000000000000000), (-263842289791318717166838669611/2251799813685248000000000000000000), (-62039238259511886900275213707/11258999068426240000000000000000000), (9720551334588290360065614043/5629499534213120000000000000000000), (328005046406112449938885829/2251799813685248000000000000000000), (-72905147555346214922385919/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial149.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial149.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial149.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 16353927815761048344088395108665176), (Int.ofNat 1068182240486546374755123074271736), (Int.negOfNat 3055850810998838312156790304297), (Int.negOfNat 52078693332437380770345600745304), (Int.negOfNat 12920861875182216654216009084427), (Int.negOfNat 95485825632732407715982775829), (Int.ofNat 254917690226583894331665017407), (Int.ofNat 14393449579925095065919503242), (Int.negOfNat 2450339915135440462465070664), (Int.negOfNat 198949172987566291542742868), (Int.ofNat 14644006093060610392351401), (Int.ofNat 1491986175131055272871555), (Int.negOfNat 60175875842374640305211), (Int.negOfNat 7471010241151513547135), (Int.ofNat 179354191185206768974), (Int.ofNat 27497775699982102221), (Int.negOfNat 403066899675219979), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(2044240976970131043011049388583147/1407374883553280000000000000000000), (133522780060818296844390384283967/1407374883553280000000000000000000), (-3055850810998838312156790304297/11258999068426240000000000000000000), (-6509836666554672596293200093163/1407374883553280000000000000000000), (-12920861875182216654216009084427/11258999068426240000000000000000000), (-95485825632732407715982775829/11258999068426240000000000000000000), (254917690226583894331665017407/11258999068426240000000000000000000), (7196724789962547532959751621/5629499534213120000000000000000000), (-306292489391930057808133833/1407374883553280000000000000000000), (-49737293246891572885685717/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial149.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial149.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial149.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 17869095702313043984625540451766875), (Int.ofNat 62422939592546429471192399660113), (Int.negOfNat 567517142600499089822104203853107), (Int.negOfNat 115599249378296981805685521673050), (Int.ofNat 2152696232027820804586355873043), (Int.ofNat 2827647765650269446525047812890), (Int.ofNat 114558993717664727723841723920), (Int.negOfNat 33750161370754779198045173428), (Int.negOfNat 2155544168855226874662004238), (Int.ofNat 250016231199432097688055094), (Int.ofNat 19607410498394399081569029), (Int.negOfNat 1274864382053009066232633), (Int.negOfNat 114733211776377473383062), (Int.ofNat 4762025805480385003396), (Int.ofNat 478683856758904223302), (Int.negOfNat 13282665351795687018), (Int.negOfNat 1589765199804518043), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(28590553123700870375400864722827/18014398509481984000000000000000), (62422939592546429471192399660113/11258999068426240000000000000000000), (-567517142600499089822104203853107/11258999068426240000000000000000000), (-2311984987565939636113710433461/225179981368524800000000000000000), (2152696232027820804586355873043/11258999068426240000000000000000000), (282764776565026944652504781289/1125899906842624000000000000000000), (1431987421470809096548021549/140737488355328000000000000000000), (-8437540342688694799511293357/2814749767106560000000000000000000), (-1077772084427613437331002119/5629499534213120000000000000000000), (125008115599716048844027547/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial149.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial149.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial149.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 14926611871661644218335977978471839), (Int.negOfNat 3294410993438249524928575149722620), (Int.negOfNat 980949570646333030288499354847904), (Int.ofNat 11875047524886278859233225006224), (Int.ofNat 26643844160338510746890999709251), (Int.ofNat 1016484254611204185816530454022), (Int.negOfNat 389736998012223431932933249374), (Int.negOfNat 22349581462564188027273030507), (Int.ofNat 3555082175102437526162293588), (Int.ofNat 238627872909026537474113003), (Int.negOfNat 22130467073106541747678262), (Int.negOfNat 1618413958129372585701103), (Int.ofNat 99854394073312091713720), (Int.ofNat 7721056262939071670440), (Int.negOfNat 340912253969940043545), (Int.negOfNat 27690732481107395157), (Int.ofNat 915589691250506479), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(14926611871661644218335977978471839/11258999068426240000000000000000000), (-164720549671912476246428757486131/562949953421312000000000000000000), (-30654674082697907196515604838997/351843720888320000000000000000000), (742190470305392428702076562889/703687441776640000000000000000000), (26643844160338510746890999709251/11258999068426240000000000000000000), (508242127305602092908265227011/5629499534213120000000000000000000), (-194868499006111715966466624687/5629499534213120000000000000000000), (-22349581462564188027273030507/11258999068426240000000000000000000), (888770543775609381540573397/2814749767106560000000000000000000), (238627872909026537474113003/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial149.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial149.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial149.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 4941023839042755792191346558727542), (Int.negOfNat 6222567583552138151104239666703462), (Int.negOfNat 290306463320553312269737223462463), (Int.ofNat 198069978821931326062076537120972), (Int.ofNat 11759689998949641120413488393444), (Int.negOfNat 3678044968073152807178492537527), (Int.negOfNat 235111649051923845136074714943), (Int.ofNat 42293847049465773175458448271), (Int.ofNat 2755037334623193611120999631), (Int.negOfNat 324881037959144023838769411), (Int.negOfNat 21187330784631468359298302), (Int.ofNat 1769986090709824434888875), (Int.ofNat 114721001461698594201695), (Int.negOfNat 7171078755515862547717), (Int.negOfNat 460266610598283126668), (Int.ofNat 22084006376052128703), (Int.ofNat 1600093786586792772), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(2470511919521377896095673279363771/5629499534213120000000000000000000), (-3111283791776069075552119833351731/5629499534213120000000000000000000), (-290306463320553312269737223462463/11258999068426240000000000000000000), (49517494705482831515519134280243/2814749767106560000000000000000000), (2939922499737410280103372098361/2814749767106560000000000000000000), (-3678044968073152807178492537527/11258999068426240000000000000000000), (-235111649051923845136074714943/11258999068426240000000000000000000), (42293847049465773175458448271/11258999068426240000000000000000000), (2755037334623193611120999631/11258999068426240000000000000000000), (-324881037959144023838769411/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial149.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial149.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial149.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 7019431998868995770388880793843572), (Int.negOfNat 4949094520285563543021543835897559), (Int.ofNat 861349239603133650169827879019429), (Int.ofNat 134042710663800139180766869106363), (Int.negOfNat 25707940590748575655283555342666), (Int.negOfNat 2477048820606520286702204807734), (Int.ofNat 407147311327952014174107481874), (Int.ofNat 30559113670330431749285818347), (Int.negOfNat 4022971480635473985633412252), (Int.negOfNat 259980206689125687892454016), (Int.ofNat 26976955688872159780756387), (Int.ofNat 1579272131041229880871572), (Int.negOfNat 130422496146626173434411), (Int.negOfNat 7095203528387449020631), (Int.ofNat 475523339590756300625), (Int.ofNat 24004418195183575475), (Int.negOfNat 1431555345086551222), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-1754857999717248942597220198460893/2814749767106560000000000000000000), (-4949094520285563543021543835897559/11258999068426240000000000000000000), (861349239603133650169827879019429/11258999068426240000000000000000000), (134042710663800139180766869106363/11258999068426240000000000000000000), (-12853970295374287827641777671333/5629499534213120000000000000000000), (-1238524410303260143351102403867/5629499534213120000000000000000000), (203573655663976007087053740937/5629499534213120000000000000000000), (30559113670330431749285818347/11258999068426240000000000000000000), (-1005742870158868496408353063/2814749767106560000000000000000000), (-2031095364758794436659797/87960930222080000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial149.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial149.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial149.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial149.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial149.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial149.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial149.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial149.reflect := by
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

end Bin149
end
end ErdosOverlap.OuterNumerics
