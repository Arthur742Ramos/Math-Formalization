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

/-! # Exact integer weighted outer models for source bin 154

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin154

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 1939027444180093700)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1917333829225837700)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 1843744128802102800)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 1404330785106973300)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 944669930831511200)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 603145553241675740)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 329982718927901400)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 133312660491984610)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial154.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial154.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9493917108202959000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 2733276928640499500)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1588014399424137200)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 919406169594710700)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 534894833879885300)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 236910911152685700)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 66257583475764215)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 15654212599703436)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 18316439541135913)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial154.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial154.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9493917108202959000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 2733276928640499500)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1588014399424137200)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 919406169594710700)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 534894833879885300)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 236910911152685700)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 66257583475764215)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 15654212599703436)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 18316439541135913)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial154.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial154.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial154.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 6220924589707714283849777536161516), (Int.ofNat 4856879891127287287061678349219443), (Int.ofNat 686165145513032842821590583279646), (Int.negOfNat 149848366403686279544532554848425), (Int.negOfNat 18850911008271187669743112226188), (Int.ofNat 2860349395076029805841373411634), (Int.ofNat 277355101892362091633800457414), (Int.negOfNat 34155032843850134046065889295), (Int.negOfNat 2599373422079516005570766709), (Int.ofNat 275156561980529470826439360), (Int.ofNat 16894889581767776849939516), (Int.negOfNat 1584622818898021676221352), (Int.negOfNat 80500318397062251617897), (Int.ofNat 6812508755512129067963), (Int.ofNat 293733922899456283810), (Int.negOfNat 22290411230039509331), (Int.negOfNat 870993171541305536), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1555231147426928570962444384040379/2814749767106560000000000000000000), (4856879891127287287061678349219443/11258999068426240000000000000000000), (343082572756516421410795291639823/5629499534213120000000000000000000), (-5993934656147451181781302193937/450359962737049600000000000000000), (-4712727752067796917435778056547/2814749767106560000000000000000000), (1430174697538014902920686705817/5629499534213120000000000000000000), (138677550946181045816900228707/5629499534213120000000000000000000), (-6831006568770026809213177859/2251799813685248000000000000000000), (-2599373422079516005570766709/11258999068426240000000000000000000), (859864256189154596332623/35184372088832000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial154.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial154.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial154.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial154 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 4841493555916488288722199467632775), (Int.ofNat 5464948867593048310930808332362427), (Int.negOfNat 396150336478485332776475465105606), (Int.negOfNat 163984844308715005985803157828823), (Int.ofNat 15181270964512298640097662196869), (Int.ofNat 2793479245309348306387263470098), (Int.negOfNat 276802203995888459631613494191), (Int.negOfNat 29474355710754210405360397148), (Int.ofNat 2981550200210466333765654679), (Int.ofNat 211391274618157523880708867), (Int.negOfNat 21380913791315427374806743), (Int.negOfNat 1097197128066280687764965), (Int.ofNat 109648556064469906576859), (Int.ofNat 4308212588490493694135), (Int.negOfNat 422809957987228631358), (Int.negOfNat 12991476483100287212), (Int.ofNat 1352091313136040758), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(193659742236659531548887978705311/450359962737049600000000000000000), (5464948867593048310930808332362427/11258999068426240000000000000000000), (-198075168239242666388237732552803/5629499534213120000000000000000000), (-163984844308715005985803157828823/11258999068426240000000000000000000), (15181270964512298640097662196869/11258999068426240000000000000000000), (1396739622654674153193631735049/5629499534213120000000000000000000), (-276802203995888459631613494191/11258999068426240000000000000000000), (-7368588927688552601340099287/2814749767106560000000000000000000), (2981550200210466333765654679/11258999068426240000000000000000000), (211391274618157523880708867/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial154.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial154.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial154.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial154 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 13186562648638880538838657579466388), (Int.ofNat 2558879062929558453708188366260426), (Int.negOfNat 872422099089898691075498380462874), (Int.ofNat 14528401912194901890396271190432), (Int.ofNat 22128084687534512212074044880837), (Int.negOfNat 1434877413669764441037696796070), (Int.negOfNat 294432280408832307102515776006), (Int.ofNat 25404690279075911269160089985), (Int.ofNat 2448006184698677338855632710), (Int.negOfNat 244641685577399764653924192), (Int.negOfNat 14052471448426277494883556), (Int.ofNat 1549922679466407595227608), (Int.ofNat 59296901651386736056731), (Int.negOfNat 7046294442958709719377), (Int.negOfNat 191717201030696295165), (Int.ofNat 24243783553680961058), (Int.ofNat 452738750524215793), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(3296640662159720134709664394866597/2814749767106560000000000000000000), (1279439531464779226854094183130213/5629499534213120000000000000000000), (-436211049544949345537749190231437/5629499534213120000000000000000000), (454012559756090684074883474701/351843720888320000000000000000000), (22128084687534512212074044880837/11258999068426240000000000000000000), (-143487741366976444103769679607/1125899906842624000000000000000000), (-147216140204416153551257888003/5629499534213120000000000000000000), (5080938055815182253832017997/2251799813685248000000000000000000), (244800618469867733885563271/1125899906842624000000000000000000), (-7645052674293742645435131/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial154.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial154.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial154.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial154 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 15223891405982142178934730072298277), (Int.negOfNat 206420010451358389071339653350001), (Int.negOfNat 419415532373045215839679729737614), (Int.ofNat 104201219558451469235989735321875), (Int.negOfNat 1136530323431385243130267373235), (Int.negOfNat 2294482915044252689590817766963), (Int.ofNat 148584054060557625346384113596), (Int.ofNat 24723552010609024756931488675), (Int.negOfNat 2275866630756128829720742851), (Int.negOfNat 165207566678454758389332115), (Int.ofNat 18913354695722144283739735), (Int.ofNat 759925075493230888832733), (Int.negOfNat 104514446175451178702646), (Int.negOfNat 2558534348526915419779), (Int.ofNat 419273338703764691977), (Int.ofNat 6117354448859782232), (Int.negOfNat 1297141994512633019), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(15223891405982142178934730072298277/11258999068426240000000000000000000), (-206420010451358389071339653350001/11258999068426240000000000000000000), (-209707766186522607919839864868807/5629499534213120000000000000000000), (33344390258704470155516715303/3602879701896396800000000000000), (-227306064686277048626053474647/2251799813685248000000000000000000), (-2294482915044252689590817766963/11258999068426240000000000000000000), (37146013515139406336596028399/2814749767106560000000000000000000), (988942080424360990277259547/450359962737049600000000000000000), (-2275866630756128829720742851/11258999068426240000000000000000000), (-33041513335690951677866423/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial154.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial154.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial154.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial154 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 13887418341148547757866792821012603), (Int.negOfNat 816599204280127515557594127526157), (Int.ofNat 42623163238625141182305548770290), (Int.ofNat 36292195158075445504145205264452), (Int.negOfNat 11186256114425003120288208447832), (Int.ofNat 376644829792227008637151373817), (Int.ofNat 197167169833289701887481449831), (Int.negOfNat 16053192065251577222340744525), (Int.negOfNat 1693429838267648435826874646), (Int.ofNat 194121243851920122158101902), (Int.ofNat 8878117403048067520327455), (Int.negOfNat 1359582666649961318866930), (Int.negOfNat 30914489523826074777507), (Int.ofNat 6506112115152997117827), (Int.ofNat 72811356460873375949), (Int.negOfNat 23354746446760140892), (Int.negOfNat 52800769048261963), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(13887418341148547757866792821012603/11258999068426240000000000000000000), (-816599204280127515557594127526157/11258999068426240000000000000000000), (4262316323862514118230554877029/1125899906842624000000000000000000), (9073048789518861376036301316113/2814749767106560000000000000000000), (-1398282014303125390036026055979/1407374883553280000000000000000000), (376644829792227008637151373817/11258999068426240000000000000000000), (197167169833289701887481449831/11258999068426240000000000000000000), (-642127682610063088893629781/450359962737049600000000000000000), (-846714919133824217913437323/5629499534213120000000000000000000), (97060621925960061079050951/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial154.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial154.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial154.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial154 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 12558358679732276277910808883080719), (Int.negOfNat 509021637937911837734368124620381), (Int.ofNat 56492981416228202539954437200083), (Int.negOfNat 17488757465493958195982266668967), (Int.negOfNat 1138247775725237341992757306083), (Int.ofNat 1057281761443682589298994070008), (Int.negOfNat 77463115551794962873338348980), (Int.negOfNat 13924461011100461129287619383), (Int.ofNat 1622740682878678060075543588), (Int.ofNat 90119368243806313861143784), (Int.negOfNat 15255618225792795057337556), (Int.negOfNat 329334438578172903758351), (Int.ofNat 89585023595830506564405), (Int.ofNat 590038843858159409526), (Int.negOfNat 371452106769515202666), (Int.ofNat 657064115541973708), (Int.ofNat 1242192675889225280), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(12558358679732276277910808883080719/11258999068426240000000000000000000), (-509021637937911837734368124620381/11258999068426240000000000000000000), (56492981416228202539954437200083/11258999068426240000000000000000000), (-17488757465493958195982266668967/11258999068426240000000000000000000), (-1138247775725237341992757306083/11258999068426240000000000000000000), (132160220180460323662374258751/1407374883553280000000000000000000), (-3873155777589748143666917449/562949953421312000000000000000000), (-13924461011100461129287619383/11258999068426240000000000000000000), (405685170719669515018885897/2814749767106560000000000000000000), (11264921030475789232642973/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial154.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial154.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial154.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial154 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 11635703983631738670612368874125849), (Int.negOfNat 464077572188084310688348080044258), (Int.negOfNat 15979138989431575421268851605967), (Int.negOfNat 1341077213193359403360195774121), (Int.ofNat 2861015541401453249327804934774), (Int.negOfNat 257113751285592679545642575872), (Int.negOfNat 81073835178034100070134600058), (Int.ofNat 10811767369122307186630875686), (Int.ofNat 730650171435188666137198350), (Int.negOfNat 145060148364033169177783499), (Int.negOfNat 2850571231425512425867484), (Int.ofNat 1080642379373577072034677), (Int.ofNat 957425205991755825536), (Int.negOfNat 5350564839018840980739), (Int.ofNat 45962986015764175209), (Int.ofNat 19836089009081900352), (Int.negOfNat 347137212427691867), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(11635703983631738670612368874125849/11258999068426240000000000000000000), (-232038786094042155344174040022129/5629499534213120000000000000000000), (-15979138989431575421268851605967/11258999068426240000000000000000000), (-1341077213193359403360195774121/11258999068426240000000000000000000), (1430507770700726624663902467387/5629499534213120000000000000000000), (-125543823869918300559395789/5497558138880000000000000000000), (-40536917589017050035067300029/5629499534213120000000000000000000), (5405883684561153593315437843/5629499534213120000000000000000000), (14613003428703773322743967/225179981368524800000000000000000), (-145060148364033169177783499/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial154.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial154.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial154.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial154 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 10666759486239966206664109354814138), (Int.negOfNat 483414869086959638651370537066028), (Int.ofNat 12515180773967279131444064671075), (Int.ofNat 4875225203811422506190989993084), (Int.negOfNat 1308216972307013634602369452699), (Int.negOfNat 279519629294724192364285925148), (Int.ofNat 60003750068859350834694438664), (Int.ofNat 4068503532514681052612116631), (Int.negOfNat 1156766571147372850433721563), (Int.negOfNat 15469722116165049591283676), (Int.ofNat 11257721569016678592810687), (Int.negOfNat 86595152983161869755503), (Int.negOfNat 68055474304916381962738), (Int.ofNat 1218321082278978707950), (Int.ofNat 285336997643382009646), (Int.negOfNat 6868423479410779468), (Int.negOfNat 1053930696773832931), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(5333379743119983103332054677407069/5629499534213120000000000000000000), (-120853717271739909662842634266507/2814749767106560000000000000000000), (500607230958691165257762586843/450359962737049600000000000000000), (1218806300952855626547747498271/2814749767106560000000000000000000), (-1308216972307013634602369452699/11258999068426240000000000000000000), (-69879907323681048091071481287/2814749767106560000000000000000000), (7500468758607418854336804833/1407374883553280000000000000000000), (4068503532514681052612116631/11258999068426240000000000000000000), (-1156766571147372850433721563/11258999068426240000000000000000000), (-3867430529041262397820919/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial154.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial154.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial154.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial154 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 9763184215017916595421593796787627), (Int.negOfNat 426897631380720701277298553975014), (Int.ofNat 3121423503515610087494869852142), (Int.negOfNat 6886275530406876160346223454731), (Int.negOfNat 582222917627849698681318098899), (Int.ofNat 314851108548497063511956934049), (Int.ofNat 9994566069740897648552051488), (Int.negOfNat 7798046209383551109616771887), (Int.ofNat 35003300369523777230440273), (Int.ofNat 99879395208706236745521244), (Int.negOfNat 2263220452771887253487825), (Int.negOfNat 751517100755062889818417), (Int.ofNat 24091453743499382648850), (Int.ofNat 3757748400467095175014), (Int.negOfNat 141196500837134194734), (Int.negOfNat 13883081394450411224), (Int.ofNat 577129654329389261), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(9763184215017916595421593796787627/11258999068426240000000000000000000), (-213448815690360350638649276987507/5629499534213120000000000000000000), (1560711751757805043747434926071/5629499534213120000000000000000000), (-6886275530406876160346223454731/11258999068426240000000000000000000), (-582222917627849698681318098899/11258999068426240000000000000000000), (314851108548497063511956934049/11258999068426240000000000000000000), (312330189679403051517251609/351843720888320000000000000000000), (-7798046209383551109616771887/11258999068426240000000000000000000), (35003300369523777230440273/11258999068426240000000000000000000), (24969848802176559186380311/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial154.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial154.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial154.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial154 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 8867241982339961728574917544678511), (Int.negOfNat 491818170650308000908578839844282), (Int.negOfNat 29345181381505856438326670263323), (Int.negOfNat 1180932366245945829275730648806), (Int.ofNat 1366516187056724036288475793813), (Int.negOfNat 40182706369265480835636822696), (Int.negOfNat 44740998599901938658887495294), (Int.ofNat 1946981476384568725081076170), (Int.ofNat 743030258579398312174418006), (Int.negOfNat 37684776461527663017893249), (Int.negOfNat 7039018956197466455769696), (Int.ofNat 392362280267745258787783), (Int.ofNat 42396341919674993923684), (Int.negOfNat 2521483605936280196785), (Int.negOfNat 177272091777572722431), (Int.ofNat 11186967884717595300), (Int.ofNat 750672496707591885), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(8867241982339961728574917544678511/11258999068426240000000000000000000), (-245909085325154000454289419922141/5629499534213120000000000000000000), (-29345181381505856438326670263323/11258999068426240000000000000000000), (-590466183122972914637865324403/5629499534213120000000000000000000), (1366516187056724036288475793813/11258999068426240000000000000000000), (-5022838296158185104454602837/1407374883553280000000000000000000), (-22370499299950969329443747647/5629499534213120000000000000000000), (194698147638456872508107617/1125899906842624000000000000000000), (371515129289699156087209003/5629499534213120000000000000000000), (-37684776461527663017893249/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial154.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial154.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial154.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial154 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 7774906325917147387726092052785872), (Int.negOfNat 589930899811168812610797063152902), (Int.negOfNat 15188246773670589059211142556968), (Int.ofNat 3116937006253339283954572523404), (Int.negOfNat 568096549016560670476544349720), (Int.negOfNat 198461391405484519041398408697), (Int.ofNat 24410168762563778000597407016), (Int.ofNat 4463285944376174214777864479), (Int.negOfNat 476164755087540454732447388), (Int.negOfNat 53646579030990881470855892), (Int.ofNat 5419018843322575243951956), (Int.ofNat 393109520949016448145851), (Int.negOfNat 39445251941822157737523), (Int.negOfNat 1921981981694618144310), (Int.ofNat 197651652907217386554), (Int.ofNat 6623384886573281384), (Int.negOfNat 655492996197966132), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(485931645369821711732880753299117/703687441776640000000000000000000), (-294965449905584406305398531576451/5629499534213120000000000000000000), (-1898530846708823632401392819621/1407374883553280000000000000000000), (779234251563334820988643130851/2814749767106560000000000000000000), (-14202413725414016761913608743/281474976710656000000000000000000), (-198461391405484519041398408697/11258999068426240000000000000000000), (3051271095320472250074675877/1407374883553280000000000000000000), (4463285944376174214777864479/11258999068426240000000000000000000), (-119041188771885113683111847/2814749767106560000000000000000000), (-13411644757747720367713973/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial154.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial154.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial154.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial154 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 6545777092361277205538674396999389), (Int.negOfNat 641230408201255407537294081483419), (Int.negOfNat 18169973442481276976413812110988), (Int.negOfNat 4007924325801463364472404929996), (Int.negOfNat 504038468178588157597674417524), (Int.ofNat 198809380355602732638456363604), (Int.ofNat 18942408821702024703618749517), (Int.negOfNat 4720236120742939398050851671), (Int.negOfNat 298151805674634266384873942), (Int.ofNat 63467085889422065005951686), (Int.ofNat 2668841667162539479049127), (Int.negOfNat 538424003922107075416850), (Int.negOfNat 15120888786823690600115), (Int.ofNat 3101432687120419970437), (Int.ofNat 58102783282576462589), (Int.negOfNat 12873981368282244540), (Int.negOfNat 350734515231638055), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(6545777092361277205538674396999389/11258999068426240000000000000000000), (-641230408201255407537294081483419/11258999068426240000000000000000000), (-4542493360620319244103453027747/2814749767106560000000000000000000), (-1001981081450365841118101232499/2814749767106560000000000000000000), (-126009617044647039399418604381/2814749767106560000000000000000000), (49702345088900683159614090901/2814749767106560000000000000000000), (18942408821702024703618749517/11258999068426240000000000000000000), (-4720236120742939398050851671/11258999068426240000000000000000000), (-149075902837317133192436971/5629499534213120000000000000000000), (31733542944711032502975843/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial154.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial154.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial154.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial154 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 5157436158711726227911322587924518), (Int.negOfNat 760859280202185259634340475854969), (Int.negOfNat 37262277049359999244403933096867), (Int.ofNat 123982604270080302974713017114), (Int.ofNat 1233272580561684728613610313951), (Int.ofNat 29106858568233588499939691247), (Int.negOfNat 37077770532164654618054003093), (Int.negOfNat 670328026512555617436033591), (Int.ofNat 622553376049978931820911645), (Int.ofNat 6907216137497829058975343), (Int.negOfNat 6353739526578271046874397), (Int.negOfNat 35426762651663423746473), (Int.ofNat 43007456563300540688902), (Int.ofNat 66828627858992711623), (Int.negOfNat 205157131314936619743), (Int.ofNat 466713240191362116), (Int.ofNat 600543677574558393), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(2578718079355863113955661293962259/5629499534213120000000000000000000), (-760859280202185259634340475854969/11258999068426240000000000000000000), (-37262277049359999244403933096867/11258999068426240000000000000000000), (61991302135040151487356508557/5629499534213120000000000000000000), (1233272580561684728613610313951/11258999068426240000000000000000000), (29106858568233588499939691247/11258999068426240000000000000000000), (-37077770532164654618054003093/11258999068426240000000000000000000), (-670328026512555617436033591/11258999068426240000000000000000000), (124510675209995786364182329/2251799813685248000000000000000000), (6907216137497829058975343/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial154.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial154.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial154.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial154 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 3506021857154718119589479776886648), (Int.negOfNat 873425048843412659057839889461871), (Int.negOfNat 12864322809104150184336192186626), (Int.ofNat 5904983438554485009122279793419), (Int.negOfNat 244528934049686087260469572574), (Int.negOfNat 227411358997116226232059401611), (Int.ofNat 8438961701346078681299316858), (Int.ofNat 5009895555562022628674909511), (Int.negOfNat 137247410004722657850586274), (Int.negOfNat 63599171946912757681485316), (Int.ofNat 1450418166968013722218132), (Int.ofNat 516822356992497512184772), (Int.negOfNat 10566872553221134894341), (Int.negOfNat 2893729362764084451807), (Int.ofNat 54706340535887756375), (Int.ofNat 11858108762924929754), (Int.negOfNat 49203466244315775), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(438252732144339764948684972110831/1407374883553280000000000000000000), (-873425048843412659057839889461871/11258999068426240000000000000000000), (-6432161404552075092168096093313/5629499534213120000000000000000000), (5904983438554485009122279793419/11258999068426240000000000000000000), (-122264467024843043630234786287/5629499534213120000000000000000000), (-227411358997116226232059401611/11258999068426240000000000000000000), (4219480850673039340649658429/5629499534213120000000000000000000), (5009895555562022628674909511/11258999068426240000000000000000000), (-68623705002361328925293137/5629499534213120000000000000000000), (-15899792986728189420371329/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial154.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial154.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial154.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial154 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 1744880849335289292203616887337139), (Int.negOfNat 876449890507015113364362435271333), (Int.ofNat 3387079159083190665334258063754), (Int.negOfNat 1537650624747520499114522581942), (Int.negOfNat 980670119492905994487260484781), (Int.ofNat 130027443327463079576014230323), (Int.ofNat 31790653648494125681326160845), (Int.negOfNat 2767064423737561866828863396), (Int.negOfNat 522451721551729431459344077), (Int.ofNat 34192303934303096807854685), (Int.ofNat 5234800448755535541435609), (Int.negOfNat 276470920904585526125795), (Int.negOfNat 35020731575785187041049), (Int.ofNat 1562357197978445781661), (Int.ofNat 166004314951227757382), (Int.negOfNat 6923857255149318136), (Int.negOfNat 545594358951150654), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(1744880849335289292203616887337139/11258999068426240000000000000000000), (-876449890507015113364362435271333/11258999068426240000000000000000000), (1693539579541595332667129031877/5629499534213120000000000000000000), (-768825312373760249557261290971/5629499534213120000000000000000000), (-980670119492905994487260484781/11258999068426240000000000000000000), (130027443327463079576014230323/11258999068426240000000000000000000), (6358130729698825136265232169/2251799813685248000000000000000000), (-691766105934390466707215849/2814749767106560000000000000000000), (-522451721551729431459344077/11258999068426240000000000000000000), (6838460786860619361570937/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial154.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial154.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial154.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial154 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 16732821301270961573769712711240), (Int.negOfNat 897901752819597437383657740202035), (Int.negOfNat 13930640076689366829206181248930), (Int.negOfNat 1332030101106079218909665851691), (Int.ofNat 1059943367531777828846717448325), (Int.ofNat 145104605280140842095967850592), (Int.negOfNat 30604583783349014081181983290), (Int.negOfNat 3293383032977810337086739861), (Int.ofNat 482366617534181537451721135), (Int.ofNat 42195922906351389779158648), (Int.negOfNat 4709449527704881666187592), (Int.negOfNat 346896565024731721137628), (Int.ofNat 31015017952207345606495), (Int.ofNat 1969055258254919214561), (Int.negOfNat 146274441891641754390), (Int.negOfNat 8352139168450502461), (Int.ofNat 430825008179133692), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-418320532531774039344242817781/281474976710656000000000000000000), (-179580350563919487476731548040407/2251799813685248000000000000000000), (-1393064007668936682920618124893/1125899906842624000000000000000000), (-1332030101106079218909665851691/11258999068426240000000000000000000), (42397734701271113153868697933/450359962737049600000000000000000), (4534518915004401315498995331/351843720888320000000000000000000), (-3060458378334901408118198329/1125899906842624000000000000000000), (-3293383032977810337086739861/11258999068426240000000000000000000), (96473323506836307490344227/2251799813685248000000000000000000), (5274490363293923722394831/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial154.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial154.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial154.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial154 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 1859553235419398206337318771392646), (Int.negOfNat 930869642313250746341632476531674), (Int.ofNat 6563103453394883840927020020399), (Int.ofNat 7218877632057556013925024205754), (Int.ofNat 389486066526637307464095620996), (Int.negOfNat 242238582784029894287726246900), (Int.negOfNat 13145629902710439943216435690), (Int.ofNat 5075982922730701250584242179), (Int.ofNat 230125445364476937278917905), (Int.negOfNat 62306302598377768554764532), (Int.negOfNat 2463311027138919583096508), (Int.ofNat 493892874279774584312952), (Int.ofNat 17488397943693137975105), (Int.negOfNat 2718498544542895866859), (Int.negOfNat 87520157233553874930), (Int.ofNat 11230029421156154579), (Int.ofNat 242336158884909608), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-929776617709699103168659385696323/5629499534213120000000000000000000), (-465434821156625373170816238265837/5629499534213120000000000000000000), (6563103453394883840927020020399/11258999068426240000000000000000000), (3609438816028778006962512102877/5629499534213120000000000000000000), (97371516631659326866023905249/2814749767106560000000000000000000), (-2422385827840298942877262469/112589990684262400000000000000000), (-1314562990271043994321643569/1125899906842624000000000000000000), (5075982922730701250584242179/11258999068426240000000000000000000), (46025089072895387455783581/2251799813685248000000000000000000), (-15576575649594442138691133/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial154.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial154.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial154.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial154 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 3638974988608719462017093636368939), (Int.negOfNat 825070826392928278551543001603610), (Int.ofNat 40212590539951947423016057553150), (Int.ofNat 1446054204251698396142718366235), (Int.negOfNat 1404922098804022816005527268226), (Int.negOfNat 554319949247306557206893396), (Int.ofNat 41247028114756207570837946415), (Int.ofNat 154360604656656182231009264), (Int.negOfNat 663450106619577176273921983), (Int.negOfNat 5076369889088275299905995), (Int.ofNat 6528018767892861290174751), (Int.ofNat 66614185425209643722565), (Int.negOfNat 42926023288472518354251), (Int.negOfNat 499992236998030508439), (Int.ofNat 200945806138344617038), (Int.ofNat 2932964280597952364), (Int.negOfNat 660817450080831086), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-3638974988608719462017093636368939/11258999068426240000000000000000000), (-82507082639292827855154300160361/1125899906842624000000000000000000), (804251810799038948460321151063/225179981368524800000000000000000), (289210840850339679228543673247/2251799813685248000000000000000000), (-702461049402011408002763634113/5629499534213120000000000000000000), (-138579987311826639301723349/2814749767106560000000000000000000), (8249405622951241514167589283/2251799813685248000000000000000000), (9647537791041011389438079/703687441776640000000000000000000), (-663450106619577176273921983/11258999068426240000000000000000000), (-1015273977817655059981199/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial154.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial154.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial154.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial154 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 5136700567263360820891071169279855), (Int.negOfNat 684539036920734971455422225720974), (Int.ofNat 23991335719237388652071297535046), (Int.negOfNat 4247468307416117937736027713969), (Int.ofNat 429180763984651290955661114914), (Int.ofNat 250219219963246656718328316850), (Int.negOfNat 13883916166046290402076145618), (Int.negOfNat 5627812897626922797617732869), (Int.ofNat 185924286453566075738206294), (Int.ofNat 71506754489407212110537864), (Int.negOfNat 1385409253728932476817252), (Int.negOfNat 577410588656681306488808), (Int.ofNat 6342896193725880617661), (Int.ofNat 3207635584155185231073), (Int.negOfNat 19228835430701364515), (Int.negOfNat 13183401744797606306), (Int.ofNat 175918262132180135), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-1027340113452672164178214233855971/2251799813685248000000000000000000), (-342269518460367485727711112860487/5629499534213120000000000000000000), (11995667859618694326035648767523/5629499534213120000000000000000000), (-4247468307416117937736027713969/11258999068426240000000000000000000), (214590381992325645477830557457/5629499534213120000000000000000000), (5004384399264933134366566337/225179981368524800000000000000000), (-6941958083023145201038072809/5629499534213120000000000000000000), (-5627812897626922797617732869/11258999068426240000000000000000000), (92962143226783037869103147/5629499534213120000000000000000000), (8938344311175901513817233/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial154.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial154.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial154.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial154 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 6430446409686975647870019205053558), (Int.negOfNat 610637101504660246229355045217801), (Int.ofNat 22341754725272409894315473499906), (Int.ofNat 4495288494052138302284428058047), (Int.ofNat 978015279420105510020090328904), (Int.negOfNat 188274542499846827905304397854), (Int.negOfNat 35954962464882725038486400410), (Int.ofNat 3749858007249012375153071609), (Int.ofNat 630229897160057440815238455), (Int.negOfNat 40411258713661471178010157), (Int.negOfNat 6503134918893999821433843), (Int.ofNat 273109922503839306880667), (Int.ofNat 44037248395051161519038), (Int.negOfNat 1262686384082678001517), (Int.negOfNat 209219047847164183457), (Int.ofNat 3941157753642552616), (Int.ofNat 605868131457423347), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-3215223204843487823935009602526779/5629499534213120000000000000000000), (-610637101504660246229355045217801/11258999068426240000000000000000000), (11170877362636204947157736749953/5629499534213120000000000000000000), (4495288494052138302284428058047/11258999068426240000000000000000000), (122251909927513188752511291113/1407374883553280000000000000000000), (-94137271249923413952652198927/5629499534213120000000000000000000), (-3595496246488272503848640041/1125899906842624000000000000000000), (3749858007249012375153071609/11258999068426240000000000000000000), (126045979432011488163047691/2251799813685248000000000000000000), (-40411258713661471178010157/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial154.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial154.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial154.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial154 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 7518454247312707003133306195609840), (Int.negOfNat 455792491012840018984487241170289), (Int.ofNat 52493235523884501428861003668519), (Int.ofNat 1963769922339525217793375541467), (Int.negOfNat 1540094112279490786837498518728), (Int.negOfNat 144385565778875338264658678010), (Int.ofNat 44341619074710799835571589893), (Int.ofNat 4109533842376962491782806709), (Int.negOfNat 645081903756007644902814358), (Int.negOfNat 58447903254220494575677774), (Int.ofNat 5619134520902903376641853), (Int.ofNat 504769702279713268577130), (Int.negOfNat 32485001552257562963285), (Int.negOfNat 2927867947931081851523), (Int.ofNat 132946429665399051131), (Int.ofNat 12294364637876786140), (Int.negOfNat 575856243608133965), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-93980678091408837539166327445123/140737488355328000000000000000000), (-455792491012840018984487241170289/11258999068426240000000000000000000), (52493235523884501428861003668519/11258999068426240000000000000000000), (1963769922339525217793375541467/11258999068426240000000000000000000), (-192511764034936348354687314841/1407374883553280000000000000000000), (-14438556577887533826465867801/1125899906842624000000000000000000), (44341619074710799835571589893/11258999068426240000000000000000000), (4109533842376962491782806709/11258999068426240000000000000000000), (-322540951878003822451407179/5629499534213120000000000000000000), (-29223951627110247287838887/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial154.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial154.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial154.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial154 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 8230442520832090770731667885098301), (Int.negOfNat 273495213028635234908571976520519), (Int.ofNat 27817374536262624986518933851700), (Int.negOfNat 8103375614695660881470347433206), (Int.negOfNat 39115473410584398063245179877), (Int.ofNat 382236552383280138343759518132), (Int.ofNat 14257119798129904466956705404), (Int.negOfNat 7637991905051540898223915001), (Int.negOfNat 363366985930210507546807892), (Int.ofNat 85957350069682304940439388), (Int.ofNat 4465845923156076667526964), (Int.negOfNat 615815994242273967618049), (Int.negOfNat 33520056103414572905997), (Int.ofNat 3038256068578865059770), (Int.ofNat 171324284471093640746), (Int.negOfNat 10715576318044308556), (Int.negOfNat 550918812834015608), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-8230442520832090770731667885098301/11258999068426240000000000000000000), (-273495213028635234908571976520519/11258999068426240000000000000000000), (278173745362626249865189338517/112589990684262400000000000000000), (-4051687807347830440735173716603/5629499534213120000000000000000000), (-39115473410584398063245179877/11258999068426240000000000000000000), (95559138095820034585939879533/2814749767106560000000000000000000), (3564279949532476116739176351/2814749767106560000000000000000000), (-7637991905051540898223915001/11258999068426240000000000000000000), (-90841746482552626886701973/2814749767106560000000000000000000), (21489337517420576235109847/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial154.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial154.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial154.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial154 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 8719495748816896854199711658336581), (Int.negOfNat 230982205498843107162216415411203), (Int.ofNat 6903567860619707693428312264152), (Int.ofNat 4727781124968479306356977569218), (Int.ofNat 2470662183826372455918274901868), (Int.negOfNat 62224320373490799342725012365), (Int.negOfNat 70923653827172208063959010166), (Int.negOfNat 500282555985221234096581170), (Int.ofNat 1056606191883044301788728454), (Int.ofNat 22274005174746785736183571), (Int.negOfNat 9533209841249670851938724), (Int.negOfNat 273504659560475099601077), (Int.ofNat 56902063385754828460256), (Int.ofNat 1883667780765480316835), (Int.negOfNat 240858554794363839289), (Int.negOfNat 8775707200198545600), (Int.ofNat 975794225084087795), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-8719495748816896854199711658336581/11258999068426240000000000000000000), (-230982205498843107162216415411203/11258999068426240000000000000000000), (862945982577463461678539033019/1407374883553280000000000000000000), (2363890562484239653178488784609/5629499534213120000000000000000000), (617665545956593113979568725467/2814749767106560000000000000000000), (-12444864074698159868545002473/2251799813685248000000000000000000), (-35461826913586104031979505083/5629499534213120000000000000000000), (-50028255598522123409658117/1125899906842624000000000000000000), (528303095941522150894364227/5629499534213120000000000000000000), (22274005174746785736183571/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial154.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial154.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial154.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial154 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 9082815555026258290795628194551702), (Int.negOfNat 85309921687870508841237646237842), (Int.ofNat 74112938214599744145708522640911), (Int.ofNat 12238132914961199617662956275502), (Int.negOfNat 1405915082418920624848403130427), (Int.negOfNat 515907269445338290839495663465), (Int.ofNat 22883818132221456320672254602), (Int.ofNat 10550879371294333144723055253), (Int.negOfNat 141803092644562621218259733), (Int.negOfNat 123803318971861442301189196), (Int.negOfNat 463934590301052197463195), (Int.ofNat 911018577579987923392303), (Int.ofNat 12155049601754879363530), (Int.negOfNat 4573053240661012820046), (Int.negOfNat 86162766417129653726), (Int.ofNat 16926935681913114316), (Int.ofNat 362656833718623259), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-4541407777513129145397814097275851/5629499534213120000000000000000000), (-42654960843935254420618823118921/5629499534213120000000000000000000), (74112938214599744145708522640911/11258999068426240000000000000000000), (6119066457480599808831478137751/5629499534213120000000000000000000), (-1405915082418920624848403130427/11258999068426240000000000000000000), (-103181453889067658167899132693/2251799813685248000000000000000000), (11441909066110728160336127301/5629499534213120000000000000000000), (10550879371294333144723055253/11258999068426240000000000000000000), (-141803092644562621218259733/11258999068426240000000000000000000), (-30950829742965360575297299/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial154.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial154.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial154.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial154 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 8895365465975491616973075564154335), (Int.ofNat 280435535637283005159334462852631), (Int.ofNat 84305285838790510656136466770172), (Int.negOfNat 10963900141616899516131939435211), (Int.negOfNat 2863634990980498545002276400647), (Int.ofNat 354743107912640966801064288346), (Int.ofNat 83120399717847067924351085236), (Int.negOfNat 5384320117974873297915595629), (Int.negOfNat 1345543993572786823671611977), (Int.ofNat 36471025058046462348542884), (Int.ofNat 12613607822037866327305333), (Int.negOfNat 97950083603586099293583), (Int.negOfNat 76373977526671240320042), (Int.negOfNat 199826965915109722310), (Int.ofNat 324750083018197261214), (Int.ofNat 2822699585567056472), (Int.negOfNat 1205786666985785189), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-1779073093195098323394615112830867/2251799813685248000000000000000000), (280435535637283005159334462852631/11258999068426240000000000000000000), (21076321459697627664034116692543/2814749767106560000000000000000000), (-10963900141616899516131939435211/11258999068426240000000000000000000), (-2863634990980498545002276400647/11258999068426240000000000000000000), (177371553956320483400532144173/5629499534213120000000000000000000), (20780099929461766981087771309/2814749767106560000000000000000000), (-5384320117974873297915595629/11258999068426240000000000000000000), (-1345543993572786823671611977/11258999068426240000000000000000000), (9117756264511615587135721/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial154.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial154.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial154.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial154 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 8115133699741222317800984734452088), (Int.ofNat 435147768000327051743140503147347), (Int.negOfNat 7600951035646487084422049032229), (Int.negOfNat 11433168173976407905166978948506), (Int.ofNat 2959424313620817720531312559517), (Int.ofNat 461971443494364475415721229532), (Int.negOfNat 81830370559558793027379515782), (Int.negOfNat 11885418188201822021327098754), (Int.ofNat 900386494049460310979492090), (Int.ofNat 150706467765791308725674421), (Int.negOfNat 5213139532166842820678396), (Int.negOfNat 1128708234198351304326983), (Int.ofNat 17490876695392540174524), (Int.ofNat 5676099418989389969681), (Int.negOfNat 29453551467773259889), (Int.negOfNat 21245480087219930148), (Int.negOfNat 59398633652382213), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-1014391712467652789725123091806511/1407374883553280000000000000000000), (435147768000327051743140503147347/11258999068426240000000000000000000), (-7600951035646487084422049032229/11258999068426240000000000000000000), (-5716584086988203952583489474253/5629499534213120000000000000000000), (2959424313620817720531312559517/11258999068426240000000000000000000), (115492860873591118853930307383/2814749767106560000000000000000000), (-40915185279779396513689757891/5629499534213120000000000000000000), (-5942709094100911010663549377/5629499534213120000000000000000000), (90038649404946031097949209/1125899906842624000000000000000000), (150706467765791308725674421/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial154.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial154.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial154.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial154 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 7311031787532662520815555597502278), (Int.ofNat 379399682798738702417550341386767), (Int.ofNat 6375817099151507572334172640351), (Int.ofNat 13271902532860999311824532690877), (Int.ofNat 843945850731944471672593823216), (Int.negOfNat 883033407446089643822818390453), (Int.negOfNat 78105206606547094118083012140), (Int.ofNat 14278529348712414861770024337), (Int.ofNat 1534886164366529633268982392), (Int.negOfNat 114406633931165583207475836), (Int.negOfNat 14785131187805303535954664), (Int.ofNat 563337524172652986005749), (Int.ofNat 89125306344305501941515), (Int.negOfNat 1880238203829488767194), (Int.negOfNat 376472964292785202234), (Int.ofNat 4436996922310073368), (Int.ofNat 1284150008854362060), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-3655515893766331260407777798751139/5629499534213120000000000000000000), (379399682798738702417550341386767/11258999068426240000000000000000000), (6375817099151507572334172640351/11258999068426240000000000000000000), (13271902532860999311824532690877/11258999068426240000000000000000000), (52746615670746529479537113951/703687441776640000000000000000000), (-883033407446089643822818390453/11258999068426240000000000000000000), (-3905260330327354705904150607/562949953421312000000000000000000), (14278529348712414861770024337/11258999068426240000000000000000000), (191860770545816204158622799/1407374883553280000000000000000000), (-28601658482791395801868959/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial154.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial154.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial154.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial154 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 6438158238056865034843498642923886), (Int.ofNat 513170782545502119275354046676177), (Int.ofNat 28543640153775476561153919424794), (Int.negOfNat 17857340733218098402684170152245), (Int.negOfNat 7581603820883199304002669576829), (Int.negOfNat 258431393406223005926067432865), (Int.ofNat 180059088471844704451130647646), (Int.ofNat 13043551266506650889979965555), (Int.negOfNat 1878779774332245457646267954), (Int.negOfNat 171915489323415149774439658), (Int.ofNat 11787948004867746772446665), (Int.ofNat 1264926704864797880723850), (Int.negOfNat 50735507611269138991893), (Int.negOfNat 6239350767219569939333), (Int.ofNat 160432720955053025531), (Int.ofNat 22932493570784579388), (Int.negOfNat 340539347823571617), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-3219079119028432517421749321461943/5629499534213120000000000000000000), (513170782545502119275354046676177/11258999068426240000000000000000000), (14271820076887738280576959712397/5629499534213120000000000000000000), (-3571468146643619680536834030449/2251799813685248000000000000000000), (-7581603820883199304002669576829/11258999068426240000000000000000000), (-51686278681244601185213486573/2251799813685248000000000000000000), (90029544235922352225565323823/5629499534213120000000000000000000), (2608710253301330177995993111/2251799813685248000000000000000000), (-939389887166122728823133977/5629499534213120000000000000000000), (-85957744661707574887219829/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial154.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial154.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial154.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial154 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 5557437530225475228241723605036774), (Int.ofNat 187939359832123723130227311061367), (Int.negOfNat 233245849460411328454318117077533), (Int.negOfNat 56797464452817737605077128170287), (Int.ofNat 1695796391890521758005913368328), (Int.ofNat 1935150563344826102618842350888), (Int.ofNat 90832442191957149210506834117), (Int.negOfNat 25644232120651307300311120125), (Int.negOfNat 1793040362505480735031222149), (Int.ofNat 198047467117118099316455585), (Int.ofNat 16345847339955158845160905), (Int.negOfNat 1037931681658145769455327), (Int.negOfNat 94562924078156878639694), (Int.ofNat 3999503601083552990281), (Int.ofNat 389166693035629668023), (Int.negOfNat 11527095049074716868), (Int.negOfNat 1229200690230954321), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-2778718765112737614120861802518387/5629499534213120000000000000000000), (187939359832123723130227311061367/11258999068426240000000000000000000), (-233245849460411328454318117077533/11258999068426240000000000000000000), (-56797464452817737605077128170287/11258999068426240000000000000000000), (211974548986315219750739171041/1407374883553280000000000000000000), (241893820418103262827355293861/1407374883553280000000000000000000), (90832442191957149210506834117/11258999068426240000000000000000000), (-205153856965210458402488961/90071992547409920000000000000000), (-1793040362505480735031222149/11258999068426240000000000000000000), (39609493423423619863291117/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial154.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial154.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial154.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial154 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 6477676903362146495469823346637965), (Int.negOfNat 1212894711329601535217636185407796), (Int.negOfNat 376099684645488612162277159161964), (Int.ofNat 32396937259269245256742456391622), (Int.ofNat 18272870037356045563793801092645), (Int.ofNat 560212951614530220595554076478), (Int.negOfNat 300796134113783272898861518774), (Int.negOfNat 17414696994733845331361754795), (Int.ofNat 2821237961881743781939688570), (Int.ofNat 195528463186185270166623088), (Int.negOfNat 17734570995670089309044924), (Int.negOfNat 1322707670425565164314772), (Int.ofNat 81075353656889152543149), (Int.ofNat 6213520661842216118703), (Int.negOfNat 283168313331696191095), (Int.negOfNat 21916620965427264602), (Int.ofNat 740477329299525447), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-1295535380672429299093964669327593/2251799813685248000000000000000000), (-303223677832400383804409046351949/2814749767106560000000000000000000), (-94024921161372153040569289790491/2814749767106560000000000000000000), (16198468629634622628371228195811/5629499534213120000000000000000000), (3654574007471209112758760218529/2251799813685248000000000000000000), (280106475807265110297777038239/5629499534213120000000000000000000), (-150398067056891636449430759387/5629499534213120000000000000000000), (-3482939398946769066272350959/2251799813685248000000000000000000), (282123796188174378193968857/1125899906842624000000000000000000), (12220528949136579385413943/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial154.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial154.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial154.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial154 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 9859075009213853527942944741230419), (Int.negOfNat 1761299936278534901135082043674305), (Int.ofNat 223475560495558780886789326975342), (Int.ofNat 148898053277376457766793351978478), (Int.ofNat 4617253628362321530118820003106), (Int.negOfNat 3026279590109253961773545405326), (Int.negOfNat 170477891515168066885934778669), (Int.ofNat 34454545452930320400431885112), (Int.ofNat 2231395498167356059058803181), (Int.negOfNat 260045801097079112103716913), (Int.negOfNat 17318377198021883377060317), (Int.ofNat 1408742602817041155313795), (Int.ofNat 92090793563923588882441), (Int.negOfNat 5751089137083133339965), (Int.negOfNat 360876094019593568662), (Int.ofNat 17984239064032672888), (Int.ofNat 1174251371607546582), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-9859075009213853527942944741230419/11258999068426240000000000000000000), (-352259987255706980227016408734861/2251799813685248000000000000000000), (111737780247779390443394663487671/5629499534213120000000000000000000), (74449026638688228883396675989239/5629499534213120000000000000000000), (2308626814181160765059410001553/5629499534213120000000000000000000), (-1513139795054626980886772702663/5629499534213120000000000000000000), (-170477891515168066885934778669/11258999068426240000000000000000000), (4306818181616290050053985639/1407374883553280000000000000000000), (2231395498167356059058803181/11258999068426240000000000000000000), (-260045801097079112103716913/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial154.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial154.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial154.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial154 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 11325629935914506494071512300542732), (Int.ofNat 809347497176864365019872052479328), (Int.ofNat 970460081082720314827872451982715), (Int.ofNat 59205589389675979954712432963528), (Int.negOfNat 24940285621901241378367939297676), (Int.negOfNat 1793285448718172953699352170476), (Int.ofNat 353648181866765417783992043579), (Int.ofNat 25102126881922958500897727445), (Int.negOfNat 3266033221161584063629172331), (Int.negOfNat 216197866894765884747233120), (Int.ofNat 21227606535899719553537784), (Int.ofNat 1280900084313336279568428), (Int.negOfNat 101964199057701869859703), (Int.negOfNat 5566106663224870807057), (Int.ofNat 375690005759619395110), (Int.ofNat 18410651370952837309), (Int.negOfNat 1122098871234343364), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-2831407483978626623517878075135683/2814749767106560000000000000000000), (25292109286777011406871001639979/351843720888320000000000000000000), (194092016216544062965574490396543/2251799813685248000000000000000000), (7400698673709497494339054120441/1407374883553280000000000000000000), (-6235071405475310344591984824419/2814749767106560000000000000000000), (-448321362179543238424838042619/2814749767106560000000000000000000), (353648181866765417783992043579/11258999068426240000000000000000000), (5020425376384591700179545489/2251799813685248000000000000000000), (-3266033221161584063629172331/11258999068426240000000000000000000), (-1351236668092286779670207/70368744177664000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial154.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial154.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial154.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial154.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial154 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial154 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial154 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 12363046198877544312071156947749864), (Int.negOfNat 1080736052422446614647599129895863), (Int.ofNat 987829785964427881596156109323354), (Int.negOfNat 57690948551927728265929966929155), (Int.negOfNat 24988756465356357228497141179612), (Int.ofNat 1790749449881794281849116556446), (Int.ofNat 353702285783606218047824996166), (Int.negOfNat 25100104937787210378030928045), (Int.negOfNat 3266065573834490208492556831), (Int.ofNat 216196926466455457401788620), (Int.ofNat 21227618170064384634099984), (Int.negOfNat 1280900084313336279568428), (Int.negOfNat 101964199057701869859703), (Int.ofNat 5566106663224870807057), (Int.ofNat 375690005759619395110), (Int.negOfNat 18410651370952837309), (Int.negOfNat 1122098871234343364), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1545380774859693039008894618468733/1407374883553280000000000000000000), (-1080736052422446614647599129895863/11258999068426240000000000000000000), (493914892982213940798078054661677/5629499534213120000000000000000000), (-11538189710385545653185993385831/2251799813685248000000000000000000), (-6247189116339089307124285294903/2814749767106560000000000000000000), (895374724940897140924558278223/5629499534213120000000000000000000), (176851142891803109023912498083/5629499534213120000000000000000000), (-5020020987557442075606185609/2251799813685248000000000000000000), (-3266065573834490208492556831/11258999068426240000000000000000000), (10809846323322772870089431/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial154.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial154.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial154.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 11358525409188618057013621141122555), (Int.ofNat 1575823202267287598897051711060013), (Int.ofNat 248581211777669440380954373603666), (Int.negOfNat 147862893060194789032654233563137), (Int.ofNat 4547195322746065191596612020871), (Int.ofNat 3024546396970774601159877585662), (Int.negOfNat 170399691333345535820852195669), (Int.negOfNat 34453163583692923570675549412), (Int.ofNat 2231348736581512211919133981), (Int.ofNat 260045159278995088492702213), (Int.negOfNat 17318359746774885756217017), (Int.negOfNat 1408742602817041155313795), (Int.ofNat 92090793563923588882441), (Int.ofNat 5751089137083133339965), (Int.negOfNat 360876094019593568662), (Int.negOfNat 17984239064032672888), (Int.ofNat 1174251371607546582), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-2271705081837723611402724228224511/2251799813685248000000000000000000), (1575823202267287598897051711060013/11258999068426240000000000000000000), (124290605888834720190477186801833/5629499534213120000000000000000000), (-147862893060194789032654233563137/11258999068426240000000000000000000), (4547195322746065191596612020871/11258999068426240000000000000000000), (1512273198485387300579938792831/5629499534213120000000000000000000), (-170399691333345535820852195669/11258999068426240000000000000000000), (-8613290895923230892668887353/2814749767106560000000000000000000), (2231348736581512211919133981/11258999068426240000000000000000000), (260045159278995088492702213/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial154.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial154.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial154.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 8240548110154763972339109084764308), (Int.ofNat 1137897568061073800088592888699134), (Int.negOfNat 346583516738938241654553799669506), (Int.negOfNat 31978372313459973180596013678252), (Int.ofNat 18190504011929566464846442505103), (Int.negOfNat 560913764764681785295855694710), (Int.negOfNat 300704195861805729547089855334), (Int.ofNat 17415255750699242599702627895), (Int.ofNat 2821182984636618943743012470), (Int.negOfNat 195528723015862790299178888), (Int.negOfNat 17734549666368203328014224), (Int.ofNat 1322707670425565164314772), (Int.ofNat 81075353656889152543149), (Int.negOfNat 6213520661842216118703), (Int.negOfNat 283168313331696191095), (Int.ofNat 21916620965427264602), (Int.ofNat 740477329299525447), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-2060137027538690993084777271191077/2814749767106560000000000000000000), (568948784030536900044296444349567/5629499534213120000000000000000000), (-173291758369469120827276899834753/5629499534213120000000000000000000), (-7994593078364993295149003419563/2814749767106560000000000000000000), (18190504011929566464846442505103/11258999068426240000000000000000000), (-56091376476468178529585569471/1125899906842624000000000000000000), (-150352097930902864773544927667/5629499534213120000000000000000000), (3483051150139848519940525579/2251799813685248000000000000000000), (282118298463661894374301247/1125899906842624000000000000000000), (-24441090376982848787397361/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial154.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial154.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial154.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 7350224173407193949021992175439937), (Int.negOfNat 142522984312667245893430378984539), (Int.negOfNat 203228800354792180286660924349306), (Int.ofNat 56543992094727145840131548563385), (Int.ofNat 1612032637803208172923937122815), (Int.negOfNat 1934726168604474076123208761377), (Int.ofNat 90925940610002174647227924004), (Int.ofNat 25643893752606188097240095325), (Int.negOfNat 1793096272422806223852967949), (Int.negOfNat 198047310055895120728865885), (Int.ofNat 16345868669257044826191605), (Int.ofNat 1037931681658145769455327), (Int.negOfNat 94562924078156878639694), (Int.negOfNat 3999503601083552990281), (Int.ofNat 389166693035629668023), (Int.ofNat 11527095049074716868), (Int.negOfNat 1229200690230954321), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-7350224173407193949021992175439937/11258999068426240000000000000000000), (-142522984312667245893430378984539/11258999068426240000000000000000000), (-101614400177396090143330462174653/5629499534213120000000000000000000), (11308798418945429168026309712677/2251799813685248000000000000000000), (322406527560641634584787424563/2251799813685248000000000000000000), (-1934726168604474076123208761377/11258999068426240000000000000000000), (22731485152500543661806981001/2814749767106560000000000000000000), (1025755750104247523889603813/450359962737049600000000000000000), (-1793096272422806223852967949/11258999068426240000000000000000000), (-39609462011179024145773177/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial154.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial154.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial154.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 8023392425699161588069060465031663), (Int.negOfNat 353356624128079212793406559047743), (Int.ofNat 55085589601812239639195931463710), (Int.ofNat 16965405365569109778649983648008), (Int.negOfNat 7655670172934700555552738683788), (Int.ofNat 259924781805140084726477035143), (Int.ofNat 180141762498157778467596800569), (Int.negOfNat 13044741941820969229957200155), (Int.negOfNat 1878829211775962273315243154), (Int.ofNat 171916043885264185281237858), (Int.ofNat 11787965456114744393289965), (Int.negOfNat 1264926704864797880723850), (Int.negOfNat 50735507611269138991893), (Int.ofNat 6239350767219569939333), (Int.ofNat 160432720955053025531), (Int.negOfNat 22932493570784579388), (Int.negOfNat 340539347823571617), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-8023392425699161588069060465031663/11258999068426240000000000000000000), (-353356624128079212793406559047743/11258999068426240000000000000000000), (5508558960181223963919593146371/1125899906842624000000000000000000), (2120675670696138722331247956001/1407374883553280000000000000000000), (-1913917543233675138888184670947/2814749767106560000000000000000000), (259924781805140084726477035143/11258999068426240000000000000000000), (180141762498157778467596800569/11258999068426240000000000000000000), (-2608948388364193845991440031/2251799813685248000000000000000000), (-939414605887981136657621577/5629499534213120000000000000000000), (85958021942632092640618929/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial154.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial154.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial154.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 8478737490315737842692895953861739), (Int.negOfNat 126356312459084291088859436579259), (Int.ofNat 25926988764946250794789025663897), (Int.negOfNat 14684157453147872912086725517793), (Int.ofNat 789387538568000987321378219823), (Int.ofNat 885397979127971360466863185852), (Int.negOfNat 78044307761632419444896294740), (Int.negOfNat 14280414612742650174012004437), (Int.ofNat 1534849747492100486929202692), (Int.ofNat 114407510371570352609828236), (Int.negOfNat 14785117614613194275298764), (Int.negOfNat 563337524172652986005749), (Int.ofNat 89125306344305501941515), (Int.ofNat 1880238203829488767194), (Int.negOfNat 376472964292785202234), (Int.negOfNat 4436996922310073368), (Int.ofNat 1284150008854362060), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-8478737490315737842692895953861739/11258999068426240000000000000000000), (-126356312459084291088859436579259/11258999068426240000000000000000000), (25926988764946250794789025663897/11258999068426240000000000000000000), (-14684157453147872912086725517793/11258999068426240000000000000000000), (789387538568000987321378219823/11258999068426240000000000000000000), (221349494781992840116715796463/2814749767106560000000000000000000), (-3902215388081620972244814737/562949953421312000000000000000000), (-14280414612742650174012004437/11258999068426240000000000000000000), (383712436873025121732300673/2814749767106560000000000000000000), (28601877592892588152457059/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial154.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial154.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial154.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 8710639633893060456350570998811969), (Int.negOfNat 122392657519755026653290348528982), (Int.ofNat 2369745106861038205743754094727), (Int.ofNat 9687657343123473319460641417521), (Int.ofNat 2931600694565870232595662377846), (Int.negOfNat 459048893589910721554852501248), (Int.negOfNat 81799313399363790989098328282), (Int.ofNat 11883088049227013581827340254), (Int.ofNat 900367923983627398222127190), (Int.negOfNat 150705383849450012053296121), (Int.negOfNat 5213131776057066100303596), (Int.ofNat 1128708234198351304326983), (Int.ofNat 17490876695392540174524), (Int.negOfNat 5676099418989389969681), (Int.negOfNat 29453551467773259889), (Int.ofNat 21245480087219930148), (Int.negOfNat 59398633652382213), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-8710639633893060456350570998811969/11258999068426240000000000000000000), (-61196328759877513326645174264491/5629499534213120000000000000000000), (2369745106861038205743754094727/11258999068426240000000000000000000), (9687657343123473319460641417521/11258999068426240000000000000000000), (1465800347282935116297831188923/5629499534213120000000000000000000), (-1793159740585588756073642583/43980465111040000000000000000000), (-40899656699681895494549164141/5629499534213120000000000000000000), (5941544024613506790913670127/5629499534213120000000000000000000), (90036792398362739822212719/1125899906842624000000000000000000), (-150705383849450012053296121/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial154.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial154.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial154.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 8839792452343616896151878130521318), (Int.ofNat 50604580209153241027115591477308), (Int.ofNat 83374813779745892438812976021905), (Int.ofNat 9116339260022661302323617435196), (Int.negOfNat 2861038472164220665921284605821), (Int.negOfNat 351649693204586049557023202752), (Int.ofNat 83117501441892087273217133036), (Int.ofNat 5381853748748919097572756229), (Int.negOfNat 1345542262021279170847937877), (Int.negOfNat 36469877153799507733072484), (Int.ofNat 12613607822037866327305333), (Int.ofNat 97950083603586099293583), (Int.negOfNat 76373977526671240320042), (Int.ofNat 199826965915109722310), (Int.ofNat 324750083018197261214), (Int.negOfNat 2822699585567056472), (Int.negOfNat 1205786666985785189), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-4419896226171808448075939065260659/5629499534213120000000000000000000), (12651145052288310256778897869327/2814749767106560000000000000000000), (16674962755949178487762595204381/2251799813685248000000000000000000), (2279084815005665325580904358799/2814749767106560000000000000000000), (-2861038472164220665921284605821/11258999068426240000000000000000000), (-5494526456321657024328487543/175921860444160000000000000000000), (20779375360473021818304283259/2814749767106560000000000000000000), (5381853748748919097572756229/11258999068426240000000000000000000), (-1345542262021279170847937877/11258999068426240000000000000000000), (-9117469288449876933268121/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial154.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial154.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial154.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 8383524651574149418760621260972847), (Int.ofNat 390786323505380421161516066373754), (Int.ofNat 62404545881646112297726796112018), (Int.negOfNat 13943020701188397657883931526029), (Int.negOfNat 1373242353918729801513260129741), (Int.ofNat 518761803229206887732347683451), (Int.ofNat 22847348318598341636466341812), (Int.negOfNat 10553155281488610199542305853), (Int.negOfNat 141781284402897927704415833), (Int.ofNat 123804377680845964632349396), (Int.negOfNat 463942346410828917837995), (Int.negOfNat 911018577579987923392303), (Int.ofNat 12155049601754879363530), (Int.ofNat 4573053240661012820046), (Int.negOfNat 86162766417129653726), (Int.negOfNat 16926935681913114316), (Int.ofNat 362656833718623259), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-8383524651574149418760621260972847/11258999068426240000000000000000000), (195393161752690210580758033186877/5629499534213120000000000000000000), (31202272940823056148863398056009/5629499534213120000000000000000000), (-13943020701188397657883931526029/11258999068426240000000000000000000), (-1373242353918729801513260129741/11258999068426240000000000000000000), (518761803229206887732347683451/11258999068426240000000000000000000), (5711837079649585409116585453/2814749767106560000000000000000000), (-10553155281488610199542305853/11258999068426240000000000000000000), (-141781284402897927704415833/11258999068426240000000000000000000), (30951094420211491158087349/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial154.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial154.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial154.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 7469113223883120497303299372132391), (Int.ofNat 470432277477350978097562430614942), (Int.negOfNat 14031881315196438276112773312797), (Int.negOfNat 6064170779665240878148462504294), (Int.ofNat 2529083376729814989794759342787), (Int.ofNat 64461869055165642307155349656), (Int.negOfNat 70988864479658396234786042766), (Int.ofNat 498498565419368003968458370), (Int.ofNat 1056645185724946763473035454), (Int.negOfNat 22273175271000676656079971), (Int.negOfNat 9533223414441780112594624), (Int.ofNat 273504659560475099601077), (Int.ofNat 56902063385754828460256), (Int.negOfNat 1883667780765480316835), (Int.negOfNat 240858554794363839289), (Int.ofNat 8775707200198545600), (Int.ofNat 975794225084087795), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-7469113223883120497303299372132391/11258999068426240000000000000000000), (235216138738675489048781215307471/5629499534213120000000000000000000), (-14031881315196438276112773312797/11258999068426240000000000000000000), (-3032085389832620439074231252147/5629499534213120000000000000000000), (2529083376729814989794759342787/11258999068426240000000000000000000), (8057733631895705288394418707/1407374883553280000000000000000000), (-35494432239829198117393021383/5629499534213120000000000000000000), (49849856541936800396845837/1125899906842624000000000000000000), (528322592862473381736517727/5629499534213120000000000000000000), (-22273175271000676656079971/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial154.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial154.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial154.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 6594590816678401823057777613398572), (Int.ofNat 415202016606608727761731625475802), (Int.ofNat 427924085062794907466098798788), (Int.ofNat 7312498816310845984663817548816), (Int.ofNat 37315863466323295234846229800), (Int.negOfNat 380912368727892024246867789663), (Int.ofNat 14171805939286376443178525304), (Int.ofNat 7636936137571651388265857901), (Int.negOfNat 363315970118154129281560892), (Int.negOfNat 85956859495738927376733288), (Int.ofNat 4465826532881634866589964), (Int.ofNat 615815994242273967618049), (Int.negOfNat 33520056103414572905997), (Int.negOfNat 3038256068578865059770), (Int.ofNat 171324284471093640746), (Int.ofNat 10715576318044308556), (Int.negOfNat 550918812834015608), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-1648647704169600455764444403349643/2814749767106560000000000000000000), (207601008303304363880865812737901/5629499534213120000000000000000000), (106981021265698726866524699697/2814749767106560000000000000000000), (457031176019427874041488596801/703687441776640000000000000000000), (186579317331616476174231149/56294995342131200000000000000000), (-380912368727892024246867789663/11258999068426240000000000000000000), (1771475742410797055397315663/1407374883553280000000000000000000), (7636936137571651388265857901/11258999068426240000000000000000000), (-90828992529538532320390223/2814749767106560000000000000000000), (-10744607436967365922091661/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial154.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial154.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial154.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 5713814058861547153634126399979849), (Int.ofNat 480985908705433957943591920702239), (Int.ofNat 22277719717563870022663476315168), (Int.negOfNat 2104376364774779794827744504344), (Int.negOfNat 1455776529074334892953128657336), (Int.ofNat 144620986455788151037223754876), (Int.ofNat 44247502463807126899048289503), (Int.negOfNat 4109721542172586569033060409), (Int.negOfNat 645025623484440317683171858), (Int.ofNat 58447990510455482679894274), (Int.ofNat 5619115130628461575704853), (Int.negOfNat 504769702279713268577130), (Int.negOfNat 32485001552257562963285), (Int.ofNat 2927867947931081851523), (Int.ofNat 132946429665399051131), (Int.negOfNat 12294364637876786140), (Int.negOfNat 575856243608133965), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-5713814058861547153634126399979849/11258999068426240000000000000000000), (480985908705433957943591920702239/11258999068426240000000000000000000), (696178741173870938208233634849/351843720888320000000000000000000), (-263047045596847474353468063043/1407374883553280000000000000000000), (-181972066134291861619141082167/1407374883553280000000000000000000), (36155246613947037759305938719/2814749767106560000000000000000000), (44247502463807126899048289503/11258999068426240000000000000000000), (-4109721542172586569033060409/11258999068426240000000000000000000), (-322512811742220158841585929/5629499534213120000000000000000000), (29223995255227741339947137/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial154.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial154.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial154.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 4696055718880433232010718477069618), (Int.ofNat 515980078224261349250838070109669), (Int.negOfNat 6697557192646824177680716243413), (Int.negOfNat 3967000214108288428148894357774), (Int.ofNat 1059050619487677340981646105489), (Int.ofNat 187390016986027631679806845613), (Int.negOfNat 36045415384508355666771256507), (Int.negOfNat 3749152779089509186714194209), (Int.ofNat 630283986330612844528999955), (Int.ofNat 40410931018023404742174857), (Int.negOfNat 6503156248195885802464543), (Int.negOfNat 273109922503839306880667), (Int.ofNat 44037248395051161519038), (Int.ofNat 1262686384082678001517), (Int.negOfNat 209219047847164183457), (Int.negOfNat 3941157753642552616), (Int.ofNat 605868131457423347), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-2348027859440216616005359238534809/5629499534213120000000000000000000), (515980078224261349250838070109669/11258999068426240000000000000000000), (-6697557192646824177680716243413/11258999068426240000000000000000000), (-1983500107054144214074447178887/5629499534213120000000000000000000), (1059050619487677340981646105489/11258999068426240000000000000000000), (187390016986027631679806845613/11258999068426240000000000000000000), (-36045415384508355666771256507/11258999068426240000000000000000000), (-3749152779089509186714194209/11258999068426240000000000000000000), (126056797266122568905799991/2251799813685248000000000000000000), (40410931018023404742174857/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial154.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial154.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial154.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 3702292288884245408285572589466888), (Int.ofNat 482569597680373439226249772911911), (Int.negOfNat 25299998583128397574707609754), (Int.ofNat 5374675607550260055910193619181), (Int.ofNat 496200128910678287088278621154), (Int.negOfNat 252106529700423579154543714769), (Int.negOfNat 13958724234587274697220979318), (Int.ofNat 5629317643033457319911837569), (Int.ofNat 185969019816703310499865294), (Int.negOfNat 71507454478314561124363564), (Int.negOfNat 1385426704975930097660552), (Int.ofNat 577410588656681306488808), (Int.ofNat 6342896193725880617661), (Int.negOfNat 3207635584155185231073), (Int.negOfNat 19228835430701364515), (Int.ofNat 13183401744797606306), (Int.ofNat 175918262132180135), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-462786536110530676035696573683361/1407374883553280000000000000000000), (482569597680373439226249772911911/11258999068426240000000000000000000), (-12649999291564198787353804877/5629499534213120000000000000000000), (5374675607550260055910193619181/11258999068426240000000000000000000), (248100064455339143544139310577/5629499534213120000000000000000000), (-252106529700423579154543714769/11258999068426240000000000000000000), (-6979362117293637348610489659/5629499534213120000000000000000000), (5629317643033457319911837569/11258999068426240000000000000000000), (92984509908351655249932647/5629499534213120000000000000000000), (-17876863619578640281090891/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial154.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial154.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial154.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 2694547141285287372901901843920919), (Int.ofNat 542541321870612312929558950119373), (Int.ofNat 24399812607053112799352381257966), (Int.ofNat 130765146250188715158399888662), (Int.negOfNat 1360795921124056958179112270399), (Int.negOfNat 2085785835114505389879284363), (Int.ofNat 41197773781157055604831212215), (Int.negOfNat 152255656573105042093193964), (Int.negOfNat 663420652792700080650618983), (Int.ofNat 5075392619256408532681195), (Int.ofNat 6528007133728196209612551), (Int.negOfNat 66614185425209643722565), (Int.negOfNat 42926023288472518354251), (Int.ofNat 499992236998030508439), (Int.ofNat 200945806138344617038), (Int.negOfNat 2932964280597952364), (Int.negOfNat 660817450080831086), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-2694547141285287372901901843920919/11258999068426240000000000000000000), (542541321870612312929558950119373/11258999068426240000000000000000000), (12199906303526556399676190628983/5629499534213120000000000000000000), (65382573125094357579199944331/5629499534213120000000000000000000), (-1360795921124056958179112270399/11258999068426240000000000000000000), (-2085785835114505389879284363/11258999068426240000000000000000000), (8239554756231411120966242443/2251799813685248000000000000000000), (-38063914143276260523298491/2814749767106560000000000000000000), (-663420652792700080650618983/11258999068426240000000000000000000), (1015078523851281706536239/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial154.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial154.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial154.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 1530202294426252529847593588338820), (Int.ofNat 605203201524668126921715071064315), (Int.ofNat 1048703060949779859576676802470), (Int.negOfNat 5401307652856434506979118801649), (Int.ofNat 404874217338364576141650808055), (Int.ofNat 239195382550120654548526727608), (Int.negOfNat 13162806397275330243959520490), (Int.negOfNat 5073556588604387036636026679), (Int.ofNat 230135716392848759235246805), (Int.ofNat 62305174084405255740231132), (Int.negOfNat 2463314905193807943283908), (Int.negOfNat 493892874279774584312952), (Int.ofNat 17488397943693137975105), (Int.ofNat 2718498544542895866859), (Int.negOfNat 87520157233553874930), (Int.negOfNat 11230029421156154579), (Int.ofNat 242336158884909608), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-76510114721312626492379679416941/562949953421312000000000000000000), (121040640304933625384343014212863/2251799813685248000000000000000000), (104870306094977985957667680247/1125899906842624000000000000000000), (-5401307652856434506979118801649/11258999068426240000000000000000000), (80974843467672915228330161611/2251799813685248000000000000000000), (29899422818765081818565840951/1407374883553280000000000000000000), (-1316280639727533024395952049/1125899906842624000000000000000000), (-5073556588604387036636026679/11258999068426240000000000000000000), (46027143278569751847049361/2251799813685248000000000000000000), (15576293521101313935057783/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial154.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial154.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial154.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 346083762292566761403875675774274), (Int.ofNat 572235312031255344954099970848294), (Int.negOfNat 8416239684119474962112262470159), (Int.ofNat 3149600080307184961778392245686), (Int.ofNat 1044555216722100461630736470024), (Int.negOfNat 148147805514177272548236033360), (Int.negOfNat 30587407288784123780438898490), (Int.ofNat 3295809367104124551034955361), (Int.ofNat 482356346505809715495392235), (Int.negOfNat 42197051420323902593692048), (Int.negOfNat 4709445649649993306000192), (Int.ofNat 346896565024731721137628), (Int.ofNat 31015017952207345606495), (Int.negOfNat 1969055258254919214561), (Int.negOfNat 146274441891641754390), (Int.ofNat 8352139168450502461), (Int.ofNat 430825008179133692), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-173041881146283380701937837887137/5629499534213120000000000000000000), (286117656015627672477049985424147/5629499534213120000000000000000000), (-8416239684119474962112262470159/11258999068426240000000000000000000), (1574800040153592480889196122843/5629499534213120000000000000000000), (130569402090262557703842058753/1407374883553280000000000000000000), (-1851847568927215906852950417/140737488355328000000000000000000), (-3058740728878412378043889849/1125899906842624000000000000000000), (3295809367104124551034955361/11258999068426240000000000000000000), (96471269301161943099078447/2251799813685248000000000000000000), (-2637315713770243912105753/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial154.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial154.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial154.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 800453002014632798955596639518799), (Int.ofNat 593920385985368083792238316529370), (Int.ofNat 19199857092083640040299903301730), (Int.ofNat 3114469975246122287348735779805), (Int.negOfNat 1024796297172953436832394983994), (Int.negOfNat 132667549111514893292945971984), (Int.ofNat 31839907982093277647332895045), (Int.ofNat 2769169371821113006966678696), (Int.negOfNat 522481175378606527082647077), (Int.negOfNat 34193281204134963575079485), (Int.ofNat 5234812082920200621997809), (Int.ofNat 276470920904585526125795), (Int.negOfNat 35020731575785187041049), (Int.negOfNat 1562357197978445781661), (Int.ofNat 166004314951227757382), (Int.ofNat 6923857255149318136), (Int.negOfNat 545594358951150654), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(800453002014632798955596639518799/11258999068426240000000000000000000), (59392038598536808379223831652937/1125899906842624000000000000000000), (1919985709208364004029990330173/1125899906842624000000000000000000), (622893995049224457469747155961/2251799813685248000000000000000000), (-512398148586476718416197491997/5629499534213120000000000000000000), (-8291721819469680830809123249/703687441776640000000000000000000), (6367981596418655529466579009/2251799813685248000000000000000000), (346146171477639125870834837/1407374883553280000000000000000000), (-522481175378606527082647077/11258999068426240000000000000000000), (-6838656240826992715015897/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial154.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial154.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial154.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 2071613578780086548871083939941655), (Int.ofNat 671455609604055263054616378039894), (Int.ofNat 11152312908765075720480288449114), (Int.negOfNat 4777776138430586253135539483571), (Int.negOfNat 311548298976129953440587938254), (Int.ofNat 225524049259965287767160545610), (Int.ofNat 8513769769887062976444150558), (Int.negOfNat 5008390810155488106380804811), (Int.negOfNat 137292143367859892612245274), (Int.ofNat 63598471958005408667659616), (Int.ofNat 1450435618215011343061432), (Int.negOfNat 516822356992497512184772), (Int.negOfNat 10566872553221134894341), (Int.ofNat 2893729362764084451807), (Int.ofNat 54706340535887756375), (Int.negOfNat 11858108762924929754), (Int.negOfNat 49203466244315775), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(414322715756017309774216787988331/2251799813685248000000000000000000), (335727804802027631527308189019947/5629499534213120000000000000000000), (5576156454382537860240144224557/5629499534213120000000000000000000), (-4777776138430586253135539483571/11258999068426240000000000000000000), (-155774149488064976720293969127/5629499534213120000000000000000000), (22552404925996528776716054561/1125899906842624000000000000000000), (4256884884943531488222075279/5629499534213120000000000000000000), (-5008390810155488106380804811/11258999068426240000000000000000000), (-68646071683929946306122637/5629499534213120000000000000000000), (1987452248687669020864363/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial154.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial154.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial154.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3423045467911727659237209608603678), (Int.ofNat 666202256922808197749369798400581), (Int.negOfNat 8222965131485302232467682736906), (Int.ofNat 404305675659939411452216218573), (Int.ofNat 1152237240495181769257753295836), (Int.negOfNat 29991384081888961133286308186), (Int.negOfNat 36987317612502391110686875170), (Int.ofNat 671033254672058805874910991), (Int.ofNat 622499286879423528107150145), (Int.negOfNat 6907543833135895494810643), (Int.negOfNat 6353718197276385065843697), (Int.ofNat 35426762651663423746473), (Int.ofNat 43007456563300540688902), (Int.negOfNat 66828627858992711623), (Int.negOfNat 205157131314936619743), (Int.negOfNat 466713240191362116), (Int.ofNat 600543677574558393), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(1711522733955863829618604804301839/5629499534213120000000000000000000), (666202256922808197749369798400581/11258999068426240000000000000000000), (-4111482565742651116233841368453/5629499534213120000000000000000000), (404305675659939411452216218573/11258999068426240000000000000000000), (288059310123795442314438323959/2814749767106560000000000000000000), (-14995692040944480566643154093/5629499534213120000000000000000000), (-3698731761250239111068687517/1125899906842624000000000000000000), (671033254672058805874910991/11258999068426240000000000000000000), (124499857375884705621430029/2251799813685248000000000000000000), (-6907543833135895494810643/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial154.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial154.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial154.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4741136903918427912365969897225340), (Int.ofNat 666423825894546937128971568614009), (Int.ofNat 12045542363739034186435104303301), (Int.ofNat 3867317883360122660094032183473), (Int.negOfNat 588356051384545640435098382172), (Int.negOfNat 198573959678679270958125556830), (Int.ofNat 19036525432605697640142049907), (Int.ofNat 4720048420947315320800597971), (Int.negOfNat 298208085946201593604516442), (Int.negOfNat 63466998633187076901735186), (Int.ofNat 2668861057436981279986127), (Int.ofNat 538424003922107075416850), (Int.negOfNat 15120888786823690600115), (Int.negOfNat 3101432687120419970437), (Int.ofNat 58102783282576462589), (Int.ofNat 12873981368282244540), (Int.negOfNat 350734515231638055), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(237056845195921395618298494861267/562949953421312000000000000000000), (666423825894546937128971568614009/11258999068426240000000000000000000), (12045542363739034186435104303301/11258999068426240000000000000000000), (3867317883360122660094032183473/11258999068426240000000000000000000), (-147089012846136410108774595543/2814749767106560000000000000000000), (-19857395967867927095812555683/1125899906842624000000000000000000), (19036525432605697640142049907/11258999068426240000000000000000000), (4720048420947315320800597971/11258999068426240000000000000000000), (-149104042973100796802258221/5629499534213120000000000000000000), (-31733499316593538450867593/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial154.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial154.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial154.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 6139054621772723105775070940221661), (Int.ofNat 731637703389352812249481715171439), (Int.ofNat 12201203677392802471215409110800), (Int.negOfNat 3907813804645871032171301241934), (Int.negOfNat 644527885891474115782019301403), (Int.ofNat 199785575060539661500105401608), (Int.ofNat 24495482621407306024375587116), (Int.negOfNat 4464341711856063724735921579), (Int.negOfNat 476215770899596832997694388), (Int.ofNat 53647069604934259034561992), (Int.ofNat 5419038233597017044888956), (Int.negOfNat 393109520949016448145851), (Int.negOfNat 39445251941822157737523), (Int.ofNat 1921981981694618144310), (Int.ofNat 197651652907217386554), (Int.negOfNat 6623384886573281384), (Int.negOfNat 655492996197966132), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(6139054621772723105775070940221661/11258999068426240000000000000000000), (731637703389352812249481715171439/11258999068426240000000000000000000), (30503009193482006178038522777/28147497671065600000000000000000), (-1953906902322935516085650620967/5629499534213120000000000000000000), (-644527885891474115782019301403/11258999068426240000000000000000000), (24973196882567457687513175201/1407374883553280000000000000000000), (6123870655351826506093896779/2814749767106560000000000000000000), (-4464341711856063724735921579/11258999068426240000000000000000000), (-119053942724899208249423597/2814749767106560000000000000000000), (6705883700616782379320249/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial154.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial154.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial154.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 7616859457415244386704599155703361), (Int.ofNat 731268242628398662120054910331643), (Int.negOfNat 8409732205867077966233856575552), (Int.negOfNat 155457288456069170071153209298), (Int.ofNat 1308094994151186736743998476472), (Int.ofNat 42420255051440129593689073305), (Int.negOfNat 44675787947415750488060462694), (Int.negOfNat 1948765466950421955209198970), (Int.ofNat 742991264737495850490111006), (Int.ofNat 37685606365273772097996849), (Int.negOfNat 7039005383005357195113796), (Int.negOfNat 392362280267745258787783), (Int.ofNat 42396341919674993923684), (Int.ofNat 2521483605936280196785), (Int.negOfNat 177272091777572722431), (Int.negOfNat 11186967884717595300), (Int.ofNat 750672496707591885), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(7616859457415244386704599155703361/11258999068426240000000000000000000), (731268242628398662120054910331643/11258999068426240000000000000000000), (-131402065716673093222404008993/175921860444160000000000000000000), (-77728644228034585035576604649/5629499534213120000000000000000000), (163511874268898342092999809559/1407374883553280000000000000000000), (8484051010288025918737814661/2251799813685248000000000000000000), (-22337893973707875244030231347/5629499534213120000000000000000000), (-194876546695042195520919897/1125899906842624000000000000000000), (371495632368747925245055503/5629499534213120000000000000000000), (37685606365273772097996849/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial154.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial154.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial154.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 9063893311573275773244002307149782), (Int.ofNat 732374033197048144937775881839902), (Int.ofNat 14829815836269483252343384608169), (Int.ofNat 5181387744177250418147338167178), (Int.negOfNat 614895646127825990821258496473), (Int.negOfNat 311996574764428010147871706935), (Int.ofNat 10031035883364012332757964278), (Int.ofNat 7795770299189274054797521287), (Int.ofNat 34981492127859083716596373), (Int.negOfNat 99878336499721714414361044), (Int.negOfNat 2263212696662110533113025), (Int.ofNat 751517100755062889818417), (Int.ofNat 24091453743499382648850), (Int.negOfNat 3757748400467095175014), (Int.negOfNat 141196500837134194734), (Int.ofNat 13883081394450411224), (Int.ofNat 577129654329389261), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(4531946655786637886622001153574891/5629499534213120000000000000000000), (366187016598524072468887940919951/5629499534213120000000000000000000), (14829815836269483252343384608169/11258999068426240000000000000000000), (2590693872088625209073669083589/5629499534213120000000000000000000), (-614895646127825990821258496473/11258999068426240000000000000000000), (-62399314952885602029574341387/2251799813685248000000000000000000), (5015517941682006166378982139/5629499534213120000000000000000000), (7795770299189274054797521287/11258999068426240000000000000000000), (34981492127859083716596373/11258999068426240000000000000000000), (-24969584124930428603590261/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial154.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial154.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial154.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 10611186472612393755333247488004855), (Int.ofNat 814454984931416736720969763794089), (Int.ofNat 13445652832840960847887712255928), (Int.negOfNat 6722786085393516435894846807589), (Int.negOfNat 1310813491118765880199457655413), (Int.ofNat 282613044002885640803961997254), (Int.ofNat 60006648344814331485828390864), (Int.negOfNat 4070969901740635252954956031), (Int.negOfNat 1156768302698880503257395663), (Int.ofNat 15470870020412004206754076), (Int.ofNat 11257721569016678592810687), (Int.ofNat 86595152983161869755503), (Int.negOfNat 68055474304916381962738), (Int.negOfNat 1218321082278978707950), (Int.ofNat 285336997643382009646), (Int.ofNat 6868423479410779468), (Int.negOfNat 1053930696773832931), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(2122237294522478751066649497600971/2251799813685248000000000000000000), (814454984931416736720969763794089/11258999068426240000000000000000000), (1680706604105120105985964031991/1407374883553280000000000000000000), (-6722786085393516435894846807589/11258999068426240000000000000000000), (-1310813491118765880199457655413/11258999068426240000000000000000000), (141306522001442820401980998627/5629499534213120000000000000000000), (3750415521550895717864274429/703687441776640000000000000000000), (-4070969901740635252954956031/11258999068426240000000000000000000), (-1156768302698880503257395663/11258999068426240000000000000000000), (3867717505103001051688519/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial154.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial154.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial154.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 12231209917783397320969147800128648), (Int.ofNat 776832682666282899166196373421893), (Int.negOfNat 25949835131938071836110190475091), (Int.negOfNat 404433617632245403248425676514), (Int.ofNat 2888839160457015616058447333243), (Int.ofNat 260036301189372155112972725628), (Int.negOfNat 81104892338229102108415787558), (Int.negOfNat 10814097508097115626130634186), (Int.ofNat 730668741501021578894563250), (Int.ofNat 145061232280374465850161799), (Int.negOfNat 2850578987535289146242284), (Int.negOfNat 1080642379373577072034677), (Int.ofNat 957425205991755825536), (Int.ofNat 5350564839018840980739), (Int.ofNat 45962986015764175209), (Int.negOfNat 19836089009081900352), (Int.negOfNat 347137212427691867), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(1528901239722924665121143475016081/1407374883553280000000000000000000), (776832682666282899166196373421893/11258999068426240000000000000000000), (-25949835131938071836110190475091/11258999068426240000000000000000000), (-202216808816122701624212838257/5629499534213120000000000000000000), (2888839160457015616058447333243/11258999068426240000000000000000000), (65009075297343038778243181407/2814749767106560000000000000000000), (-40552446169114551054207893779/5629499534213120000000000000000000), (-5407048754048557813065317093/5629499534213120000000000000000000), (2922674966004086315578253/45035996273704960000000000000000), (145061232280374465850161799/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial154.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial154.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial154.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 13726064382510658676748807110521318), (Int.ofNat 762065008275540362296141015394253), (Int.ofNat 36941809750610224361426069489089), (Int.ofNat 16076502545224298809157607743103), (Int.negOfNat 1083689463566863736267613513036), (Int.negOfNat 1054917189761902079396701396167), (Int.negOfNat 77524014396709637546525066380), (Int.ofNat 13922575747070225817045639283), (Int.ofNat 1622777099753107206415323288), (Int.negOfNat 90118491803401544458791384), (Int.negOfNat 15255631798984904317993456), (Int.ofNat 329334438578172903758351), (Int.ofNat 89585023595830506564405), (Int.negOfNat 590038843858159409526), (Int.negOfNat 371452106769515202666), (Int.negOfNat 657064115541973708), (Int.ofNat 1242192675889225280), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(6863032191255329338374403555260659/5629499534213120000000000000000000), (762065008275540362296141015394253/11258999068426240000000000000000000), (36941809750610224361426069489089/11258999068426240000000000000000000), (16076502545224298809157607743103/11258999068426240000000000000000000), (-270922365891715934066903378259/2814749767106560000000000000000000), (-1054917189761902079396701396167/11258999068426240000000000000000000), (-3876200719835481877326253319/562949953421312000000000000000000), (13922575747070225817045639283/11258999068426240000000000000000000), (202847137469138400801915411/1407374883553280000000000000000000), (-11264811475425193057348923/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial154.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial154.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial154.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 15472652528782928215752147721464986), (Int.ofNat 976413362696368079111748626290983), (Int.ofNat 16081213790813774713556926949526), (Int.negOfNat 37184130525733415757889867843415), (Int.negOfNat 11112189762375055699282247606551), (Int.negOfNat 375151441393205355653377821015), (Int.ofNat 197084495807013260750097568734), (Int.ofNat 16052001389937258882363509925), (Int.negOfNat 1693380400823931620157899446), (Int.negOfNat 194120689290071086651303702), (Int.ofNat 8878099951801069899484155), (Int.ofNat 1359582666649961318866930), (Int.negOfNat 30914489523826074777507), (Int.negOfNat 6506112115152997117827), (Int.ofNat 72811356460873375949), (Int.ofNat 23354746446760140892), (Int.negOfNat 52800769048261963), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(7736326264391464107876073860732493/5629499534213120000000000000000000), (976413362696368079111748626290983/11258999068426240000000000000000000), (8040606895406887356778463474763/5629499534213120000000000000000000), (-7436826105146683151577973568683/2251799813685248000000000000000000), (-11112189762375055699282247606551/11258999068426240000000000000000000), (-75030288278641071130675564203/2251799813685248000000000000000000), (98542247903506630375048784367/5629499534213120000000000000000000), (642080055597490355294540397/450359962737049600000000000000000), (-846690200411965810078949723/5629499534213120000000000000000000), (-97060344645035543325651851/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial154.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial154.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial154.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 17016678049154324730960314044843054), (Int.ofNat 251836385970313393388628526641093), (Int.negOfNat 449432581478536708348014148520507), (Int.negOfNat 104454691916561287158461945351453), (Int.negOfNat 1052766569345025633297873276568), (Int.ofNat 2294907309784705922828203478032), (Int.ofNat 148490555642475967030580751883), (Int.negOfNat 24723890378654143960002513475), (Int.negOfNat 2275810720838803340898997051), (Int.ofNat 165207723739677736976921815), (Int.ofNat 18913333366420258302709035), (Int.negOfNat 759925075493230888832733), (Int.negOfNat 104514446175451178702646), (Int.ofNat 2558534348526915419779), (Int.ofNat 419273338703764691977), (Int.negOfNat 6117354448859782232), (Int.negOfNat 1297141994512633019), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(8508339024577162365480157022421527/5629499534213120000000000000000000), (251836385970313393388628526641093/11258999068426240000000000000000000), (-449432581478536708348014148520507/11258999068426240000000000000000000), (-104454691916561287158461945351453/11258999068426240000000000000000000), (-131595821168128204162234159571/1407374883553280000000000000000000), (143431706861544120176762717377/703687441776640000000000000000000), (148490555642475967030580751883/11258999068426240000000000000000000), (-988955615146165758400100539/450359962737049600000000000000000), (-2275810720838803340898997051/11258999068426240000000000000000000), (33041544747935547395384363/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial154.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial154.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial154.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 14949433855421277052700620050643285), (Int.negOfNat 2633876206198309235578927139898124), (Int.negOfNat 901938266996423549933140927682596), (Int.negOfNat 14109836966396554245590137108362), (Int.ofNat 22210450712963245046952041267995), (Int.ofNat 1434176600519476993728831820442), (Int.negOfNat 294524218660809850454287439446), (Int.negOfNat 25404131523110514000819216885), (Int.ofNat 2448061161943802177052308810), (Int.ofNat 244641425747722244521368392), (Int.negOfNat 14052492777728163475914256), (Int.negOfNat 1549922679466407595227608), (Int.ofNat 59296901651386736056731), (Int.ofNat 7046294442958709719377), (Int.negOfNat 191717201030696295165), (Int.negOfNat 24243783553680961058), (Int.ofNat 452738750524215793), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(2989886771084255410540124010128657/2251799813685248000000000000000000), (-658469051549577308894731784974531/2814749767106560000000000000000000), (-225484566749105887483285231920649/2814749767106560000000000000000000), (-7054918483198277122795068554181/5629499534213120000000000000000000), (4442090142592649009390408253599/2251799813685248000000000000000000), (717088300259738496864415910221/5629499534213120000000000000000000), (-147262109330404925227143719723/5629499534213120000000000000000000), (-5080826304622102800163843377/2251799813685248000000000000000000), (244806116194380217705230881/1125899906842624000000000000000000), (30580178218465280565171049/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial154.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial154.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial154.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 6340943955880645823876981293205359), (Int.negOfNat 5650425601604466413983598486880935), (Int.negOfNat 421255987760563327976844196514842), (Int.ofNat 165020004525899185610450812624522), (Int.ofNat 15251329270130859467468800520994), (Int.negOfNat 2795212438447892240863601139494), (Int.negOfNat 276880404177710990696696077191), (Int.ofNat 29475737579991607235116732848), (Int.ofNat 2981596961796310180905323879), (Int.negOfNat 211391916436241547491723567), (Int.negOfNat 21380931242562424995650043), (Int.ofNat 1097197128066280687764965), (Int.ofNat 109648556064469906576859), (Int.negOfNat 4308212588490493694135), (Int.negOfNat 422809957987228631358), (Int.ofNat 12991476483100287212), (Int.ofNat 1352091313136040758), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(6340943955880645823876981293205359/11258999068426240000000000000000000), (-1130085120320893282796719697376187/2251799813685248000000000000000000), (-210627993880281663988422098257421/5629499534213120000000000000000000), (82510002262949592805225406312261/5629499534213120000000000000000000), (7625664635065429733734400260497/5629499534213120000000000000000000), (-1397606219223946120431800569747/5629499534213120000000000000000000), (-276880404177710990696696077191/11258999068426240000000000000000000), (1842233598749475452194795803/703687441776640000000000000000000), (2981596961796310180905323879/11258999068426240000000000000000000), (-211391916436241547491723567/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial154.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial154.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial154.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 5183508326755569722288267088459908), (Int.negOfNat 5128268446372955839887610994911608), (Int.ofNat 668795440631360757983941546620085), (Int.ofNat 151363007241438032961410328024552), (Int.negOfNat 18802440164817482129204975765084), (Int.negOfNat 2862885393912441743129079468524), (Int.ofNat 277300997975484658490885233001), (Int.ofNat 34157054787985882168932688695), (Int.negOfNat 2599341069406609860707382209), (Int.negOfNat 275157502408839898171883860), (Int.ofNat 16894877947603111769377316), (Int.ofNat 1584622818898021676221352), (Int.negOfNat 80500318397062251617897), (Int.negOfNat 6812508755512129067963), (Int.ofNat 293733922899456283810), (Int.ofNat 22290411230039509331), (Int.negOfNat 870993171541305536), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-1295877081688892430572066772114977/2814749767106560000000000000000000), (-641033555796619479985951374363951/1407374883553280000000000000000000), (133759088126272151596788309324017/2251799813685248000000000000000000), (18920375905179754120176291003069/1407374883553280000000000000000000), (-4700610041204370532301243941271/2814749767106560000000000000000000), (-715721348478110435782269867131/2814749767106560000000000000000000), (277300997975484658490885233001/11258999068426240000000000000000000), (6831410957597176433786537739/2251799813685248000000000000000000), (-2599341069406609860707382209/11258999068426240000000000000000000), (-13757875120441994908594193/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial154.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial154.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial154.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial154.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial154.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial154.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial154.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial154.reflect := by
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

end Bin154
end
end ErdosOverlap.OuterNumerics
