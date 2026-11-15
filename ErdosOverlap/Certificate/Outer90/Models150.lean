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

/-! # Exact integer weighted outer models for source bin 150

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin150

def weightDenominator : ℤ := (Int.ofNat 5000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 1111469712464034000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1113547695720310800)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 1043805070184775100)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 750178800150234200)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 474822187462466700)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 306831739108013450)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 164592107689314450)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 57263631510617230)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial150.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial150.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 4825108387358446500)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1269031605504676000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 785208194178202850)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 493283083489125600)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 219588554804402350)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 117628124769750870)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 32080140513969350)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 13992937301478413)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 9890714898177700)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial150.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial150.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4825108387358446500)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1269031605504676000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 785208194178202850)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 493283083489125600)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 219588554804402350)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 117628124769750870)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 32080140513969350)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 13992937301478413)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 9890714898177700)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial150.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial150.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial150.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 3632371562098708729226949964107261), (Int.ofNat 2453901538191968250989415019146991), (Int.ofNat 367271867173478755124641655696358), (Int.negOfNat 74947333916263156008670478941419), (Int.negOfNat 9530470288985637462622688940236), (Int.ofNat 1410245670996446539234273916211), (Int.ofNat 134737208590822637255783120311), (Int.negOfNat 16623380683103032440356714259), (Int.negOfNat 1225979195998043459128466516), (Int.ofNat 132233827916210727075645857), (Int.ofNat 7780089305256780861108802), (Int.negOfNat 752053181291887051949510), (Int.negOfNat 36323172411792845510948), (Int.ofNat 3195645892288023753296), (Int.ofNat 129575416656993560780), (Int.negOfNat 10331312922545947828), (Int.negOfNat 377573038551855987), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-3632371562098708729226949964107261/5629499534213120000000000000000000), (2453901538191968250989415019146991/5629499534213120000000000000000000), (183635933586739377562320827848179/2814749767106560000000000000000000), (-74947333916263156008670478941419/5629499534213120000000000000000000), (-2382617572246409365655672235059/1407374883553280000000000000000000), (1410245670996446539234273916211/5629499534213120000000000000000000), (134737208590822637255783120311/5629499534213120000000000000000000), (-16623380683103032440356714259/5629499534213120000000000000000000), (-306494798999510864782116629/1407374883553280000000000000000000), (132233827916210727075645857/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial150.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial150.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial150.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial150 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 2043836195934463667046054675747341), (Int.ofNat 2848967790440284329755010248583960), (Int.negOfNat 178678829349542840481435568102842), (Int.negOfNat 83933819053657583010192940121820), (Int.ofNat 7231208726424101114950503075117), (Int.ofNat 1386043725170814917564536646689), (Int.negOfNat 132791335570451104538512386149), (Int.negOfNat 14230761179929182064888854861), (Int.ofNat 1421332413979221186132687234), (Int.ofNat 99616217790851963931501673), (Int.negOfNat 10085702947952947790416188), (Int.negOfNat 505373297021176082068790), (Int.ofNat 51141259790007998384692), (Int.ofNat 1941917267536196050494), (Int.negOfNat 195129145418639410830), (Int.negOfNat 5728615515301186782), (Int.ofNat 618993325157824273), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(2043836195934463667046054675747341/5629499534213120000000000000000000), (71224194761007108243875256214599/140737488355328000000000000000000), (-89339414674771420240717784051421/2814749767106560000000000000000000), (-4196690952682879150509647006091/281474976710656000000000000000000), (7231208726424101114950503075117/5629499534213120000000000000000000), (1386043725170814917564536646689/5629499534213120000000000000000000), (-132791335570451104538512386149/5629499534213120000000000000000000), (-14230761179929182064888854861/5629499534213120000000000000000000), (710666206989610593066343617/2814749767106560000000000000000000), (99616217790851963931501673/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial150.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial150.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial150.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial150 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 6505722186788529103603161761774993), (Int.ofNat 1439086469867627194123855529885748), (Int.negOfNat 436402897501301120369572365171051), (Int.ofNat 3054236981731241593768420997528), (Int.ofNat 10983178964299437042061723605416), (Int.negOfNat 655914795271823987750051340681), (Int.negOfNat 143958900779134263870505668911), (Int.ofNat 11922446604222117064722186609), (Int.ofNat 1176694479811334374385342356), (Int.negOfNat 114506310077962134367119857), (Int.negOfNat 6625388870012302375924192), (Int.ofNat 719117222764058908523160), (Int.ofNat 27355554255512656659958), (Int.negOfNat 3237578495509783690576), (Int.negOfNat 86376612440230843050), (Int.ofNat 11033179226401160278), (Int.ofNat 195891429121826597), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(6505722186788529103603161761774993/5629499534213120000000000000000000), (359771617466906798530963882471437/1407374883553280000000000000000000), (-436402897501301120369572365171051/5629499534213120000000000000000000), (381779622716405199221052624691/703687441776640000000000000000000), (1372897370537429630257715450677/703687441776640000000000000000000), (-655914795271823987750051340681/5629499534213120000000000000000000), (-143958900779134263870505668911/5629499534213120000000000000000000), (11922446604222117064722186609/5629499534213120000000000000000000), (294173619952833593596335589/1407374883553280000000000000000000), (-114506310077962134367119857/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial150.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial150.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial150.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial150 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 7810009105259490759017455717044964), (Int.ofNat 7731197531823456887328165543389), (Int.negOfNat 231966389712287221333127981686825), (Int.ofNat 49749972861377317567718994748559), (Int.negOfNat 75454879330436607850776706357), (Int.negOfNat 1116133077822263076809856591959), (Int.ofNat 67036319841475736987560607659), (Int.ofNat 12015760861901085720174290511), (Int.negOfNat 1051649940476482043126991894), (Int.negOfNat 79584297670865361207002873), (Int.ofNat 8718713992715171943863648), (Int.ofNat 360732826662552287344030), (Int.negOfNat 47815279149701901064542), (Int.negOfNat 1189650696096586364044), (Int.ofNat 190150975788040134580), (Int.ofNat 2749153356811629132), (Int.negOfNat 589321180463291173), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(1952502276314872689754363929261241/1407374883553280000000000000000000), (7731197531823456887328165543389/5629499534213120000000000000000000), (-9278655588491488853325119267473/225179981368524800000000000000000), (49749972861377317567718994748559/5629499534213120000000000000000000), (-75454879330436607850776706357/5629499534213120000000000000000000), (-1116133077822263076809856591959/5629499534213120000000000000000000), (67036319841475736987560607659/5629499534213120000000000000000000), (12015760861901085720174290511/5629499534213120000000000000000000), (-525824970238241021563495947/2814749767106560000000000000000000), (-79584297670865361207002873/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial150.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial150.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial150.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial150 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 7264210024446287934377318762620622), (Int.negOfNat 397798619912248143636757706218377), (Int.negOfNat 2548840335445088739485359829986), (Int.ofNat 19786813368979394397089700066743), (Int.negOfNat 5222803940234900048689426974119), (Int.ofNat 141979173428060509990240496551), (Int.ofNat 95679733240171321994773503141), (Int.negOfNat 7253535831126274824733424479), (Int.negOfNat 829217318629714845853841836), (Int.ofNat 88679827530284905427422687), (Int.ofNat 4346931889342320462230482), (Int.negOfNat 618993324351694045559350), (Int.negOfNat 15063264446227762651218), (Int.ofNat 2942512109634646700366), (Int.ofNat 35111546795068389390), (Int.negOfNat 10498348470140992578), (Int.negOfNat 24100534589974907), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(3632105012223143967188659381310311/2814749767106560000000000000000000), (-397798619912248143636757706218377/5629499534213120000000000000000000), (-1274420167722544369742679914993/2814749767106560000000000000000000), (19786813368979394397089700066743/5629499534213120000000000000000000), (-5222803940234900048689426974119/5629499534213120000000000000000000), (141979173428060509990240496551/5629499534213120000000000000000000), (95679733240171321994773503141/5629499534213120000000000000000000), (-7253535831126274824733424479/5629499534213120000000000000000000), (-207304329657428711463460459/1407374883553280000000000000000000), (88679827530284905427422687/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial150.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial150.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial150.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial150 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 6542721721716934027721149456903838), (Int.negOfNat 311832416607915857332669116327778), (Int.ofNat 19226620290345652688745592949662), (Int.negOfNat 6039094100552227365712597721525), (Int.negOfNat 632932527668796480554083205990), (Int.ofNat 504326222313491102807393401389), (Int.negOfNat 33938470532450290552895740749), (Int.negOfNat 6906311383256801957359368821), (Int.ofNat 732688734734124793200426294), (Int.ofNat 45626328057623681604610583), (Int.negOfNat 6903980224239392215247858), (Int.negOfNat 171622618711419006486240), (Int.ofNat 40374108328797287029932), (Int.ofNat 337153656415016680124), (Int.negOfNat 166310107921440126870), (Int.ofNat 147021766735608978), (Int.ofNat 559649035768758073), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(3271360860858467013860574728451919/2814749767106560000000000000000000), (-155916208303957928666334558163889/2814749767106560000000000000000000), (9613310145172826344372796474831/2814749767106560000000000000000000), (-241563764022089094628503908861/225179981368524800000000000000000), (-63293252766879648055408320599/562949953421312000000000000000000), (504326222313491102807393401389/5629499534213120000000000000000000), (-33938470532450290552895740749/5629499534213120000000000000000000), (-6906311383256801957359368821/5629499534213120000000000000000000), (366344367367062396600213147/2814749767106560000000000000000000), (45626328057623681604610583/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial150.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial150.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial150.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial150 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 5950809738844355280002681049821560), (Int.negOfNat 296093915386557824152814989628424), (Int.negOfNat 3196922141142837481808529475544), (Int.ofNat 1222300871370804481092767364563), (Int.ofNat 1349865464908996041948249184229), (Int.negOfNat 119548142833208743383022352431), (Int.negOfNat 41301293670019495752045869671), (Int.ofNat 4843197252906808765481095809), (Int.ofNat 388087937130166311267029986), (Int.negOfNat 65209447810252769803960237), (Int.negOfNat 1660232445290430461049132), (Int.ofNat 485209599476644206521560), (Int.ofNat 1989024005432077889778), (Int.negOfNat 2391530188653696126976), (Int.ofNat 16162263109216012550), (Int.ofNat 8838026513464835678), (Int.negOfNat 147690359941876783), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(148770243471108882000067026245539/140737488355328000000000000000000), (-37011739423319728019101873703553/703687441776640000000000000000000), (-399615267642854685226066184443/703687441776640000000000000000000), (1222300871370804481092767364563/5629499534213120000000000000000000), (1349865464908996041948249184229/5629499534213120000000000000000000), (-119548142833208743383022352431/5629499534213120000000000000000000), (-41301293670019495752045869671/5629499534213120000000000000000000), (4843197252906808765481095809/5629499534213120000000000000000000), (194043968565083155633514993/2814749767106560000000000000000000), (-65209447810252769803960237/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial150.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial150.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial150.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial150 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 5371426825790364647282272712788957), (Int.negOfNat 266098196191522304586390782411393), (Int.ofNat 20701392316416739481970057256168), (Int.ofNat 3682714702480427571377194545514), (Int.negOfNat 798267136491346904056700346940), (Int.negOfNat 165520659619284826720593434402), (Int.ofNat 27368512381324896920995701059), (Int.ofNat 2438270204693455521768401801), (Int.negOfNat 517324877589554755324527364), (Int.negOfNat 12064266568697770421003023), (Int.ofNat 5035235982651203530096678), (Int.negOfNat 11696750316711562019190), (Int.negOfNat 30364125109622053613742), (Int.ofNat 445742284811056079326), (Int.ofNat 126570464549785044000), (Int.negOfNat 2808632542363603158), (Int.negOfNat 472713259563607743), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(5371426825790364647282272712788957/5629499534213120000000000000000000), (-266098196191522304586390782411393/5629499534213120000000000000000000), (2587674039552092435246257157021/703687441776640000000000000000000), (1841357351240213785688597272757/2814749767106560000000000000000000), (-39913356824567345202835017347/281474976710656000000000000000000), (-82760329809642413360296717201/2814749767106560000000000000000000), (27368512381324896920995701059/5629499534213120000000000000000000), (2438270204693455521768401801/5629499534213120000000000000000000), (-129331219397388688831131841/1407374883553280000000000000000000), (-12064266568697770421003023/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial150.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial150.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial150.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial150 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 4935358869678617866753964780015235), (Int.negOfNat 172071749095203231090765797078645), (Int.ofNat 17677678576844134449440201159537), (Int.negOfNat 4498113778060058264900213286942), (Int.negOfNat 693079532429743054379219756342), (Int.ofNat 149078634829803712960876499561), (Int.ofNat 10592239364982396554789654241), (Int.negOfNat 3475446621773347343272716499), (Int.negOfNat 44669898636074980926901336), (Int.ofNat 44497255775723460453518677), (Int.negOfNat 613651764088758775630278), (Int.negOfNat 334958849341949560647990), (Int.ofNat 8936923418218870780642), (Int.ofNat 1669244442955195833626), (Int.negOfNat 56917221248163230300), (Int.negOfNat 6146631851656581358), (Int.ofNat 242436193166755843), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(987071773935723573350792956003047/1125899906842624000000000000000000), (-34414349819040646218153159415729/1125899906842624000000000000000000), (17677678576844134449440201159537/5629499534213120000000000000000000), (-2249056889030029132450106643471/2814749767106560000000000000000000), (-346539766214871527189609878171/2814749767106560000000000000000000), (149078634829803712960876499561/5629499534213120000000000000000000), (10592239364982396554789654241/5629499534213120000000000000000000), (-3475446621773347343272716499/5629499534213120000000000000000000), (-5583737329509372615862667/703687441776640000000000000000000), (44497255775723460453518677/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial150.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial150.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial150.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial150 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 4619865547416240304924890322834445), (Int.negOfNat 165063778996218392901408552335213), (Int.negOfNat 13702646699968848956645815504081), (Int.negOfNat 4194058708455785920258984923023), (Int.ofNat 568773339515722384083234364833), (Int.ofNat 40471648568949838245819350452), (Int.negOfNat 19340327812688242055014525329), (Int.ofNat 236430880674410203158563209), (Int.ofNat 328306520605639040163050714), (Int.negOfNat 11770830051777584582887237), (Int.negOfNat 3137312114710567170275968), (Int.ofNat 146413583626417390125060), (Int.ofNat 18887162181385873805922), (Int.negOfNat 1007220865065971292676), (Int.negOfNat 78543191939571722950), (Int.ofNat 4624828301493347378), (Int.ofNat 338404566746017883), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(923973109483248060984978064566889/1125899906842624000000000000000000), (-165063778996218392901408552335213/5629499534213120000000000000000000), (-13702646699968848956645815504081/5629499534213120000000000000000000), (-4194058708455785920258984923023/5629499534213120000000000000000000), (568773339515722384083234364833/5629499534213120000000000000000000), (10117912142237459561454837613/1407374883553280000000000000000000), (-19340327812688242055014525329/5629499534213120000000000000000000), (236430880674410203158563209/5629499534213120000000000000000000), (164153260302819520081525357/2814749767106560000000000000000000), (-11770830051777584582887237/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial150.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial150.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial150.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial150 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 4210638056357601942833465051927037), (Int.negOfNat 252076958623681609475789434074206), (Int.negOfNat 25958346893530480327796415994027), (Int.negOfNat 502233077669413429475032743949), (Int.ofNat 165491624730801865497450048375), (Int.negOfNat 67852709646297390032315655741), (Int.ofNat 5301829153481538776594565749), (Int.ofNat 1897748511206641590563128479), (Int.negOfNat 157658909304167157642756794), (Int.negOfNat 23907187728487915124964417), (Int.ofNat 2028086917638410324443258), (Int.ofNat 176781402349865397133560), (Int.negOfNat 15616511589726341365232), (Int.negOfNat 861023481262162728776), (Int.ofNat 80804825841632249770), (Int.ofNat 2926325050091763478), (Int.negOfNat 270027679982839973), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(4210638056357601942833465051927037/5629499534213120000000000000000000), (-126038479311840804737894717037103/2814749767106560000000000000000000), (-25958346893530480327796415994027/5629499534213120000000000000000000), (-502233077669413429475032743949/5629499534213120000000000000000000), (1323932997846414923979600387/45035996273704960000000000000000), (-67852709646297390032315655741/5629499534213120000000000000000000), (5301829153481538776594565749/5629499534213120000000000000000000), (1897748511206641590563128479/5629499534213120000000000000000000), (-78829454652083578821378397/2814749767106560000000000000000000), (-23907187728487915124964417/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial150.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial150.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial150.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial150 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 3599641463105798499490677126401780), (Int.negOfNat 360406055013868955834237261882878), (Int.negOfNat 28245945475771208587663914191599), (Int.negOfNat 355754797265157136535180308838), (Int.ofNat 95991271371150467022791180534), (Int.ofNat 56155675563699164046866931488), (Int.ofNat 6529118675655068189618725689), (Int.negOfNat 1638981683362392179938347279), (Int.negOfNat 131841725568019608644680764), (Int.ofNat 23858454778678661224819287), (Int.ofNat 1237511584044876034810418), (Int.negOfNat 211444204918069424188950), (Int.negOfNat 7033684691880697128582), (Int.ofNat 1252202878079078088466), (Int.ofNat 26679028051491210010), (Int.negOfNat 5296078768351734278), (Int.negOfNat 166613672214166193), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(179982073155289924974533856320089/281474976710656000000000000000000), (-180203027506934477917118630941439/2814749767106560000000000000000000), (-28245945475771208587663914191599/5629499534213120000000000000000000), (-177877398632578568267590154419/2814749767106560000000000000000000), (47995635685575233511395590267/2814749767106560000000000000000000), (1754864861365598876464591609/175921860444160000000000000000000), (6529118675655068189618725689/5629499534213120000000000000000000), (-1638981683362392179938347279/5629499534213120000000000000000000), (-32960431392004902161170191/1407374883553280000000000000000000), (23858454778678661224819287/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial150.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial150.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial150.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial150 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 2766519728637844286601535458434678), (Int.negOfNat 469651578834707050108350536894553), (Int.negOfNat 23236925472364757744137289362680), (Int.ofNat 2686895776964083209903119874560), (Int.ofNat 546195455707815282835944842965), (Int.negOfNat 10697738212049067456302483409), (Int.negOfNat 14251823074859132400560227359), (Int.negOfNat 278936512493606713675759389), (Int.ofNat 237912950083124511890954894), (Int.ofNat 4065169824838443119610827), (Int.negOfNat 2479419701982933684371048), (Int.negOfNat 23913608790344645078870), (Int.ofNat 17153886127142234277042), (Int.ofNat 63803367006429185556), (Int.negOfNat 83172667417109406680), (Int.ofNat 132917503465190332), (Int.ofNat 240355535288306873), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(1383259864318922143300767729217339/2814749767106560000000000000000000), (-469651578834707050108350536894553/5629499534213120000000000000000000), (-580923136809118943603432234067/140737488355328000000000000000000), (1049568662876595003868406201/2199023255552000000000000000000), (109239091141563056567188968593/1125899906842624000000000000000000), (-10697738212049067456302483409/5629499534213120000000000000000000), (-14251823074859132400560227359/5629499534213120000000000000000000), (-278936512493606713675759389/5629499534213120000000000000000000), (118956475041562255945477447/2814749767106560000000000000000000), (4065169824838443119610827/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial150.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial150.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial150.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial150 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 1763273483024045711553469736551282), (Int.negOfNat 516354968929795856543514257904911), (Int.ofNat 1946413061935377205072308808426), (Int.ofNat 4603043969105721271952252721952), (Int.negOfNat 243360234460489828561492882764), (Int.negOfNat 109394079267880745507668108868), (Int.ofNat 3503299953447671453379383111), (Int.ofNat 2013311690652099130433379609), (Int.negOfNat 43385652039805365432049756), (Int.negOfNat 24792400354595753977447657), (Int.ofNat 476943707755504960976492), (Int.ofNat 203233809222593526561060), (Int.negOfNat 3816898329736318642158), (Int.negOfNat 1155514676510528696176), (Int.ofNat 21237980399051739850), (Int.ofNat 4802275175201421178), (Int.negOfNat 5177222317685497), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(881636741512022855776734868275641/2814749767106560000000000000000000), (-516354968929795856543514257904911/5629499534213120000000000000000000), (973206530967688602536154404213/2814749767106560000000000000000000), (143845124034553789748507897561/175921860444160000000000000000000), (-60840058615122457140373220691/1407374883553280000000000000000000), (-27348519816970186376917027217/1407374883553280000000000000000000), (3503299953447671453379383111/5629499534213120000000000000000000), (2013311690652099130433379609/5629499534213120000000000000000000), (-10846413009951341358012439/1407374883553280000000000000000000), (-24792400354595753977447657/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial150.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial150.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial150.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial150 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 768238169545833843447334458251654), (Int.negOfNat 468394214862604026691351284666618), (Int.ofNat 16985038627049938282676755978137), (Int.negOfNat 227483184626046299310581494534), (Int.negOfNat 697808265153691771395595047132), (Int.ofNat 41468571358451910688856053189), (Int.ofNat 14325216709301115008582146249), (Int.negOfNat 927177596357510011139262361), (Int.negOfNat 205757567423480116655287234), (Int.ofNat 12211397742428676106122973), (Int.ofNat 2021104890104245530663988), (Int.negOfNat 104540231236760006116590), (Int.negOfNat 13653984749875223124792), (Int.ofNat 617820522067389707694), (Int.ofNat 65609137469251047930), (Int.negOfNat 2879818496037355682), (Int.negOfNat 210683390593773773), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(384119084772916921723667229125827/2814749767106560000000000000000000), (-234197107431302013345675642333309/2814749767106560000000000000000000), (16985038627049938282676755978137/5629499534213120000000000000000000), (-113741592313023149655290747267/2814749767106560000000000000000000), (-174452066288422942848898761783/1407374883553280000000000000000000), (41468571358451910688856053189/5629499534213120000000000000000000), (14325216709301115008582146249/5629499534213120000000000000000000), (-927177596357510011139262361/5629499534213120000000000000000000), (-102878783711740058327643617/2814749767106560000000000000000000), (12211397742428676106122973/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial150.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial150.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial150.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial150 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 111514390045186575955627486513174), (Int.negOfNat 420034857341259594074274562928990), (Int.ofNat 4712305133494019473672203097027), (Int.negOfNat 2656145756338024670428886409493), (Int.ofNat 156870991247022096588639136151), (Int.ofNat 80011099132218039011932416998), (Int.negOfNat 8878212950901736001688885311), (Int.negOfNat 1327356922106384120575645359), (Int.ofNat 166993565905340769032256016), (Int.ofNat 15765198376795753221180157), (Int.negOfNat 1762903508185127346805902), (Int.negOfNat 129584830365519660494410), (Int.ofNat 12161056694006670632248), (Int.ofNat 748628635239448683996), (Int.negOfNat 58553914939912713080), (Int.negOfNat 3254623381741799028), (Int.ofNat 167077401951359487), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-55757195022593287977813743256587/2814749767106560000000000000000000), (-42003485734125959407427456292899/562949953421312000000000000000000), (4712305133494019473672203097027/5629499534213120000000000000000000), (-2656145756338024670428886409493/5629499534213120000000000000000000), (156870991247022096588639136151/5629499534213120000000000000000000), (40005549566109019505966208499/2814749767106560000000000000000000), (-8878212950901736001688885311/5629499534213120000000000000000000), (-1327356922106384120575645359/5629499534213120000000000000000000), (10437097869083798064516001/351843720888320000000000000000000), (15765198376795753221180157/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial150.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial150.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial150.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial150 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 949603060116093212485063582016166), (Int.negOfNat 423740729053850477384834961973241), (Int.negOfNat 3732674859029815220887790544607), (Int.negOfNat 11573580238139403703923294915), (Int.ofNat 275807355758216530546046206162), (Int.negOfNat 48066294108712477305434132329), (Int.negOfNat 5171043913037029925606172869), (Int.ofNat 1598700666809852607515480361), (Int.ofNat 76341007097746202675428484), (Int.negOfNat 22482953769239248168457943), (Int.negOfNat 815313732214622184990278), (Int.ofNat 189626989301197953728850), (Int.ofNat 6005210706376360405272), (Int.negOfNat 1083015941446721887564), (Int.negOfNat 31247624190368925200), (Int.ofNat 4616591482840576212), (Int.ofNat 76374697776183913), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-474801530058046606242531791008083/2814749767106560000000000000000000), (-423740729053850477384834961973241/5629499534213120000000000000000000), (-3732674859029815220887790544607/5629499534213120000000000000000000), (-2314716047627880740784658983/1125899906842624000000000000000000), (137903677879108265273023103081/2814749767106560000000000000000000), (-48066294108712477305434132329/5629499534213120000000000000000000), (-5171043913037029925606172869/5629499534213120000000000000000000), (1598700666809852607515480361/5629499534213120000000000000000000), (19085251774436550668857121/1407374883553280000000000000000000), (-22482953769239248168457943/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial150.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial150.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial150.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial150 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 1809351722280805825192844532069011), (Int.negOfNat 434081980637140162488284129304109), (Int.negOfNat 1165392686549328577408550449917), (Int.ofNat 351904891051688484222004311074), (Int.negOfNat 75233716714323666379949285091), (Int.ofNat 12313815255413716621058247702), (Int.ofNat 10821750039653162258026984731), (Int.negOfNat 171519565152368883023550821), (Int.negOfNat 223937027188229207366434406), (Int.ofNat 627583524516852343608973), (Int.ofNat 2418879196464611949876612), (Int.ofNat 7661869286301620009470), (Int.negOfNat 16698370208732926933008), (Int.negOfNat 109234384971892770766), (Int.ofNat 80625078778181955050), (Int.ofNat 909442062890433598), (Int.negOfNat 261823235176238547), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-1809351722280805825192844532069011/5629499534213120000000000000000000), (-434081980637140162488284129304109/5629499534213120000000000000000000), (-1165392686549328577408550449917/5629499534213120000000000000000000), (175952445525844242111002155537/2814749767106560000000000000000000), (-75233716714323666379949285091/5629499534213120000000000000000000), (6156907627706858310529123851/2814749767106560000000000000000000), (10821750039653162258026984731/5629499534213120000000000000000000), (-171519565152368883023550821/5629499534213120000000000000000000), (-111968513594114603683217203/2814749767106560000000000000000000), (627583524516852343608973/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial150.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial150.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial150.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial150 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 2679555656949469597490694480031679), (Int.negOfNat 434157932671946177699341052337130), (Int.ofNat 2236053677820854896143004451904), (Int.ofNat 1515720431057919346317678272924), (Int.ofNat 431664789333702005758441869161), (Int.ofNat 46794437366387374214339848906), (Int.negOfNat 8948063586315873291012289051), (Int.negOfNat 1701872678362915971896166671), (Int.ofNat 111245291330763039513556556), (Int.ofNat 25020515053947303978924883), (Int.negOfNat 858780808989892637102092), (Int.negOfNat 216600287002848125698320), (Int.ofNat 4305911507356449794578), (Int.ofNat 1254421549152979056064), (Int.negOfNat 15062540698705970570), (Int.negOfNat 5318457786695788662), (Int.ofNat 105306911653845477), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-2679555656949469597490694480031679/5629499534213120000000000000000000), (-43415793267194617769934105233713/562949953421312000000000000000000), (34938338715950857752234444561/87960930222080000000000000000000), (378930107764479836579419568231/1407374883553280000000000000000000), (431664789333702005758441869161/5629499534213120000000000000000000), (23397218683193687107169924453/2814749767106560000000000000000000), (-8948063586315873291012289051/5629499534213120000000000000000000), (-1701872678362915971896166671/5629499534213120000000000000000000), (27811322832690759878389139/1407374883553280000000000000000000), (25020515053947303978924883/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial150.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial150.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial150.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial150 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 3519148007468864231677863907248081), (Int.negOfNat 391783816338311957860768935342282), (Int.ofNat 22441827501396599257932450218270), (Int.ofNat 4768431135990306507361784751985), (Int.ofNat 91962954232089612927851455118), (Int.negOfNat 115770646915505159540285274142), (Int.negOfNat 9082574395874928063385853031), (Int.ofNat 1945287619726397537365516851), (Int.ofNat 200076735533989605448430026), (Int.negOfNat 20341548351924475038224833), (Int.negOfNat 2297147192461624827457932), (Int.ofNat 138365287074361487427530), (Int.ofNat 16538765372775772294938), (Int.negOfNat 649741541857493390944), (Int.negOfNat 81580031646671780940), (Int.ofNat 2070020095599124052), (Int.ofNat 232151090481705447), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-3519148007468864231677863907248081/5629499534213120000000000000000000), (-195891908169155978930384467671141/2814749767106560000000000000000000), (2244182750139659925793245021827/562949953421312000000000000000000), (953686227198061301472356950397/1125899906842624000000000000000000), (45981477116044806463925727559/2814749767106560000000000000000000), (-57885323457752579770142637071/2814749767106560000000000000000000), (-9082574395874928063385853031/5629499534213120000000000000000000), (1945287619726397537365516851/5629499534213120000000000000000000), (100038367766994802724215013/2814749767106560000000000000000000), (-20341548351924475038224833/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial150.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial150.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial150.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial150 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 4177327625393730076544138741885613), (Int.negOfNat 251838363368242183825923709998239), (Int.ofNat 43368511720516990011041211124089), (Int.ofNat 730816843336318185843253751247), (Int.negOfNat 947195410618662450264340940481), (Int.negOfNat 25776635971645158026271457736), (Int.ofNat 21997996562507176148219085741), (Int.ofNat 1059692118200611609322274561), (Int.negOfNat 305732055605799325521118696), (Int.negOfNat 18327573457592979269417433), (Int.ofNat 2656558048121468688466762), (Int.ofNat 176286405604543977437590), (Int.negOfNat 15461413741727619510258), (Int.negOfNat 1090597222434288713114), (Int.ofNat 63705310091866199330), (Int.ofNat 4783627030435620962), (Int.negOfNat 277097806185697167), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-4177327625393730076544138741885613/5629499534213120000000000000000000), (-251838363368242183825923709998239/5629499534213120000000000000000000), (43368511720516990011041211124089/5629499534213120000000000000000000), (730816843336318185843253751247/5629499534213120000000000000000000), (-947195410618662450264340940481/5629499534213120000000000000000000), (-3222079496455644753283932217/703687441776640000000000000000000), (21997996562507176148219085741/5629499534213120000000000000000000), (1059692118200611609322274561/5629499534213120000000000000000000), (-38216506950724915690139837/703687441776640000000000000000000), (-18327573457592979269417433/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial150.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial150.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial150.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial150 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 4516204877900161452764142502526114), (Int.negOfNat 97608679732768766570631360079007), (Int.ofNat 28352275091647764140052375064940), (Int.negOfNat 4364860209879487500138376023654), (Int.ofNat 36184103926656990981940475642), (Int.ofNat 178083245350901089920105438002), (Int.ofNat 713243847091392920082514271), (Int.negOfNat 3467281473641103651376943761), (Int.negOfNat 76751775256397510977448246), (Int.ofNat 39139477531348507753371843), (Int.ofNat 1303886599756778831761902), (Int.negOfNat 282704208075583613106800), (Int.negOfNat 11329965349177519467468), (Int.ofNat 1404741968329268836324), (Int.ofNat 62714022527469015530), (Int.negOfNat 4966195219146362162), (Int.negOfNat 202478945787172347), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-2258102438950080726382071251263057/2814749767106560000000000000000000), (-97608679732768766570631360079007/5629499534213120000000000000000000), (1417613754582388207002618753247/281474976710656000000000000000000), (-2182430104939743750069188011827/2814749767106560000000000000000000), (18092051963328495490970237821/2814749767106560000000000000000000), (89041622675450544960052719001/2814749767106560000000000000000000), (713243847091392920082514271/5629499534213120000000000000000000), (-3467281473641103651376943761/5629499534213120000000000000000000), (-38375887628198755488724123/2814749767106560000000000000000000), (39139477531348507753371843/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial150.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial150.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial150.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial150 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 4627051460489505615879288217654792), (Int.negOfNat 22574873033853499126913212794442), (Int.ofNat 15168709743012835290829964273471), (Int.ofNat 1300515873195034907192041054312), (Int.ofNat 965530117141613764192173375004), (Int.negOfNat 58572940341817226699260302714), (Int.negOfNat 30249844923545802602148058431), (Int.ofNat 584821393042812097256160229), (Int.ofNat 464589027599468535921298706), (Int.ofNat 1259920184949578969854243), (Int.negOfNat 4266373441442364568806572), (Int.negOfNat 66424313141524847669640), (Int.ofNat 25722959520782224786778), (Int.ofNat 596382499555254750384), (Int.negOfNat 109516509996140502610), (Int.negOfNat 3123305073759464062), (Int.ofNat 448888700717548857), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-578381432561188201984911027206849/703687441776640000000000000000000), (-11287436516926749563456606397221/2814749767106560000000000000000000), (15168709743012835290829964273471/5629499534213120000000000000000000), (162564484149379363399005131789/703687441776640000000000000000000), (241382529285403441048043343751/1407374883553280000000000000000000), (-29286470170908613349630151357/2814749767106560000000000000000000), (-30249844923545802602148058431/5629499534213120000000000000000000), (584821393042812097256160229/5629499534213120000000000000000000), (232294513799734267960649353/2814749767106560000000000000000000), (1259920184949578969854243/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial150.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial150.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial150.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial150 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 4589294042305904458973043469519778), (Int.ofNat 74828015509389426676721658293846), (Int.ofNat 35380850944848046713694604715163), (Int.ofNat 2943330149992239766520706456600), (Int.negOfNat 802806090036910118068193378695), (Int.negOfNat 195452317271643212924388298362), (Int.ofNat 17064506999920728998912343669), (Int.ofNat 4419737711698040327896485941), (Int.negOfNat 162384981144164676236994004), (Int.negOfNat 54023145064567190649813143), (Int.ofNat 575642599488730320042718), (Int.ofNat 404823874426461807200850), (Int.ofNat 1387965358448112249538), (Int.negOfNat 2048886109076300136794), (Int.negOfNat 23436272278126009700), (Int.ofNat 7627805994774356342), (Int.ofNat 115543169582022017), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-2294647021152952229486521734759889/2814749767106560000000000000000000), (37414007754694713338360829146923/2814749767106560000000000000000000), (35380850944848046713694604715163/5629499534213120000000000000000000), (14716650749961198832603532283/28147497671065600000000000000000), (-160561218007382023613638675739/1125899906842624000000000000000000), (-97726158635821606462194149181/2814749767106560000000000000000000), (17064506999920728998912343669/5629499534213120000000000000000000), (4419737711698040327896485941/5629499534213120000000000000000000), (-40596245286041169059248501/1407374883553280000000000000000000), (-54023145064567190649813143/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial150.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial150.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial150.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial150 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 4292077306133204313813086340621490), (Int.ofNat 215318508510084571611772169784423), (Int.ofNat 24680708680486402763343940813802), (Int.negOfNat 6647764782295555377040439251548), (Int.negOfNat 871365358374309985517821075264), (Int.ofNat 214997463812313328551016239304), (Int.ofNat 32002821107300940098514031601), (Int.negOfNat 3455216895648395215837425559), (Int.negOfNat 568417776490472943182135696), (Int.ofNat 26495833141879686181706757), (Int.ofNat 5513893833909106517593282), (Int.negOfNat 105662549408010694541550), (Int.negOfNat 33834455786095654712638), (Int.ofNat 173328971694023743906), (Int.ofNat 144582221262305046400), (Int.ofNat 431910411951209742), (Int.negOfNat 543634533942427917), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-429207730613320431381308634062149/562949953421312000000000000000000), (215318508510084571611772169784423/5629499534213120000000000000000000), (12340354340243201381671970406901/2814749767106560000000000000000000), (-1661941195573888844260109812887/1407374883553280000000000000000000), (-13615083724598593523715954301/87960930222080000000000000000000), (26874682976539166068877029913/703687441776640000000000000000000), (32002821107300940098514031601/5629499534213120000000000000000000), (-3455216895648395215837425559/5629499534213120000000000000000000), (-35526111030654558948883481/351843720888320000000000000000000), (26495833141879686181706757/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial150.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial150.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial150.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial150 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 3821482240810625362028735564067560), (Int.ofNat 227686097736225722471223542574895), (Int.negOfNat 14398252896351650867421893929136), (Int.negOfNat 2632845562618908763486216320149), (Int.ofNat 1767086990700008593657954023655), (Int.ofNat 145670238295362817408620893002), (Int.negOfNat 47117255588646440037727159569), (Int.negOfNat 4775854797354707260100538771), (Int.ofNat 527390470453715167577300994), (Int.ofNat 64710727889666485090504643), (Int.negOfNat 3218182650752897770678528), (Int.negOfNat 495309750122016375131940), (Int.ofNat 12120169073409815945522), (Int.ofNat 2509671287524142471684), (Int.negOfNat 28398197208553971390), (Int.negOfNat 9444001753904100562), (Int.ofNat 18765523235567843), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-95537056020265634050718389101689/140737488355328000000000000000000), (45537219547245144494244708514979/1125899906842624000000000000000000), (-899890806021978179213868370571/351843720888320000000000000000000), (-2632845562618908763486216320149/5629499534213120000000000000000000), (353417398140001718731590804731/1125899906842624000000000000000000), (72835119147681408704310446501/2814749767106560000000000000000000), (-47117255588646440037727159569/5629499534213120000000000000000000), (-4775854797354707260100538771/5629499534213120000000000000000000), (263695235226857583788650497/2814749767106560000000000000000000), (64710727889666485090504643/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial150.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial150.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial150.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial150 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 3415293892246804494661508076815975), (Int.ofNat 196180757203611606317755811279996), (Int.ofNat 10544315689784865263542828684618), (Int.ofNat 8342097678528004056758318699757), (Int.negOfNat 150668585647854321540672205883), (Int.negOfNat 492779032858566253831738336164), (Int.negOfNat 28338522960859328955595484671), (Int.ofNat 7831699244805032512957408339), (Int.ofNat 645750741795160636090314746), (Int.negOfNat 63168344277539543555067957), (Int.negOfNat 6439437008780004768945102), (Int.ofNat 318121412660876100374000), (Int.ofNat 39219468878677968018368), (Int.negOfNat 1104874585256858477176), (Int.negOfNat 166108643983612122030), (Int.ofNat 2788396389613608138), (Int.ofNat 571226020758512047), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-136611755689872179786460323072639/225179981368524800000000000000000), (49045189300902901579438952819999/1407374883553280000000000000000000), (5272157844892432631771414342309/2814749767106560000000000000000000), (8342097678528004056758318699757/5629499534213120000000000000000000), (-150668585647854321540672205883/5629499534213120000000000000000000), (-123194758214641563457934584041/1407374883553280000000000000000000), (-28338522960859328955595484671/5629499534213120000000000000000000), (7831699244805032512957408339/5629499534213120000000000000000000), (322875370897580318045157373/2814749767106560000000000000000000), (-63168344277539543555067957/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial150.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial150.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial150.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial150 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 2932881991522674268914581381410215), (Int.ofNat 292774288777137045684158784236364), (Int.ofNat 16823486513523909536191486970806), (Int.negOfNat 11986726869357757250077177058002), (Int.negOfNat 4186050656532698445827440038888), (Int.negOfNat 52096673155437773355361231062), (Int.ofNat 96206720659430782159445906329), (Int.ofNat 5372323847588737586343121561), (Int.negOfNat 993406504184851691913250904), (Int.negOfNat 74639282734127118566038033), (Int.ofNat 6232710387555880663571738), (Int.ofNat 555895362375551782766990), (Int.negOfNat 26988895375599304233942), (Int.negOfNat 2747992393601140896814), (Int.ofNat 86195483595723586470), (Int.ofNat 10115252220762487462), (Int.negOfNat 190556417767419533), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-586576398304534853782916276282043/1125899906842624000000000000000000), (73193572194284261421039696059091/1407374883553280000000000000000000), (8411743256761954768095743485403/2814749767106560000000000000000000), (-5993363434678878625038588529001/2814749767106560000000000000000000), (-523256332066587305728430004861/703687441776640000000000000000000), (-26048336577718886677680615531/2814749767106560000000000000000000), (96206720659430782159445906329/5629499534213120000000000000000000), (5372323847588737586343121561/5629499534213120000000000000000000), (-124175813023106461489156363/703687441776640000000000000000000), (-74639282734127118566038033/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial150.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial150.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial150.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial150 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 2438017437279656347740940267044527), (Int.ofNat 97832807532141212162406640143975), (Int.negOfNat 135068899864349646867579698528485), (Int.negOfNat 31223415196847557544316014278456), (Int.ofNat 1259012698706341809798438048393), (Int.ofNat 1021312848243669827726397410024), (Int.ofNat 37050359111092985269225252161), (Int.negOfNat 13284904897024716957376876049), (Int.negOfNat 784387030533466948397880826), (Int.ofNat 101625009298319648211887467), (Int.ofNat 7217234563527905330918332), (Int.negOfNat 529841142462566951292570), (Int.negOfNat 41729413365028134212838), (Int.ofNat 2034788667815671031456), (Int.ofNat 171098781811091503840), (Int.negOfNat 5847638943170561948), (Int.negOfNat 541553876063978947), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-2438017437279656347740940267044527/5629499534213120000000000000000000), (3913312301285648486496265605759/225179981368524800000000000000000), (-27013779972869929373515939705697/1125899906842624000000000000000000), (-3902926899605944693039501784807/703687441776640000000000000000000), (1259012698706341809798438048393/5629499534213120000000000000000000), (127664106030458728465799676253/703687441776640000000000000000000), (37050359111092985269225252161/5629499534213120000000000000000000), (-13284904897024716957376876049/5629499534213120000000000000000000), (-392193515266733474198940413/2814749767106560000000000000000000), (101625009298319648211887467/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial150.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial150.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial150.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial150 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 2979060391192438174014193300662923), (Int.negOfNat 694507292018051600026799723574733), (Int.negOfNat 211394977203779788114219910467129), (Int.ofNat 17414911341557494513792211231773), (Int.ofNat 9576858917041188519625641493998), (Int.ofNat 242581804595092792598926962175), (Int.negOfNat 153989490967574294850312357199), (Int.negOfNat 7841742555945617702254029471), (Int.ofNat 1424281779603334093282739244), (Int.ofNat 87610574848962302542323883), (Int.negOfNat 8862753980390176127101008), (Int.negOfNat 588236655995864770670820), (Int.ofNat 40165979605947010203822), (Int.ofNat 2743402631427840374464), (Int.negOfNat 139087350793663778630), (Int.negOfNat 9621448627612174362), (Int.ofNat 362347312299271223), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-2979060391192438174014193300662923/5629499534213120000000000000000000), (-694507292018051600026799723574733/5629499534213120000000000000000000), (-211394977203779788114219910467129/5629499534213120000000000000000000), (17414911341557494513792211231773/5629499534213120000000000000000000), (4788429458520594259812820746999/2814749767106560000000000000000000), (9703272183803711703957078487/225179981368524800000000000000000), (-153989490967574294850312357199/5629499534213120000000000000000000), (-7841742555945617702254029471/5629499534213120000000000000000000), (356070444900833523320684811/1407374883553280000000000000000000), (87610574848962302542323883/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial150.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial150.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial150.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial150 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 4923802926355337836783367264268021), (Int.negOfNat 1036711886756872833524331236899586), (Int.ofNat 102958972694401675632487197632032), (Int.ofNat 77570896900103946446597789565365), (Int.ofNat 2378026384140089670038830498170), (Int.negOfNat 1533351975608297056439114559694), (Int.negOfNat 81005377196122626019967387831), (Int.ofNat 17193586347921038071705551479), (Int.ofNat 1027509789943464400204005806), (Int.negOfNat 128263340093030257792112727), (Int.negOfNat 7821917581052514973894212), (Int.ofNat 687361339723102634010870), (Int.ofNat 41021784465380447375108), (Int.negOfNat 2777077571205651435566), (Int.negOfNat 158997861863243243750), (Int.ofNat 8594539935742727298), (Int.ofNat 511881731369445847), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-4923802926355337836783367264268021/5629499534213120000000000000000000), (-518355943378436416762165618449793/2814749767106560000000000000000000), (3217467896700052363515224926001/175921860444160000000000000000000), (15514179380020789289319557913073/1125899906842624000000000000000000), (237802638414008967003883049817/562949953421312000000000000000000), (-766675987804148528219557279847/2814749767106560000000000000000000), (-81005377196122626019967387831/5629499534213120000000000000000000), (17193586347921038071705551479/5629499534213120000000000000000000), (513754894971732200102002903/2814749767106560000000000000000000), (-128263340093030257792112727/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial150.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial150.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial150.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial150 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 5978635127318590799858804283093852), (Int.ofNat 252278337256159096993441484254952), (Int.ofNat 496083414349640694338315449043372), (Int.ofNat 32992927408967404178019706835143), (Int.negOfNat 12440004779697544031666015889501), (Int.negOfNat 899050482928085337674489332785), (Int.ofNat 174192690333578375069555023769), (Int.ofNat 11965609360449728206887649861), (Int.negOfNat 1593420394606393836774842784), (Int.negOfNat 99895340600841231627986443), (Int.ofNat 10250123252496443960908778), (Int.ofNat 579185533848588648824750), (Int.negOfNat 48695490144321058924172), (Int.negOfNat 2475970120982283950864), (Int.ofNat 176865178456836828900), (Int.ofNat 8073796834152552212), (Int.negOfNat 524247491932945213), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-1494658781829647699964701070773463/1407374883553280000000000000000000), (31534792157019887124180185531869/703687441776640000000000000000000), (124020853587410173584578862260843/1407374883553280000000000000000000), (32992927408967404178019706835143/5629499534213120000000000000000000), (-12440004779697544031666015889501/5629499534213120000000000000000000), (-179810096585617067534897866557/1125899906842624000000000000000000), (174192690333578375069555023769/5629499534213120000000000000000000), (11965609360449728206887649861/5629499534213120000000000000000000), (-49794387331449807399213837/175921860444160000000000000000000), (-99895340600841231627986443/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial150.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial150.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial150.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial150.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial150 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial150 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial150 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 6658745130367945812022465279993679), (Int.negOfNat 471436756668536561451227516661771), (Int.ofNat 516214379446278053379900153086542), (Int.negOfNat 29600696464956638552605164959101), (Int.negOfNat 12669693746941752348549111893104), (Int.ofNat 867544391468499581995919338209), (Int.ofNat 175826365401341534647457383669), (Int.negOfNat 11794059423017220525636807861), (Int.negOfNat 1600254006304603115293110784), (Int.ofNat 99331254470318228086475043), (Int.ofNat 10268161969133929924578178), (Int.negOfNat 577965743119544368015550), (Int.negOfNat 48728498011527669228972), (Int.ofNat 2474469763381983482464), (Int.ofNat 176865178456836828900), (Int.negOfNat 8073796834152552212), (Int.negOfNat 524247491932945213), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-6658745130367945812022465279993679/5629499534213120000000000000000000), (-471436756668536561451227516661771/5629499534213120000000000000000000), (258107189723139026689950076543271/2814749767106560000000000000000000), (-29600696464956638552605164959101/5629499534213120000000000000000000), (-791855859183859521784319493319/351843720888320000000000000000000), (867544391468499581995919338209/5629499534213120000000000000000000), (175826365401341534647457383669/5629499534213120000000000000000000), (-11794059423017220525636807861/5629499534213120000000000000000000), (-3125496106063677959556857/10995116277760000000000000000000), (99331254470318228086475043/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial150.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial150.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial150.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 5939126782490864331341670545963141), (Int.ofNat 929295892712286736778988359055700), (Int.ofNat 135903059046489427067067962363222), (Int.negOfNat 76933919293697708365674361030800), (Int.ofNat 1969692175286918603238808880203), (Int.ofNat 1531839205208391833744805459211), (Int.negOfNat 78038079144746916389329931431), (Int.negOfNat 17189849999812506512550014079), (Int.ofNat 1015055632512515859586820806), (Int.ofNat 128253234875729482156942727), (Int.negOfNat 7789026490835717882368012), (Int.negOfNat 687340334716698427453270), (Int.ofNat 40962520340168578873308), (Int.ofNat 2777077571205651435566), (Int.negOfNat 158997861863243243750), (Int.negOfNat 8594539935742727298), (Int.ofNat 511881731369445847), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-5939126782490864331341670545963141/5629499534213120000000000000000000), (9292958927122867367789883590557/56294995342131200000000000000000), (67951529523244713533533981181611/2814749767106560000000000000000000), (-192334798234244270914185902577/14073748835532800000000000000000), (1969692175286918603238808880203/5629499534213120000000000000000000), (1531839205208391833744805459211/5629499534213120000000000000000000), (-78038079144746916389329931431/5629499534213120000000000000000000), (-17189849999812506512550014079/5629499534213120000000000000000000), (507527816256257929793410403/2814749767106560000000000000000000), (128253234875729482156942727/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial150.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial150.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial150.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 4078738599780357158489046689990253), (Int.ofNat 713882444304410225067850837694052), (Int.negOfNat 183857394396424142154304177675369), (Int.negOfNat 19650130883790770006761960953388), (Int.ofNat 9318927168142510140912883865964), (Int.negOfNat 213513063050369667022794099819), (Int.negOfNat 152264168118995994128163112549), (Int.ofNat 7674971589799068825991768671), (Int.ofNat 1417137702370101806339533644), (Int.negOfNat 87058090319375899845000083), (Int.negOfNat 8843922018663970097351608), (Int.ofNat 587040870988425297356020), (Int.ofNat 40131471381140099430622), (Int.negOfNat 2741902273827539906064), (Int.negOfNat 139087350793663778630), (Int.ofNat 9621448627612174362), (Int.ofNat 362347312299271223), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-4078738599780357158489046689990253/5629499534213120000000000000000000), (178470611076102556266962709423513/1407374883553280000000000000000000), (-183857394396424142154304177675369/5629499534213120000000000000000000), (-4912532720947692501690490238347/1407374883553280000000000000000000), (2329731792035627535228220966491/1407374883553280000000000000000000), (-213513063050369667022794099819/5629499534213120000000000000000000), (-152264168118995994128163112549/5629499534213120000000000000000000), (7674971589799068825991768671/5629499534213120000000000000000000), (354284425592525451584883411/1407374883553280000000000000000000), (-87058090319375899845000083/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial150.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial150.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial150.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 3409785929979816981349271124217964), (Int.negOfNat 807686974082303957192866638989), (Int.negOfNat 124515564647066305345116298069695), (Int.ofNat 28260554661277805771554351846901), (Int.ofNat 1343017077988621468454525176697), (Int.negOfNat 987522052886491448775656096641), (Int.ofNat 36056028799608770419700803461), (Int.ofNat 13094503545190519340064747049), (Int.negOfNat 779962945311277730933987826), (Int.negOfNat 100995832080506554778994867), (Int.ofNat 7205456229492781204370932), (Int.ofNat 528479567940294276219570), (Int.negOfNat 41707658179823777421038), (Int.negOfNat 2032538131415220328856), (Int.ofNat 171098781811091503840), (Int.ofNat 5847638943170561948), (Int.negOfNat 541553876063978947), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-852446482494954245337317781054491/1407374883553280000000000000000000), (-807686974082303957192866638989/5629499534213120000000000000000000), (-24903112929413261069023259613939/1125899906842624000000000000000000), (28260554661277805771554351846901/5629499534213120000000000000000000), (1343017077988621468454525176697/5629499534213120000000000000000000), (-987522052886491448775656096641/5629499534213120000000000000000000), (36056028799608770419700803461/5629499534213120000000000000000000), (13094503545190519340064747049/5629499534213120000000000000000000), (-389981472655638865466993913/2814749767106560000000000000000000), (-100995832080506554778994867/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial150.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial150.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial150.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 3689750979557240342055715922887882), (Int.negOfNat 183969056365164518734020312270483), (Int.ofNat 13963093193863773750822980284666), (Int.ofNat 10792890529471731609335645230037), (Int.negOfNat 3869831110220763996366408474981), (Int.ofNat 61079758236701418558390063449), (Int.ofNat 93407053287958605976951870859), (Int.negOfNat 5419085067763672557699815761), (Int.negOfNat 981328183674732940719266104), (Int.ofNat 74792000187894203507726233), (Int.ofNat 6200687005838077689303538), (Int.negOfNat 556225441047617885814990), (Int.negOfNat 26931131607987736200542), (Int.ofNat 2748742572401291131014), (Int.ofNat 86195483595723586470), (Int.negOfNat 10115252220762487462), (Int.negOfNat 190556417767419533), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-1844875489778620171027857961443941/2814749767106560000000000000000000), (-183969056365164518734020312270483/5629499534213120000000000000000000), (6981546596931886875411490142333/2814749767106560000000000000000000), (10792890529471731609335645230037/5629499534213120000000000000000000), (-3869831110220763996366408474981/5629499534213120000000000000000000), (61079758236701418558390063449/5629499534213120000000000000000000), (93407053287958605976951870859/5629499534213120000000000000000000), (-5419085067763672557699815761/5629499534213120000000000000000000), (-122666022959341617589908263/703687441776640000000000000000000), (74792000187894203507726233/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial150.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial150.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial150.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 3970379735125517569233438345015498), (Int.negOfNat 102851393195679556724692315553402), (Int.ofNat 8147450376408569861325901561038), (Int.negOfNat 7099021154875111188312509414495), (Int.ofNat 88015208754393097794536690150), (Int.ofNat 469695090657448958012625121811), (Int.negOfNat 30446455210767436106974252271), (Int.negOfNat 7694214013535920426093211139), (Int.ofNat 654841955338349677040941746), (Int.ofNat 62710557181586198174016557), (Int.negOfNat 6463539224950045897660902), (Int.negOfNat 317128926108277340527400), (Int.ofNat 39262979249086681601968), (Int.ofNat 1103374227656558008776), (Int.negOfNat 166108643983612122030), (Int.negOfNat 2788396389613608138), (Int.ofNat 571226020758512047), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-1985189867562758784616719172507749/2814749767106560000000000000000000), (-51425696597839778362346157776701/2814749767106560000000000000000000), (4073725188204284930662950780519/2814749767106560000000000000000000), (-1419804230975022237662501882899/1125899906842624000000000000000000), (1760304175087861955890733803/112589990684262400000000000000000), (469695090657448958012625121811/5629499534213120000000000000000000), (-30446455210767436106974252271/5629499534213120000000000000000000), (-7694214013535920426093211139/5629499534213120000000000000000000), (327420977669174838520470873/2814749767106560000000000000000000), (62710557181586198174016557/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial150.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial150.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial150.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 4186587189252411688157535597560480), (Int.negOfNat 123571096846340592755607376443956), (Int.negOfNat 5854542113099545452945640373136), (Int.ofNat 4615263826525144967485735170777), (Int.ofNat 1695010529663463639048853062691), (Int.negOfNat 179511812783878765766003656869), (Int.negOfNat 46653928337766501215412117169), (Int.ofNat 4975891941518207296548967971), (Int.ofNat 525485301861015493567976994), (Int.negOfNat 65376122818658597120600643), (Int.negOfNat 3213165510131444049618128), (Int.ofNat 496751593775905125264340), (Int.ofNat 12111166927808013135122), (Int.negOfNat 2511921823924593174284), (Int.negOfNat 28398197208553971390), (Int.ofNat 9444001753904100562), (Int.ofNat 18765523235567843), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-26166169932827573050984597484753/35184372088832000000000000000000), (-30892774211585148188901844110989/1407374883553280000000000000000000), (-365908882068721590809102523321/351843720888320000000000000000000), (4615263826525144967485735170777/5629499534213120000000000000000000), (1695010529663463639048853062691/5629499534213120000000000000000000), (-179511812783878765766003656869/5629499534213120000000000000000000), (-46653928337766501215412117169/5629499534213120000000000000000000), (4975891941518207296548967971/5629499534213120000000000000000000), (262742650930507746783988497/2814749767106560000000000000000000), (-65376122818658597120600643/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial150.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial150.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial150.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 4401099779983471597925635682558777), (Int.negOfNat 58078284936512082303066696126967), (Int.ofNat 40921008753792092611790727319572), (Int.ofNat 6879206614304638230818326520766), (Int.negOfNat 1202737804290710979518737685000), (Int.negOfNat 228589484546181396942932928058), (Int.ofNat 34643310324940512450804862001), (Int.ofNat 3540920567019928966554774159), (Int.negOfNat 579652110563731750131556696), (Int.negOfNat 26783305325729209725583157), (Int.ofNat 5543621169222659848236682), (Int.ofNat 106286698169735689395950), (Int.negOfNat 33887718480906321340838), (Int.negOfNat 174079150494173978106), (Int.ofNat 144582221262305046400), (Int.negOfNat 431910411951209742), (Int.negOfNat 543634533942427917), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-4401099779983471597925635682558777/5629499534213120000000000000000000), (-58078284936512082303066696126967/5629499534213120000000000000000000), (10230252188448023152947681829893/1407374883553280000000000000000000), (3439603307152319115409163260383/2814749767106560000000000000000000), (-240547560858142195903747537/1125899906842624000000000000000), (-114294742273090698471466464029/2814749767106560000000000000000000), (34643310324940512450804862001/5629499534213120000000000000000000), (3540920567019928966554774159/5629499534213120000000000000000000), (-72456513820466468766444587/703687441776640000000000000000000), (-26783305325729209725583157/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial150.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial150.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial150.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 4322583268161951712079310980354615), (Int.ofNat 138992791160323694568237591644605), (Int.ofNat 44639711596787005281669277783963), (Int.negOfNat 5457277078819323726371479471918), (Int.negOfNat 1100995102630936839856783362538), (Int.ofNat 215385231024112755640865422079), (Int.ofNat 19559198271144254975103132499), (Int.negOfNat 4524780520506788726357399741), (Int.negOfNat 173069654294872057671261804), (Int.ofNat 54366852952888106975854943), (Int.ofNat 603941649560748650038518), (Int.negOfNat 405566551438610539058850), (Int.ofNat 1336953200037896323938), (Int.ofNat 2050386466676600605194), (Int.negOfNat 23436272278126009700), (Int.negOfNat 7627805994774356342), (Int.ofNat 115543169582022017), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-864516653632390342415862196070923/1125899906842624000000000000000000), (27798558232064738913647518328921/1125899906842624000000000000000000), (44639711596787005281669277783963/5629499534213120000000000000000000), (-2728638539409661863185739735959/2814749767106560000000000000000000), (-550497551315468419928391681269/2814749767106560000000000000000000), (215385231024112755640865422079/5629499534213120000000000000000000), (19559198271144254975103132499/5629499534213120000000000000000000), (-4524780520506788726357399741/5629499534213120000000000000000000), (-43267413573718014417815451/1407374883553280000000000000000000), (54366852952888106975854943/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial150.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial150.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial150.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 3919764694068574979916424106325145), (Int.ofNat 235738251541591519034658036296633), (Int.ofNat 4292861467300319186482313927021), (Int.negOfNat 5079232963041601098617458221277), (Int.ofNat 976701695163377964772095635627), (Int.ofNat 95726232725455673621042767648), (Int.negOfNat 30110086288459112056643214031), (Int.negOfNat 789223324949925221752524029), (Int.ofNat 463858127722870538085755506), (Int.negOfNat 586792153685135966467043), (Int.negOfNat 4264387996658352644775172), (Int.ofNat 64967465911633092853240), (Int.ofNat 25719958805581623849978), (Int.negOfNat 594131963154804047784), (Int.negOfNat 109516509996140502610), (Int.ofNat 3123305073759464062), (Int.ofNat 448888700717548857), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-783952938813714995983284821265029/1125899906842624000000000000000000), (235738251541591519034658036296633/5629499534213120000000000000000000), (4292861467300319186482313927021/5629499534213120000000000000000000), (-5079232963041601098617458221277/5629499534213120000000000000000000), (976701695163377964772095635627/5629499534213120000000000000000000), (2991444772670489800657586489/175921860444160000000000000000000), (-30110086288459112056643214031/5629499534213120000000000000000000), (-789223324949925221752524029/5629499534213120000000000000000000), (231929063861435269042877753/2814749767106560000000000000000000), (-586792153685135966467043/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial150.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial150.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial150.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 3454973895991079950687411314222917), (Int.ofNat 225189871771787917803891992785046), (Int.negOfNat 2057536520147227920109261570153), (Int.ofNat 2071821916539133188818654745549), (Int.ofNat 371902541763647595773580566825), (Int.negOfNat 155419719896267756978341572419), (Int.negOfNat 1652732219333443534740280929), (Int.ofNat 3342482465500110078201988161), (Int.negOfNat 66869545344011378466781246), (Int.negOfNat 38728440428561794517965043), (Int.ofNat 1277805271396833252503502), (Int.ofNat 281814496018605435345600), (Int.negOfNat 11283454263568204947068), (Int.negOfNat 1403241610728968367924), (Int.ofNat 62714022527469015530), (Int.ofNat 4966195219146362162), (Int.negOfNat 202478945787172347), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-3454973895991079950687411314222917/5629499534213120000000000000000000), (112594935885893958901945996392523/2814749767106560000000000000000000), (-2057536520147227920109261570153/5629499534213120000000000000000000), (2071821916539133188818654745549/5629499534213120000000000000000000), (14876101670545903830943222673/225179981368524800000000000000000), (-155419719896267756978341572419/5629499534213120000000000000000000), (-1652732219333443534740280929/5629499534213120000000000000000000), (3342482465500110078201988161/5629499534213120000000000000000000), (-33434772672005689233390623/2814749767106560000000000000000000), (-38728440428561794517965043/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial150.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial150.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial150.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 2994985769145449013914754961015180), (Int.ofNat 242320668229106201330080296653878), (Int.ofNat 8438376595429908299259617039879), (Int.ofNat 139475940802033175945772368038), (Int.negOfNat 549400306562862161030971042574), (Int.ofNat 14589758647618123682439732212), (Int.ofNat 19170110646487204033723156571), (Int.negOfNat 995607366510281591276136361), (Int.negOfNat 293904065513321990748996496), (Int.ofNat 18115315371499522370005433), (Int.ofNat 2625336494622893704469962), (Int.negOfNat 175826546000051883872990), (Int.negOfNat 15405150331716351945258), (Int.ofNat 1089847043634138478914), (Int.ofNat 63705310091866199330), (Int.negOfNat 4783627030435620962), (Int.negOfNat 277097806185697167), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-149749288457272450695737748050759/281474976710656000000000000000000), (121160334114553100665040148326939/2814749767106560000000000000000000), (8438376595429908299259617039879/5629499534213120000000000000000000), (69737970401016587972886184019/2814749767106560000000000000000000), (-274700153281431080515485521287/2814749767106560000000000000000000), (3647439661904530920609933053/1407374883553280000000000000000000), (19170110646487204033723156571/5629499534213120000000000000000000), (-995607366510281591276136361/5629499534213120000000000000000000), (-18369004094582624421812281/351843720888320000000000000000000), (18115315371499522370005433/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial150.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial150.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial150.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 2482762891503813164453558470231418), (Int.ofNat 264320812599419591528818008992833), (Int.ofNat 769828323272517914503331496240), (Int.negOfNat 1560226320425027566968657524880), (Int.ofNat 238157973473682630666490277755), (Int.ofNat 80670501100468473471656469309), (Int.negOfNat 9926167308960992057387977961), (Int.negOfNat 1748747655318592716621680051), (Int.ofNat 203474507928468233855686826), (Int.ofNat 19692665901477158099054833), (Int.negOfNat 2306067041701445812722732), (Int.negOfNat 136960952360480249005130), (Int.ofNat 16555269306379077447338), (Int.ofNat 647491005457042688344), (Int.negOfNat 81580031646671780940), (Int.negOfNat 2070020095599124052), (Int.ofNat 232151090481705447), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-1241381445751906582226779235115709/2814749767106560000000000000000000), (264320812599419591528818008992833/5629499534213120000000000000000000), (9622854040906473931291643703/70368744177664000000000000000000), (-19502829005312844587108219061/70368744177664000000000000000000), (47631594694736526133298055551/1125899906842624000000000000000000), (80670501100468473471656469309/5629499534213120000000000000000000), (-9926167308960992057387977961/5629499534213120000000000000000000), (-1748747655318592716621680051/5629499534213120000000000000000000), (101737253964234116927843413/2814749767106560000000000000000000), (19692665901477158099054833/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial150.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial150.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial150.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 1957931292447238349849269522579322), (Int.ofNat 260303653744632405932127459513011), (Int.ofNat 446601033127180125175204784314), (Int.ofNat 1435650119716550378856632309288), (Int.ofNat 232403852670452081102723143024), (Int.negOfNat 75323781517154842535357132832), (Int.negOfNat 7104333801103925173042008651), (Int.ofNat 1858356849702042641532472671), (Int.ofNat 103248420324263760111753756), (Int.negOfNat 25535615469654179480287283), (Int.negOfNat 837564503067053936719092), (Int.ofNat 217714302521071223485320), (Int.ofNat 4267652388548787850378), (Int.negOfNat 1255921906753279524464), (Int.negOfNat 15062540698705970570), (Int.ofNat 5318457786695788662), (Int.ofNat 105306911653845477), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-978965646223619174924634761289661/2814749767106560000000000000000000), (260303653744632405932127459513011/5629499534213120000000000000000000), (223300516563590062587602392157/2814749767106560000000000000000000), (179456264964568797357079038661/703687441776640000000000000000000), (14525240791903255068920196439/351843720888320000000000000000000), (-2353868172411088829229910401/175921860444160000000000000000000), (-7104333801103925173042008651/5629499534213120000000000000000000), (1858356849702042641532472671/5629499534213120000000000000000000), (25812105081065940027938439/1407374883553280000000000000000000), (-25535615469654179480287283/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial150.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial150.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial150.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1422948134216529819783721250166594), (Int.ofNat 280242485834656383479225744585258), (Int.ofNat 8219989461446322427695515801423), (Int.ofNat 230100926210163782080964284774), (Int.negOfNat 416055308639773531698896528008), (Int.negOfNat 9995112583243105671919364589), (Int.ofNat 13699630757375819969123142331), (Int.ofNat 150999300267729236297441221), (Int.negOfNat 236277932360342905295615206), (Int.negOfNat 556284828164343432961173), (Int.ofNat 2451569820829685273513812), (Int.negOfNat 7817906476732868723070), (Int.negOfNat 16757634333944795434808), (Int.ofNat 109234384971892770766), (Int.ofNat 80625078778181955050), (Int.negOfNat 909442062890433598), (Int.negOfNat 261823235176238547), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-711474067108264909891860625083297/2814749767106560000000000000000000), (140121242917328191739612872292629/2814749767106560000000000000000000), (8219989461446322427695515801423/5629499534213120000000000000000000), (115050463105081891040482142387/2814749767106560000000000000000000), (-52006913579971691462362066001/703687441776640000000000000000000), (-9995112583243105671919364589/5629499534213120000000000000000000), (13699630757375819969123142331/5629499534213120000000000000000000), (150999300267729236297441221/5629499534213120000000000000000000), (-118138966180171452647807603/2814749767106560000000000000000000), (-556284828164343432961173/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial150.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial150.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial150.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 833881365588309366451603878269306), (Int.ofNat 304237089324487495862925689983230), (Int.ofNat 1806003897544699024465178913893), (Int.negOfNat 1612518216112185466912096969447), (Int.ofNat 111991113362410225147054539409), (Int.ofNat 78064076883963709464800782722), (Int.negOfNat 3810549142549711139072074069), (Int.negOfNat 1777281294834611766843618161), (Int.ofNat 70519738188674151970528484), (Int.ofNat 23077540013739798177830943), (Int.negOfNat 799898280453359499779878), (Int.negOfNat 190915046301055905850250), (Int.ofNat 5976703911970651505672), (Int.ofNat 1085266477847172590164), (Int.negOfNat 30497445390218691000), (Int.negOfNat 4616591482840576212), (Int.ofNat 76374697776183913), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-416940682794154683225801939134653/2814749767106560000000000000000000), (30423708932448749586292568998323/562949953421312000000000000000000), (1806003897544699024465178913893/5629499534213120000000000000000000), (-1612518216112185466912096969447/5629499534213120000000000000000000), (111991113362410225147054539409/5629499534213120000000000000000000), (39032038441981854732400391361/2814749767106560000000000000000000), (-3810549142549711139072074069/5629499534213120000000000000000000), (-1777281294834611766843618161/5629499534213120000000000000000000), (17629934547168537992632121/1407374883553280000000000000000000), (23077540013739798177830943/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial150.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial150.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial150.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 227236084571757015124766096045934), (Int.ofNat 300531217612001400214357268271001), (Int.negOfNat 826373623025402279836705557173), (Int.ofNat 1032053959988125672489911781575), (Int.ofNat 320687233644010703626198394658), (Int.negOfNat 50013316357039171578400306731), (Int.negOfNat 10238707721389054788222984111), (Int.ofNat 1148776294081624961247507559), (Int.ofNat 172814834814412819737156016), (Int.negOfNat 15170612132295203211807157), (Int.negOfNat 1778318959946390032016302), (Int.ofNat 128296773365661708373010), (Int.ofNat 12189563488412379531848), (Int.negOfNat 746378098838997981396), (Int.negOfNat 59304093740062947280), (Int.ofNat 3254623381741799028), (Int.ofNat 167077401951359487), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-113618042285878507562383048022967/2814749767106560000000000000000000), (300531217612001400214357268271001/5629499534213120000000000000000000), (-826373623025402279836705557173/5629499534213120000000000000000000), (41282158399525026899596471263/225179981368524800000000000000000), (160343616822005351813099197329/2814749767106560000000000000000000), (-50013316357039171578400306731/5629499534213120000000000000000000), (-10238707721389054788222984111/5629499534213120000000000000000000), (1148776294081624961247507559/5629499534213120000000000000000000), (10800927175900801233572251/351843720888320000000000000000000), (-15170612132295203211807157/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial150.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial150.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial150.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 381834581483179669739403051287151), (Int.ofNat 314554720060418803318501118412229), (Int.ofNat 7599656479102471941255160113097), (Int.ofNat 809489001886765544342255321106), (Int.negOfNat 356986673228376693814072180909), (Int.negOfNat 39149868686138189645808563862), (Int.ofNat 11447335991578457297485988649), (Int.ofNat 906657331472870364413152761), (Int.negOfNat 193416662251366418726106434), (Int.negOfNat 12140099046076167195475173), (Int.ofNat 1988414265739172207026788), (Int.ofNat 104384194046328757402990), (Int.negOfNat 13594720624663354622992), (Int.negOfNat 617820522067389707694), (Int.ofNat 65609137469251047930), (Int.ofNat 2879818496037355682), (Int.negOfNat 210683390593773773), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(381834581483179669739403051287151/5629499534213120000000000000000000), (314554720060418803318501118412229/5629499534213120000000000000000000), (7599656479102471941255160113097/5629499534213120000000000000000000), (404744500943382772171127660553/2814749767106560000000000000000000), (-356986673228376693814072180909/5629499534213120000000000000000000), (-19574934343069094822904281931/2814749767106560000000000000000000), (11447335991578457297485988649/5629499534213120000000000000000000), (906657331472870364413152761/5629499534213120000000000000000000), (-96708331125683209363053217/2814749767106560000000000000000000), (-12140099046076167195475173/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial150.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial150.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial150.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1041649118524213149992192751800439), (Int.ofNat 342500690002944038013892027903030), (Int.ofNat 3735865706652765542343163179856), (Int.negOfNat 1651673418336406560491018440504), (Int.negOfNat 44099297797539362517984146681), (Int.ofNat 80864735117149467506060383194), (Int.ofNat 1659570168235723335409102711), (Int.negOfNat 1856827519312972460797073609), (Int.negOfNat 35388781033306086030246956), (Int.ofNat 24277299938888878476085257), (Int.ofNat 455727401832666260593492), (Int.negOfNat 202119793704370428774060), (Int.negOfNat 3778639210928656697958), (Int.ofNat 1154014318910228227776), (Int.ofNat 21237980399051739850), (Int.negOfNat 4802275175201421178), (Int.negOfNat 5177222317685497), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(1041649118524213149992192751800439/5629499534213120000000000000000000), (34250069000294403801389202790303/562949953421312000000000000000000), (233491606665797846396447698741/351843720888320000000000000000000), (-206459177292050820061377305063/703687441776640000000000000000000), (-44099297797539362517984146681/5629499534213120000000000000000000), (40432367558574733753030191597/2814749767106560000000000000000000), (1659570168235723335409102711/5629499534213120000000000000000000), (-1856827519312972460797073609/5629499534213120000000000000000000), (-8847195258326521507561739/1407374883553280000000000000000000), (24277299938888878476085257/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial150.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial150.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial150.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 1730134612676138358782747291749881), (Int.ofNat 342188575096281368729249444868662), (Int.negOfNat 1564926294264210985610957280290), (Int.ofNat 521309038594300162986884743175), (Int.ofNat 400000436466850559310468730742), (Int.negOfNat 24402407602895472456695425898), (Int.negOfNat 13408230161753286976761747029), (Int.ofNat 475476476901411534419596189), (Int.ofNat 234515177688645883483698094), (Int.negOfNat 4714052275285760058780827), (Int.negOfNat 2470499852743112699106248), (Int.ofNat 25317943504225883501270), (Int.ofNat 17137382193538929124642), (Int.negOfNat 66053903406879888156), (Int.negOfNat 83172667417109406680), (Int.negOfNat 132917503465190332), (Int.ofNat 240355535288306873), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(1730134612676138358782747291749881/5629499534213120000000000000000000), (171094287548140684364624722434331/2814749767106560000000000000000000), (-156492629426421098561095728029/562949953421312000000000000000000), (20852361543772006519475389727/225179981368524800000000000000000), (200000218233425279655234365371/2814749767106560000000000000000000), (-12201203801447736228347712949/2814749767106560000000000000000000), (-13408230161753286976761747029/5629499534213120000000000000000000), (475476476901411534419596189/5629499534213120000000000000000000), (117257588844322941741849047/2814749767106560000000000000000000), (-4714052275285760058780827/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial150.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial150.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial150.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 2417299606861653449348051418057433), (Int.ofNat 350888359875034916140772888369119), (Int.ofNat 6684189649266791076608111750271), (Int.ofNat 1226047581401290373561061905193), (Int.negOfNat 301803832685022547796622055179), (Int.negOfNat 67342552887742607280311859864), (Int.ofNat 9357004591675040304114654859), (Int.ofNat 1703066435052722197984485479), (Int.negOfNat 143669715660496943416802964), (Int.negOfNat 24070712864772118124231287), (Int.ofNat 1268733137543451018807218), (Int.ofNat 211904064522561517753550), (Int.negOfNat 7089948101891964693582), (Int.negOfNat 1252953056879228322666), (Int.ofNat 26679028051491210010), (Int.ofNat 5296078768351734278), (Int.negOfNat 166613672214166193), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(2417299606861653449348051418057433/5629499534213120000000000000000000), (350888359875034916140772888369119/5629499534213120000000000000000000), (6684189649266791076608111750271/5629499534213120000000000000000000), (1226047581401290373561061905193/5629499534213120000000000000000000), (-301803832685022547796622055179/5629499534213120000000000000000000), (-8417819110967825910038982483/703687441776640000000000000000000), (9357004591675040304114654859/5629499534213120000000000000000000), (1703066435052722197984485479/5629499534213120000000000000000000), (-35917428915124235854200741/1407374883553280000000000000000000), (-24070712864772118124231287/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial150.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial150.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial150.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 3149407074453050565722004567539374), (Int.ofNat 379658150662773036841599984595067), (Int.ofNat 4451464718201762406589773015740), (Int.negOfNat 1790805215674215819422897582006), (Int.negOfNat 170226813105309173955248388562), (Int.ofNat 90516235100754635107624331698), (Int.ofNat 7667805219906375231417360949), (Int.negOfNat 2022547519347635163738084079), (Int.negOfNat 167541139216553290153423794), (Int.ofNat 24318224831274628360371217), (Int.ofNat 2054168245998355903701658), (Int.negOfNat 177671114406843574894760), (Int.negOfNat 15663022675335655885632), (Int.ofNat 862523838862463197176), (Int.ofNat 80804825841632249770), (Int.negOfNat 2926325050091763478), (Int.negOfNat 270027679982839973), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(1574703537226525282861002283769687/2814749767106560000000000000000000), (379658150662773036841599984595067/5629499534213120000000000000000000), (222573235910088120329488650787/281474976710656000000000000000000), (-895402607837107909711448791003/2814749767106560000000000000000000), (-85113406552654586977624194281/2814749767106560000000000000000000), (45258117550377317553812165849/2814749767106560000000000000000000), (7667805219906375231417360949/5629499534213120000000000000000000), (-2022547519347635163738084079/5629499534213120000000000000000000), (-83770569608276645076711897/2814749767106560000000000000000000), (24318224831274628360371217/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial150.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial150.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial150.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 3912578780999695306099577296202872), (Int.ofNat 378227157503738723820097722625982), (Int.negOfNat 2826798424339988396164207368651), (Int.ofNat 415341618605660670263342057868), (Int.ofNat 557601761492814486133909121136), (Int.negOfNat 3318356185039944755087825526), (Int.negOfNat 19480086447774932600519369729), (Int.negOfNat 440832812581523327654927009), (Int.ofNat 329037420482237037998593914), (Int.ofNat 12443958083042027586274437), (Int.negOfNat 3139297559494579094307368), (Int.negOfNat 147870430856309144941460), (Int.ofNat 18890162896586474742722), (Int.ofNat 1009471401466421995276), (Int.negOfNat 78543191939571722950), (Int.negOfNat 4624828301493347378), (Int.ofNat 338404566746017883), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(489072347624961913262447162025359/703687441776640000000000000000000), (189113578751869361910048861312991/2814749767106560000000000000000000), (-2826798424339988396164207368651/5629499534213120000000000000000000), (103835404651415167565835514467/1407374883553280000000000000000000), (34850110093300905383369320071/351843720888320000000000000000000), (-1659178092519972377543912763/2814749767106560000000000000000000), (-19480086447774932600519369729/5629499534213120000000000000000000), (-440832812581523327654927009/5629499534213120000000000000000000), (164518710241118518999296957/2814749767106560000000000000000000), (12443958083042027586274437/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial150.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial150.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial150.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 4668648095538251378303700952029738), (Int.ofNat 385892555764326728177157749906034), (Int.ofNat 8418817924805148896320931650757), (Int.ofNat 1984166849230988369712103479380), (Int.negOfNat 394890519835497597485069922185), (Int.negOfNat 129145721077222242658972124918), (Int.ofNat 8097548093758870578598865411), (Int.ofNat 3370403812964598944811802699), (Int.negOfNat 33985225485367599492633536), (Int.negOfNat 44153547887402544127476877), (Int.negOfNat 641950814160777105626078), (Int.ofNat 334216172329800828789990), (Int.ofNat 8987935576629086706242), (Int.negOfNat 1667744085354895365226), (Int.negOfNat 56917221248163230300), (Int.ofNat 6146631851656581358), (Int.ofNat 242436193166755843), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(2334324047769125689151850476014869/2814749767106560000000000000000000), (192946277882163364088578874953017/2814749767106560000000000000000000), (8418817924805148896320931650757/5629499534213120000000000000000000), (99208342461549418485605173969/281474976710656000000000000000000), (-78978103967099519497013984437/1125899906842624000000000000000000), (-64572860538611121329486062459/2814749767106560000000000000000000), (8097548093758870578598865411/5629499534213120000000000000000000), (3370403812964598944811802699/5629499534213120000000000000000000), (-531019148208868742072399/87960930222080000000000000000000), (-44153547887402544127476877/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial150.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial150.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial150.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 5480449299642634657905712322450410), (Int.ofNat 423338419764102821604489533409797), (Int.ofNat 4461092243024654751988416466858), (Int.negOfNat 3451272870464773488868215485152), (Int.negOfNat 466894690572526037878417561576), (Int.ofNat 151928638885444728290295126096), (Int.ofNat 24728023163685324568704870659), (Int.negOfNat 2352566533321921771051053201), (Int.negOfNat 506090543516295948375106364), (Int.ofNat 11776794384848246877126623), (Int.ofNat 5005508647337650199453278), (Int.ofNat 12320899078436556873590), (Int.negOfNat 30310862414811386985542), (Int.negOfNat 446492463611206313526), (Int.ofNat 126570464549785044000), (Int.ofNat 2808632542363603158), (Int.negOfNat 472713259563607743), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(548044929964263465790571232245041/562949953421312000000000000000000), (423338419764102821604489533409797/5629499534213120000000000000000000), (2230546121512327375994208233429/2814749767106560000000000000000000), (-107852277202024171527131733911/175921860444160000000000000000000), (-58361836321565754734802195197/703687441776640000000000000000000), (9495539930340295518143445381/351843720888320000000000000000000), (24728023163685324568704870659/5629499534213120000000000000000000), (-2352566533321921771051053201/5629499534213120000000000000000000), (-126522635879073987093776591/1407374883553280000000000000000000), (11776794384848246877126623/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial150.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial150.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial150.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 6315914687285900305878660227883580), (Int.ofNat 400208916275258310615336883342585), (Int.negOfNat 11740632924391101266950432972064), (Int.ofNat 760117392549674435047430827729), (Int.ofNat 1421941925945738421559423858745), (Int.ofNat 85706568344345611190672835898), (Int.negOfNat 41764620920899434574360912071), (Int.negOfNat 4643160108743308729032666609), (Int.ofNat 389993105722865985276353986), (Int.ofNat 64544052881260657773864237), (Int.negOfNat 1665249585911884182109532), (Int.negOfNat 483767755822755456389160), (Int.ofNat 1998026151033880700178), (Int.ofNat 2389279652253245424376), (Int.ofNat 16162263109216012550), (Int.negOfNat 8838026513464835678), (Int.negOfNat 147690359941876783), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(315795734364295015293933011394179/281474976710656000000000000000000), (80041783255051662123067376668517/1125899906842624000000000000000000), (-366894778887221914592201030377/175921860444160000000000000000000), (760117392549674435047430827729/5629499534213120000000000000000000), (284388385189147684311884771749/1125899906842624000000000000000000), (42853284172172805595336417949/2814749767106560000000000000000000), (-41764620920899434574360912071/5629499534213120000000000000000000), (-4643160108743308729032666609/5629499534213120000000000000000000), (194996552861432992638176993/2814749767106560000000000000000000), (64544052881260657773864237/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial150.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial150.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial150.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 7097807564593168958206371232878355), (Int.ofNat 405161780614853057894337916348584), (Int.ofNat 21623485603813726352268531074882), (Int.ofNat 7282170624213187357938247078963), (Int.negOfNat 871616322073922690179148283677), (Int.negOfNat 527410164514644573032931597616), (Int.negOfNat 31830538282542183401516973149), (Int.ofNat 7043796614525914044223566021), (Int.ofNat 723597521190935752249799294), (Int.negOfNat 46084115153577026985661983), (Int.negOfNat 6879878008069351086532058), (Int.ofNat 172615105264017766332840), (Int.ofNat 40330597958388573446332), (Int.negOfNat 338654014015317148524), (Int.negOfNat 166310107921440126870), (Int.negOfNat 147021766735608978), (Int.ofNat 559649035768758073), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(1419561512918633791641274246575671/1125899906842624000000000000000000), (50645222576856632236792239543573/703687441776640000000000000000000), (10811742801906863176134265537441/2814749767106560000000000000000000), (7282170624213187357938247078963/5629499534213120000000000000000000), (-871616322073922690179148283677/5629499534213120000000000000000000), (-32963135282165285814558224851/351843720888320000000000000000000), (-31830538282542183401516973149/5629499534213120000000000000000000), (7043796614525914044223566021/5629499534213120000000000000000000), (361798760595467876124899647/2814749767106560000000000000000000), (-46084115153577026985661983/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial150.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial150.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial150.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 8021079012476810567803067435051675), (Int.ofNat 506603852323654827507672758184716), (Int.ofNat 311552984327406148927749877054), (Int.negOfNat 20980649708870400576288391879518), (Int.negOfNat 5539023486547479265768647170732), (Int.negOfNat 132996088346729316053015996538), (Int.ofNat 98479400611663279607063894011), (Int.ofNat 7206774610951339853376730279), (Int.negOfNat 841295639139833597047826636), (Int.negOfNat 88527110076517820485734487), (Int.ofNat 4378955271060123436498682), (Int.ofNat 618663245679627942511350), (Int.negOfNat 15121028213839330684618), (Int.negOfNat 2941761930834496466166), (Int.ofNat 35111546795068389390), (Int.ofNat 10498348470140992578), (Int.negOfNat 24100534589974907), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(320843160499072422712122697402067/225179981368524800000000000000000), (126650963080913706876918189546179/1407374883553280000000000000000000), (155776492163703074463874938527/2814749767106560000000000000000000), (-10490324854435200288144195939759/2814749767106560000000000000000000), (-1384755871636869816442161792683/1407374883553280000000000000000000), (-66498044173364658026507998269/2814749767106560000000000000000000), (98479400611663279607063894011/5629499534213120000000000000000000), (7206774610951339853376730279/5629499534213120000000000000000000), (-210323909784958399261956659/1407374883553280000000000000000000), (-88527110076517820485734487/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial150.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial150.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial150.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 8781777597954845457673158747676767), (Int.ofNat 89293923026006877850243918575265), (Int.negOfNat 242519724929507016045437829083215), (Int.negOfNat 52712833396956342197897912143144), (Int.negOfNat 159459258613149598270136025013), (Int.ofNat 1149923873179477630167022887216), (Int.ofNat 68030650152940170407288700959), (Int.negOfNat 12206162213735283337486419511), (Int.negOfNat 1056074025698671260590884894), (Int.ofNat 80213474888678454639895473), (Int.ofNat 8730492326750296070411048), (Int.negOfNat 362094401184824962417030), (Int.negOfNat 47837034334906257856342), (Int.ofNat 1191901232497037066644), (Int.ofNat 190150975788040134580), (Int.negOfNat 2749153356811629132), (Int.negOfNat 589321180463291173), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(8781777597954845457673158747676767/5629499534213120000000000000000000), (17858784605201375570048783715053/1125899906842624000000000000000000), (-48503944985901403209087565816643/1125899906842624000000000000000000), (-6589104174619542774737239017893/703687441776640000000000000000000), (-159459258613149598270136025013/5629499534213120000000000000000000), (71870242073717351885438930451/351843720888320000000000000000000), (68030650152940170407288700959/5629499534213120000000000000000000), (-12206162213735283337486419511/5629499534213120000000000000000000), (-528037012849335630295442447/2814749767106560000000000000000000), (80213474888678454639895473/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial150.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial150.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial150.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 7605400395371347539545786075605663), (Int.negOfNat 1419711317581352332218173081750967), (Int.negOfNat 463940480308641391330189329878171), (Int.negOfNat 5289456523969837441456146767413), (Int.ofNat 11241110713199115400766138466162), (Int.ofNat 684983536816451578717385578585), (Int.negOfNat 145684223627712564592654913561), (Int.negOfNat 12089217570368665940984447409), (Int.ofNat 1183838557044566661328547956), (Int.ofNat 115058794607548537064443657), (Int.negOfNat 6644220831738508405673592), (Int.negOfNat 720313007771498381837960), (Int.ofNat 27390062480319567433158), (Int.ofNat 3239078853110084158976), (Int.negOfNat 86376612440230843050), (Int.negOfNat 11033179226401160278), (Int.ofNat 195891429121826597), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(7605400395371347539545786075605663/5629499534213120000000000000000000), (-1419711317581352332218173081750967/5629499534213120000000000000000000), (-463940480308641391330189329878171/5629499534213120000000000000000000), (-5289456523969837441456146767413/5629499534213120000000000000000000), (5620555356599557700383069233081/2814749767106560000000000000000000), (136996707363290315743477115717/1125899906842624000000000000000000), (-145684223627712564592654913561/5629499534213120000000000000000000), (-12089217570368665940984447409/5629499534213120000000000000000000), (295959639261141665332136989/1407374883553280000000000000000000), (115058794607548537064443657/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial150.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial150.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial150.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 3059160052064760985624743612661601), (Int.negOfNat 2956383784484921247724349386932834), (Int.negOfNat 211622915701614629516052722286732), (Int.ofNat 84570796660063859474921385581135), (Int.ofNat 7639542935278360302411153101590), (Int.negOfNat 1387556495570736533235474373646), (Int.negOfNat 135758633621826814169149842549), (Int.ofNat 14234497528037713624044392261), (Int.ofNat 1433786571410169726749872234), (Int.negOfNat 99626323008152739566671673), (Int.negOfNat 10118594038169744881942388), (Int.ofNat 505394302027580288626390), (Int.ofNat 51200523915219866886492), (Int.negOfNat 1941917267536196050494), (Int.negOfNat 195129145418639410830), (Int.ofNat 5728615515301186782), (Int.ofNat 618993325157824273), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(3059160052064760985624743612661601/5629499534213120000000000000000000), (-1478191892242460623862174693466417/2814749767106560000000000000000000), (-52905728925403657379013180571683/1407374883553280000000000000000000), (16914159332012771894984277116227/1125899906842624000000000000000000), (763954293527836030241115310159/562949953421312000000000000000000), (-693778247785368266617737186823/2814749767106560000000000000000000), (-135758633621826814169149842549/5629499534213120000000000000000000), (14234497528037713624044392261/5629499534213120000000000000000000), (716893285705084863374936117/2814749767106560000000000000000000), (-99626323008152739566671673/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial150.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial150.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial150.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 2952261559054668693661346330360508), (Int.negOfNat 2673059957604371546997340983424272), (Int.ofNat 347140902076851181355409958809988), (Int.ofNat 78339564860274851998703379287357), (Int.negOfNat 9300781321741998000185459122579), (Int.negOfNat 1441751762456020702014869580435), (Int.ofNat 133103533523039696248084405011), (Int.ofNat 16794930620535540121607556259), (Int.negOfNat 1219145584299834180610198516), (Int.negOfNat 132797914046733730617157257), (Int.ofNat 7762050588619294897439402), (Int.ofNat 753272972020931332758710), (Int.negOfNat 36290164544586235206148), (Int.negOfNat 3197146249888324221696), (Int.ofNat 129575416656993560780), (Int.ofNat 10331312922545947828), (Int.negOfNat 377573038551855987), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-738065389763667173415336582590127/1407374883553280000000000000000000), (-167066247350273221687333811464017/351843720888320000000000000000000), (86785225519212795338852489702497/1407374883553280000000000000000000), (78339564860274851998703379287357/5629499534213120000000000000000000), (-9300781321741998000185459122579/5629499534213120000000000000000000), (-288350352491204140402973916087/1125899906842624000000000000000000), (133103533523039696248084405011/5629499534213120000000000000000000), (16794930620535540121607556259/5629499534213120000000000000000000), (-304786396074958545152549629/1407374883553280000000000000000000), (-132797914046733730617157257/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial150.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial150.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial150.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial150.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial150.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial150.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial150.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial150.reflect := by
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

end Bin150
end
end ErdosOverlap.OuterNumerics
