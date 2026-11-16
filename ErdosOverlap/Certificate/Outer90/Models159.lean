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

/-! # Exact integer weighted outer models for source bin 159

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin159

def weightDenominator : ℤ := (Int.ofNat 5000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 176532630508618500)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 890382437423363000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 661103416427357000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 225613089218351800)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 432503617738170750)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 351189130184491750)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 255048204393856750)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 194535511422925600)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 113963573722772085)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 65223243422444770)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial159.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial159.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 4648197062097122000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1821655219759268650)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 597514366525393200)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 511883493837904000)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 272948865635372800)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 102515370566150100)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 12364524061798342)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 11081401572184649)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 5365021085483039)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial159.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial159.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4648197062097122000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1821655219759268650)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 597514366525393200)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 511883493837904000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 272948865635372800)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 102515370566150100)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 12364524061798342)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 11081401572184649)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 5365021085483039)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial159.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial159.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial159.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 1955687724202093170441753711597746), (Int.ofNat 2075913478513185213682556375616551), (Int.ofNat 195736269359042975968372884843309), (Int.negOfNat 52983193781894659020139441586402), (Int.negOfNat 6150764324108844968980695847216), (Int.ofNat 969330103955429895236153017173), (Int.ofNat 105476222642004645744354145643), (Int.negOfNat 11673817009445356149409364563), (Int.negOfNat 1111277073238252085125312994), (Int.ofNat 96227967073306748369169046), (Int.ofNat 7879176806089526456307513), (Int.negOfNat 568484339255575793185608), (Int.negOfNat 40121509089039488477511), (Int.ofNat 2502714778978550487311), (Int.ofNat 153987098171025869429), (Int.negOfNat 8387105349047044625), (Int.negOfNat 483351318920078818), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-977843862101046585220876855798873/2814749767106560000000000000000000), (2075913478513185213682556375616551/5629499534213120000000000000000000), (195736269359042975968372884843309/5629499534213120000000000000000000), (-26491596890947329510069720793201/2814749767106560000000000000000000), (-384422770256802810561293490451/351843720888320000000000000000000), (969330103955429895236153017173/5629499534213120000000000000000000), (105476222642004645744354145643/5629499534213120000000000000000000), (-11673817009445356149409364563/5629499534213120000000000000000000), (-555638536619126042562656497/2814749767106560000000000000000000), (48113983536653374184584523/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial159.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial159.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial159.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial159 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 2492852868005216743493355603758828), (Int.ofNat 2117920607300447907597189757938612), (Int.negOfNat 176240833393831682818919697434659), (Int.negOfNat 54458011046038869415763986660265), (Int.ofNat 5823648481905332298752997451654), (Int.ofNat 994201625159010127516313404964), (Int.negOfNat 101415041989130596181005196623), (Int.negOfNat 11725593282602143855850002271), (Int.ofNat 1095363629274572472426367067), (Int.ofNat 93386266297011754113862167), (Int.negOfNat 8015164573346689448864464), (Int.negOfNat 530913573253798203065559), (Int.ofNat 42099123306022905393163), (Int.ofNat 2253214942247355261197), (Int.negOfNat 165985275736277484026), (Int.negOfNat 7319463459712788353), (Int.ofNat 537984791765768670), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(623213217001304185873338900939707/1407374883553280000000000000000000), (529480151825111976899297439484653/1407374883553280000000000000000000), (-176240833393831682818919697434659/5629499534213120000000000000000000), (-10891602209207773883152797332053/1125899906842624000000000000000000), (2911824240952666149376498725827/2814749767106560000000000000000000), (248550406289752531879078351241/1407374883553280000000000000000000), (-101415041989130596181005196623/5629499534213120000000000000000000), (-11725593282602143855850002271/5629499534213120000000000000000000), (1095363629274572472426367067/5629499534213120000000000000000000), (93386266297011754113862167/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial159.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial159.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial159.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial159 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 5705387169742504630477857180357758), (Int.ofNat 1001920199282358706360026256917543), (Int.negOfNat 313615346431959031314355132033835), (Int.ofNat 11431167457315557911615472757688), (Int.ofNat 7876760406501339782534764195659), (Int.negOfNat 604248885347741489437110063312), (Int.negOfNat 112074339148355478280917966842), (Int.ofNat 9982769105212820405042887827), (Int.ofNat 1022910903085391618552941098), (Int.negOfNat 96004281200990884240167421), (Int.negOfNat 6498367803553147338989898), (Int.ofNat 618803380055766346038809), (Int.ofNat 30353352305043089288824), (Int.negOfNat 2873300627859016049930), (Int.negOfNat 108372457939835261625), (Int.ofNat 10082306417179256411), (Int.ofNat 293046609738227547), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(2852693584871252315238928590178879/2814749767106560000000000000000000), (1001920199282358706360026256917543/5629499534213120000000000000000000), (-62723069286391806262871026406767/1125899906842624000000000000000000), (1428895932164444738951934094711/703687441776640000000000000000000), (7876760406501339782534764195659/5629499534213120000000000000000000), (-37765555334233843089819378957/351843720888320000000000000000000), (-56037169574177739140458983421/2814749767106560000000000000000000), (9982769105212820405042887827/5629499534213120000000000000000000), (511455451542695809276470549/2814749767106560000000000000000000), (-96004281200990884240167421/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial159.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial159.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial159.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial159 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 6647220184484960251894603450043090), (Int.ofNat 72103801228293653764172126353366), (Int.negOfNat 123180629360894837819423918233209), (Int.ofNat 39179528751032357293907449037556), (Int.negOfNat 1394929261039798364070796966219), (Int.negOfNat 877922880011554452512042544182), (Int.ofNat 66157408953687991687185009599), (Int.ofNat 9977403181669502730791617258), (Int.negOfNat 947909756370072249700371902), (Int.negOfNat 72744841715174801753835192), (Int.ofNat 7867920689262854211046121), (Int.ofNat 374211518487953922062861), (Int.negOfNat 44134184968892492061570), (Int.negOfNat 1438328255933319903990), (Int.ofNat 180415315037632521928), (Int.ofNat 4151141128934593780), (Int.negOfNat 554079855022217787), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(664722018448496025189460345004309/562949953421312000000000000000000), (36051900614146826882086063176683/2814749767106560000000000000000000), (-123180629360894837819423918233209/5629499534213120000000000000000000), (9794882187758089323476862259389/1407374883553280000000000000000000), (-1394929261039798364070796966219/5629499534213120000000000000000000), (-438961440005777226256021272091/2814749767106560000000000000000000), (66157408953687991687185009599/5629499534213120000000000000000000), (4988701590834751365395808629/2814749767106560000000000000000000), (-473954878185036124850185951/2814749767106560000000000000000000), (-9093105214396850219229399/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial159.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial159.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial159.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial159 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 6566969004334137942444771584056508), (Int.negOfNat 49258743412178797440035750400240), (Int.ofNat 28831174631535588738036128424077), (Int.ofNat 7117385528537710436322568516255), (Int.negOfNat 4650381680784617587783299418185), (Int.ofNat 252507360798335019283515721123), (Int.ofNat 79978363023197746911953951994), (Int.negOfNat 7328903300936550654329286864), (Int.negOfNat 719601565066892879082449224), (Int.ofNat 84894763060139725868676748), (Int.ofNat 4163131232341684413436503), (Int.negOfNat 595547911423931881003079), (Int.negOfNat 16967119846754070446435), (Int.ofNat 2889951094229060805191), (Int.ofNat 51474443931968877762), (Int.negOfNat 10492868219313672689), (Int.negOfNat 97376879470893237), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(1641742251083534485611192896014127/1407374883553280000000000000000000), (-615734292652234968000446880003/70368744177664000000000000000000), (28831174631535588738036128424077/5629499534213120000000000000000000), (1423477105707542087264513703251/1125899906842624000000000000000000), (-930076336156923517556659883637/1125899906842624000000000000000000), (252507360798335019283515721123/5629499534213120000000000000000000), (39989181511598873455976975997/2814749767106560000000000000000000), (-458056456308534415895580429/351843720888320000000000000000000), (-89950195633361609885306153/703687441776640000000000000000000), (21223690765034931467169187/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial159.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial159.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial159.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial159 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 6578432190686634170333004029584360), (Int.ofNat 34408526289282614680362217040730), (Int.negOfNat 6471116765759408996662911477173), (Int.negOfNat 12088409282138839208305794117998), (Int.ofNat 187370531190845891264093100128), (Int.ofNat 460601087254023130691376372595), (Int.negOfNat 41344736696647043242912737945), (Int.negOfNat 5872831749403936868011316262), (Int.ofNat 757680820873597174098824605), (Int.ofNat 40307253963720817199574502), (Int.negOfNat 6970731854221693474318323), (Int.negOfNat 172469963929822562654125), (Int.ofNat 41148613180685766536664), (Int.ofNat 479991744453569381134), (Int.negOfNat 173040898165939008897), (Int.negOfNat 745071889601848887), (Int.ofNat 570174918278666904), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(164460804767165854258325100739609/140737488355328000000000000000000), (3440852628928261468036221704073/562949953421312000000000000000000), (-6471116765759408996662911477173/5629499534213120000000000000000000), (-6044204641069419604152897058999/2814749767106560000000000000000000), (5855329099713934102002909379/175921860444160000000000000000000), (92120217450804626138275274519/1125899906842624000000000000000000), (-8268947339329408648582547589/1125899906842624000000000000000000), (-2936415874701968434005658131/2814749767106560000000000000000000), (151536164174719434819764921/1125899906842624000000000000000000), (20153626981860408599787251/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial159.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial159.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial159.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial159 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 6539204161634446541791203197038897), (Int.negOfNat 103430008936433302487272928593405), (Int.negOfNat 50064738600743847036646776798805), (Int.negOfNat 604597288290702404828451503028), (Int.ofNat 1583668529463766954222277289079), (Int.negOfNat 165310024333294922790974539551), (Int.negOfNat 35180902090558004126565834249), (Int.ofNat 5473193822281532968587790706), (Int.ofNat 314340575201057509035032565), (Int.negOfNat 69701116212704797196082086), (Int.negOfNat 1383114241674425227563528), (Int.ofNat 515382336064064664456370), (Int.ofNat 2270976336558590454561), (Int.negOfNat 2574877686220781263133), (Int.ofNat 8589847255126548979), (Int.ofNat 9588235110828227489), (Int.negOfNat 98292850796441073), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(6539204161634446541791203197038897/5629499534213120000000000000000000), (-20686001787286660497454585718681/1125899906842624000000000000000000), (-10012947720148769407329355359761/1125899906842624000000000000000000), (-151149322072675601207112875757/1407374883553280000000000000000000), (1583668529463766954222277289079/5629499534213120000000000000000000), (-165310024333294922790974539551/5629499534213120000000000000000000), (-35180902090558004126565834249/5629499534213120000000000000000000), (2736596911140766484293895353/2814749767106560000000000000000000), (62868115040211501807006513/1125899906842624000000000000000000), (-34850558106352398598041043/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial159.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial159.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial159.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial159 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 6145790589879226538919695277137537), (Int.negOfNat 277634343140310810828119307840933), (Int.negOfNat 33434061376619594158385657877365), (Int.ofNat 3077029416322534446099420555786), (Int.negOfNat 574205135298194993023309115108), (Int.negOfNat 123921781857198297290112435793), (Int.ofNat 32381119137515848755502890043), (Int.ofNat 1652204067094348994940208905), (Int.negOfNat 588153888199416847519318769), (Int.negOfNat 6138372935526995454542553), (Int.ofNat 5606831901465319008459849), (Int.negOfNat 32019039982374542510737), (Int.negOfNat 33975618671440774135326), (Int.ofNat 455067189167538234773), (Int.ofNat 144590629020447307216), (Int.negOfNat 2571493822328813766), (Int.negOfNat 521046738112671251), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(6145790589879226538919695277137537/5629499534213120000000000000000000), (-277634343140310810828119307840933/5629499534213120000000000000000000), (-6686812275323918831677131575473/1125899906842624000000000000000000), (1538514708161267223049710277893/2814749767106560000000000000000000), (-143551283824548748255827278777/1407374883553280000000000000000000), (-123921781857198297290112435793/5629499534213120000000000000000000), (32381119137515848755502890043/5629499534213120000000000000000000), (330440813418869798988041781/1125899906842624000000000000000000), (-588153888199416847519318769/5629499534213120000000000000000000), (-6138372935526995454542553/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial159.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial159.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial159.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial159 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 5470384820390694553163866453723004), (Int.negOfNat 396366041280284404106496373778359), (Int.negOfNat 30805541781154589969768221857806), (Int.negOfNat 1373065137440903256229274961416), (Int.negOfNat 21418029545296645041224895938), (Int.ofNat 168678314666648077559898119012), (Int.ofNat 2071647866355360081753842637), (Int.negOfNat 4182698488964141734934467771), (Int.ofNat 42402429618770608330494107), (Int.ofNat 52249512056221278089896131), (Int.negOfNat 1149106978736268133007763), (Int.negOfNat 391742346508079167790223), (Int.ofNat 10919705067332050996322), (Int.ofNat 1980713683131517733371), (Int.negOfNat 61226774339127446104), (Int.negOfNat 7383710663485185966), (Int.ofNat 239469379812296691), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(1367596205097673638290966613430751/1407374883553280000000000000000000), (-396366041280284404106496373778359/5629499534213120000000000000000000), (-15402770890577294984884110928903/2814749767106560000000000000000000), (-171633142180112907028659370177/703687441776640000000000000000000), (-10709014772648322520612447969/2814749767106560000000000000000000), (42169578666662019389974529753/1407374883553280000000000000000000), (2071647866355360081753842637/5629499534213120000000000000000000), (-4182698488964141734934467771/5629499534213120000000000000000000), (42402429618770608330494107/5629499534213120000000000000000000), (52249512056221278089896131/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial159.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial159.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial159.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial159 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 4548133954792172657916772502449719), (Int.negOfNat 524578322208852423560948796529674), (Int.negOfNat 28083770331696165778782124691268), (Int.ofNat 3516309134416020505709847640795), (Int.ofNat 846706103748862728633777189569), (Int.negOfNat 52649434421842472286200044747), (Int.negOfNat 25260238824675954569530213155), (Int.ofNat 1305357213545118610447273520), (Int.ofNat 410286212632552891441462981), (Int.negOfNat 20827155512847365057054132), (Int.negOfNat 3867683156314892848807060), (Int.ofNat 197130148790595907703330), (Int.ofNat 23544100737296866564389), (Int.negOfNat 1202209035572084941671), (Int.negOfNat 100617974575779623581), (Int.ofNat 5191220950557867803), (Int.ofNat 401330293438747789), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(4548133954792172657916772502449719/5629499534213120000000000000000000), (-262289161104426211780474398264837/2814749767106560000000000000000000), (-7020942582924041444695531172817/1407374883553280000000000000000000), (703261826883204101141969528159/1125899906842624000000000000000000), (846706103748862728633777189569/5629499534213120000000000000000000), (-52649434421842472286200044747/5629499534213120000000000000000000), (-5052047764935190913906042631/1125899906842624000000000000000000), (16316965169313982630590919/70368744177664000000000000000000), (410286212632552891441462981/5629499534213120000000000000000000), (-5206788878211841264263533/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial159.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial159.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial159.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial159 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 3425276546427019666305748956450864), (Int.negOfNat 575745149463651796466666190152490), (Int.ofNat 4539442355933103503792477234026), (Int.ofNat 5447763344394405437982408870667), (Int.negOfNat 495555453792410417951353492403), (Int.negOfNat 127756255479198330594216493856), (Int.ofNat 15956010280638271178096712601), (Int.ofNat 2629058849964950447126598428), (Int.negOfNat 277935159812194567193279791), (Int.negOfNat 31588452005968283642456840), (Int.ofNat 2930128374396144040357089), (Int.ofNat 235281661963062354881665), (Int.negOfNat 20239894143016543806864), (Int.negOfNat 1185705872695299010898), (Int.ofNat 97742847640737730023), (Int.ofNat 4310666957705078579), (Int.negOfNat 320787686491190578), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(214079784151688729144109309778179/351843720888320000000000000000000), (-57574514946365179646666619015249/562949953421312000000000000000000), (2269721177966551751896238617013/2814749767106560000000000000000000), (5447763344394405437982408870667/5629499534213120000000000000000000), (-495555453792410417951353492403/5629499534213120000000000000000000), (-3992382983724947831069265433/175921860444160000000000000000000), (15956010280638271178096712601/5629499534213120000000000000000000), (657264712491237611781649607/1407374883553280000000000000000000), (-277935159812194567193279791/5629499534213120000000000000000000), (-789711300149207091061421/140737488355328000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial159.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial159.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial159.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial159 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 2324782807153694616410788959955882), (Int.negOfNat 514391403948303052628646739289759), (Int.ofNat 20103604378915845463645194846093), (Int.negOfNat 217178149229210189065147222072), (Int.negOfNat 471843261400278497542516560430), (Int.ofNat 124612360774640811832124564421), (Int.ofNat 12355955379837006066238960430), (Int.negOfNat 2906830228977880739961200302), (Int.negOfNat 196595647472240527983668500), (Int.ofNat 36669591893552101282495030), (Int.ofNat 1832863850606217096316895), (Int.negOfNat 295447106589685128506381), (Int.negOfNat 11026612861646439076123), (Int.ofNat 1638886293057110380293), (Int.ofNat 46321014291871520542), (Int.negOfNat 6632356167591616903), (Int.negOfNat 205660563171413479), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(1162391403576847308205394479977941/2814749767106560000000000000000000), (-514391403948303052628646739289759/5629499534213120000000000000000000), (20103604378915845463645194846093/5629499534213120000000000000000000), (-27147268653651273633143402759/703687441776640000000000000000000), (-47184326140027849754251656043/562949953421312000000000000000000), (124612360774640811832124564421/5629499534213120000000000000000000), (1235595537983700606623896043/562949953421312000000000000000000), (-1453415114488940369980600151/2814749767106560000000000000000000), (-393191294944481055967337/11258999068426240000000000000000), (3666959189355210128249503/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial159.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial159.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial159.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial159 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 1371503488740652933174116933527396), (Int.negOfNat 440753987146024752691252638082370), (Int.ofNat 18286322389325031711041260298524), (Int.ofNat 1201467421943216430197907147295), (Int.ofNat 640775064128670108681162053874), (Int.ofNat 20054248397994170437204315331), (Int.negOfNat 24199855750970064744423375208), (Int.negOfNat 662740514160536883500802924), (Int.ofNat 386808526773036408799286714), (Int.ofNat 8444641082707817143957830), (Int.negOfNat 3742460379117915141996771), (Int.negOfNat 61749893600361421651061), (Int.ofNat 24297758045097668488578), (Int.ofNat 293831565102880035654), (Int.negOfNat 112544968186680106872), (Int.negOfNat 933518881103567392), (Int.ofNat 336882749747639695), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(342875872185163233293529233381849/1407374883553280000000000000000000), (-44075398714602475269125263808237/562949953421312000000000000000000), (4571580597331257927760315074631/1407374883553280000000000000000000), (240293484388643286039581429459/1125899906842624000000000000000000), (320387532064335054340581026937/2814749767106560000000000000000000), (20054248397994170437204315331/5629499534213120000000000000000000), (-3024981968871258093052921901/703687441776640000000000000000000), (-165685128540134220875200731/1407374883553280000000000000000000), (193404263386518204399643357/2814749767106560000000000000000000), (844464108270781714395783/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial159.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial159.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial159.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial159 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 582112546770543549553988920918059), (Int.negOfNat 335628935422523950268421687214127), (Int.ofNat 36913610014642748547568290126229), (Int.ofNat 3567931823386654483462675094863), (Int.negOfNat 378802653976879911871223814363), (Int.negOfNat 165259719409438719739734416382), (Int.ofNat 3446980461508202588201413732), (Int.ofNat 3422641626305451523626843199), (Int.negOfNat 32992929238448862458242766), (Int.negOfNat 40833850924937238637643037), (Int.ofNat 282360701388439084806830), (Int.ofNat 316017163729340080895311), (Int.negOfNat 1982963617210633187568), (Int.negOfNat 1704587283955699828994), (Int.ofNat 10683709780325914175), (Int.ofNat 6779756558347436681), (Int.ofNat 9990832904079169), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(582112546770543549553988920918059/5629499534213120000000000000000000), (-335628935422523950268421687214127/5629499534213120000000000000000000), (36913610014642748547568290126229/5629499534213120000000000000000000), (3567931823386654483462675094863/5629499534213120000000000000000000), (-378802653976879911871223814363/5629499534213120000000000000000000), (-82629859704719359869867208191/2814749767106560000000000000000000), (861745115377050647050353433/1407374883553280000000000000000000), (3422641626305451523626843199/5629499534213120000000000000000000), (-16496464619224431229121383/2814749767106560000000000000000000), (-40833850924937238637643037/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial159.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial159.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial159.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial159 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 76333683484244843195980734651729), (Int.negOfNat 168429609592606899817687561369653), (Int.ofNat 38900919566875091720655031120831), (Int.negOfNat 3866345013926863669909892704164), (Int.negOfNat 1051538314053129563097889553499), (Int.ofNat 77393124900775507089785302245), (Int.ofNat 25382072257141869344272515563), (Int.negOfNat 1267997135783304276465478383), (Int.negOfNat 378721153751058900584966429), (Int.ofNat 14007856374325821514638635), (Int.ofNat 3561013835665763463244608), (Int.negOfNat 105746863722661708800681), (Int.negOfNat 22703370512161735930965), (Int.ofNat 571302419465572213379), (Int.ofNat 103823551967856317614), (Int.negOfNat 2420483130362715035), (Int.negOfNat 352977813004088812), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(76333683484244843195980734651729/5629499534213120000000000000000000), (-168429609592606899817687561369653/5629499534213120000000000000000000), (38900919566875091720655031120831/5629499534213120000000000000000000), (-966586253481715917477473176041/1407374883553280000000000000000000), (-1051538314053129563097889553499/5629499534213120000000000000000000), (15478624980155101417957060449/1125899906842624000000000000000000), (25382072257141869344272515563/5629499534213120000000000000000000), (-1267997135783304276465478383/5629499534213120000000000000000000), (-378721153751058900584966429/5629499534213120000000000000000000), (2801571274865164302927727/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial159.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial159.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial159.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial159 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 148824938971640864724387978861501), (Int.negOfNat 82713563841251698258169444624885), (Int.ofNat 1319501168928025074361433177533), (Int.negOfNat 6387323259830950556619900219400), (Int.ofNat 563413252161761718030879895553), (Int.ofNat 157611565086817601354051982009), (Int.negOfNat 16117421714622108927267096911), (Int.negOfNat 2922803032330503504258097823), (Int.ofNat 235585776247064997014877570), (Int.ofNat 34011944446845037378899152), (Int.negOfNat 2162891954537956666952835), (Int.negOfNat 260653323469100743342132), (Int.ofNat 13599926099230512245641), (Int.ofNat 1400954515633008991093), (Int.negOfNat 61883832238952711971), (Int.negOfNat 5602866478203261167), (Int.ofNat 191043918448738180), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-148824938971640864724387978861501/5629499534213120000000000000000000), (-16542712768250339651633888924977/1125899906842624000000000000000000), (1319501168928025074361433177533/5629499534213120000000000000000000), (-31936616299154752783099501097/28147497671065600000000000000000), (563413252161761718030879895553/5629499534213120000000000000000000), (157611565086817601354051982009/5629499534213120000000000000000000), (-16117421714622108927267096911/5629499534213120000000000000000000), (-2922803032330503504258097823/5629499534213120000000000000000000), (23558577624706499701487757/562949953421312000000000000000000), (2125746527927814836181197/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial159.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial159.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial159.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial159 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 347345058264570833871486014488042), (Int.negOfNat 127543255914130298621496749924268), (Int.negOfNat 16158144238953902574303974822922), (Int.ofNat 771560815965658602263240499289), (Int.ofNat 717170727760035054847734020072), (Int.negOfNat 130589082137800051716981112464), (Int.negOfNat 17863656413752101209582021899), (Int.ofNat 2755360895290466862102439947), (Int.ofNat 264224067956183338603803970), (Int.negOfNat 31974586002170896478306518), (Int.negOfNat 2483767011845118045570065), (Int.ofNat 241452426298838806311808), (Int.ofNat 15936799055913568893359), (Int.negOfNat 1279082964336134265907), (Int.negOfNat 73708661591167900649), (Int.ofNat 5094875840228246673), (Int.ofNat 233261368330165350), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-173672529132285416935743007244021/2814749767106560000000000000000000), (-31885813978532574655374187481067/1407374883553280000000000000000000), (-8079072119476951287151987411461/2814749767106560000000000000000000), (771560815965658602263240499289/5629499534213120000000000000000000), (89646340970004381855966752509/703687441776640000000000000000000), (-8161817633612503232311319529/351843720888320000000000000000000), (-17863656413752101209582021899/5629499534213120000000000000000000), (2755360895290466862102439947/5629499534213120000000000000000000), (26422406795618333860380397/562949953421312000000000000000000), (-15987293001085448239153259/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial159.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial159.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial159.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial159 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 654337092061553540260755994945390), (Int.negOfNat 172422971438034905890206999364628), (Int.negOfNat 6894296531096202500322861758347), (Int.ofNat 245198743948437789147986107078), (Int.negOfNat 743720611692100316116566731871), (Int.negOfNat 71344974717325878324591063427), (Int.ofNat 24661071829013549663743777247), (Int.ofNat 1509518149212121986168965567), (Int.negOfNat 375547349934698040838548271), (Int.negOfNat 17964342077089797636156035), (Int.ofNat 3497590011673697685502172), (Int.ofNat 141416164857541048741459), (Int.negOfNat 22006291930007832574755), (Int.negOfNat 783395888629876564921), (Int.ofNat 99537890256279445106), (Int.ofNat 3318024250274172865), (Int.negOfNat 332220447464593798), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-65433709206155354026075599494539/562949953421312000000000000000000), (-43105742859508726472551749841157/1407374883553280000000000000000000), (-6894296531096202500322861758347/5629499534213120000000000000000000), (122599371974218894573993053539/2814749767106560000000000000000000), (-743720611692100316116566731871/5629499534213120000000000000000000), (-71344974717325878324591063427/5629499534213120000000000000000000), (24661071829013549663743777247/5629499534213120000000000000000000), (1509518149212121986168965567/5629499534213120000000000000000000), (-375547349934698040838548271/5629499534213120000000000000000000), (-3592868415417959527231207/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial159.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial159.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial159.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial159 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 1037311234719454512190445334375466), (Int.negOfNat 221560260526570357836953981444365), (Int.negOfNat 22760002525982727722839902550648), (Int.negOfNat 4479753852202930032278989018205), (Int.ofNat 2127751455874016301257213227), (Int.ofNat 176931725620276028823197293822), (Int.ofNat 4111930850556532805668389798), (Int.negOfNat 3578623282954255925364948511), (Int.negOfNat 68655907713896655001726974), (Int.ofNat 42272089143523078772569493), (Int.ofNat 720177863383697054033550), (Int.negOfNat 322849440013996525895109), (Int.negOfNat 5197904294301126404372), (Int.ofNat 1716925158250672049126), (Int.ofNat 26353740504395778145), (Int.negOfNat 6790076908360458459), (Int.negOfNat 42956659148314079), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-518655617359727256095222667187733/2814749767106560000000000000000000), (-44312052105314071567390796288873/1125899906842624000000000000000000), (-2845000315747840965354987818831/703687441776640000000000000000000), (-895950770440586006455797803641/1125899906842624000000000000000000), (2127751455874016301257213227/5629499534213120000000000000000000), (88465862810138014411598646911/2814749767106560000000000000000000), (2055965425278266402834194899/2814749767106560000000000000000000), (-3578623282954255925364948511/5629499534213120000000000000000000), (-34327953856948327500863487/2814749767106560000000000000000000), (42272089143523078772569493/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial159.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial159.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial159.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial159 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 1601804701005611374106615905086916), (Int.negOfNat 352921316231249474370584791686069), (Int.negOfNat 36780002551253060161072248667590), (Int.ofNat 1369989697508069482731279562506), (Int.ofNat 1105712902283893091939652319998), (Int.negOfNat 23560212272715657590756908982), (Int.negOfNat 27551884014442474481449731053), (Int.ofNat 454091352805443870759413046), (Int.ofNat 424775526596716232952922306), (Int.negOfNat 4319405864139494967177140), (Int.negOfNat 4045024280999731466072429), (Int.ofNat 21216506935857865895439), (Int.ofNat 25794098818605562765562), (Int.negOfNat 46376227416479722086), (Int.negOfNat 117233538751493064208), (Int.negOfNat 149701919495978292), (Int.ofNat 348315510721042915), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-400451175251402843526653976271729/1407374883553280000000000000000000), (-352921316231249474370584791686069/5629499534213120000000000000000000), (-3678000255125306016107224866759/562949953421312000000000000000000), (684994848754034741365639781253/2814749767106560000000000000000000), (552856451141946545969826159999/2814749767106560000000000000000000), (-11780106136357828795378454491/2814749767106560000000000000000000), (-27551884014442474481449731053/5629499534213120000000000000000000), (227045676402721935379706523/2814749767106560000000000000000000), (212387763298358116476461153/2814749767106560000000000000000000), (-215970293206974748358857/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial159.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial159.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial159.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial159 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 2428472607613040376516836942702829), (Int.negOfNat 454784818111813491785698308885678), (Int.negOfNat 9518088925839428713344866136957), (Int.ofNat 5798821441876333647652711680999), (Int.negOfNat 247858770379308319819868581483), (Int.negOfNat 163956746670314968482659832194), (Int.ofNat 11627980525286353247206909250), (Int.ofNat 3456549726647148701551017148), (Int.negOfNat 172029560626676586089046300), (Int.negOfNat 42662966602507856573938420), (Int.ofNat 1433927174117547923196245), (Int.ofNat 334843156017210329183779), (Int.negOfNat 7781185956713537178717), (Int.negOfNat 1810633285568105893187), (Int.ofNat 29529041573981252718), (Int.ofNat 7200638710494874737), (Int.negOfNat 152713071119020231), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-2428472607613040376516836942702829/5629499534213120000000000000000000), (-227392409055906745892849154442839/2814749767106560000000000000000000), (-9518088925839428713344866136957/5629499534213120000000000000000000), (5798821441876333647652711680999/5629499534213120000000000000000000), (-247858770379308319819868581483/5629499534213120000000000000000000), (-81978373335157484241329916097/2814749767106560000000000000000000), (46511922101145412988827637/22517998136852480000000000000000), (864137431661787175387754287/1407374883553280000000000000000000), (-1720295606266765860890463/56294995342131200000000000000000), (-2133148330125392828696921/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial159.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial159.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial159.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial159 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 3337813530002875019417203032378069), (Int.negOfNat 440801853268011263765429537768326), (Int.ofNat 10843488191527483266179748841650), (Int.ofNat 550990063097753242509890888308), (Int.negOfNat 554787393611555566227240578334), (Int.ofNat 122981005326202450270428439650), (Int.ofNat 21033250325420083983120558369), (Int.negOfNat 2666987123369951813010702642), (Int.negOfNat 364994559828101363525842409), (Int.ofNat 29216377138850593000002430), (Int.ofNat 3673621056892855726489031), (Int.negOfNat 201367772844294211613575), (Int.negOfNat 24215409174557004141356), (Int.ofNat 958319920576791904742), (Int.ofNat 112924661220611906177), (Int.negOfNat 3256367319836766601), (Int.negOfNat 364410573977492032), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-3337813530002875019417203032378069/5629499534213120000000000000000000), (-220400926634005631882714768884163/2814749767106560000000000000000000), (216869763830549665323594976833/112589990684262400000000000000000), (137747515774438310627472722077/1407374883553280000000000000000000), (-277393696805777783113620289167/2814749767106560000000000000000000), (2459620106524049005408568793/112589990684262400000000000000000), (21033250325420083983120558369/5629499534213120000000000000000000), (-1333493561684975906505351321/2814749767106560000000000000000000), (-364994559828101363525842409/5629499534213120000000000000000000), (2921637713885059300000243/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial159.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial159.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial159.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial159 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 4175647035786619742739104620124939), (Int.negOfNat 396177593435615396814538413887489), (Int.ofNat 13444539585192368771376377934651), (Int.ofNat 2452285518273396114860083977551), (Int.ofNat 937521156433656173640649344547), (Int.ofNat 68368629177987617736355846977), (Int.negOfNat 29330598713715744297343526595), (Int.negOfNat 2302829229820115184376339590), (Int.ofNat 421790322009674533342743159), (Int.ofNat 32384884144363268010265958), (Int.negOfNat 3641190453394182290626820), (Int.negOfNat 272264299890428171711270), (Int.ofNat 21004952114333004703991), (Int.ofNat 1535942979391332193929), (Int.negOfNat 86737785049482698659), (Int.negOfNat 6296005602009429537), (Int.ofNat 348382801386354541), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-4175647035786619742739104620124939/5629499534213120000000000000000000), (-396177593435615396814538413887489/5629499534213120000000000000000000), (13444539585192368771376377934651/5629499534213120000000000000000000), (2452285518273396114860083977551/5629499534213120000000000000000000), (937521156433656173640649344547/5629499534213120000000000000000000), (68368629177987617736355846977/5629499534213120000000000000000000), (-5866119742743148859468705319/1125899906842624000000000000000000), (-230282922982011518437633959/562949953421312000000000000000000), (421790322009674533342743159/5629499534213120000000000000000000), (16192442072181634005132979/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial159.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial159.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial159.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial159 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 4879469195769374603704090846343070), (Int.negOfNat 283679578894699788046606862524852), (Int.ofNat 48398498103782355946216036968095), (Int.ofNat 7569981100942334417730717027885), (Int.negOfNat 237757550737275012053818622078), (Int.negOfNat 257668789800457050182819978922), (Int.negOfNat 7327051626035840029097122537), (Int.ofNat 4830738425875411215625582299), (Int.ofNat 198827417587569742420824673), (Int.negOfNat 52853730982943173406172979), (Int.negOfNat 2382383061673388336167457), (Int.ofNat 371872596933946209052537), (Int.ofNat 17304845745582477460318), (Int.negOfNat 1816780863613635772249), (Int.negOfNat 85194480113126292196), (Int.ofNat 6572933031767429254), (Int.ofNat 315282393811496379), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-487946919576937460370409084634307/562949953421312000000000000000000), (-70919894723674947011651715631213/1407374883553280000000000000000000), (9679699620756471189243207393619/1125899906842624000000000000000000), (1513996220188466883546143405577/1125899906842624000000000000000000), (-118878775368637506026909311039/2814749767106560000000000000000000), (-128834394900228525091409989461/2814749767106560000000000000000000), (-7327051626035840029097122537/5629499534213120000000000000000000), (4830738425875411215625582299/5629499534213120000000000000000000), (198827417587569742420824673/5629499534213120000000000000000000), (-52853730982943173406172979/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial159.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial159.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial159.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial159 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 5204552415634931307356099539247813), (Int.negOfNat 26636045434885583004541897795247), (Int.ofNat 69083093357421926682363169344181), (Int.negOfNat 3053307242244906423266882821486), (Int.negOfNat 1906732257239001781209641979963), (Int.ofNat 35584680316271734424689696281), (Int.ofNat 45124599152901451169717033307), (Int.ofNat 291138382754313282917222955), (Int.negOfNat 638533441778281323300183131), (Int.negOfNat 12071654319126545979797003), (Int.ofNat 5576527231042024888951611), (Int.ofNat 140575087605638094939023), (Int.negOfNat 32559067517789213395074), (Int.negOfNat 925721258450383554967), (Int.ofNat 136004107125015827484), (Int.ofNat 4091481154666388014), (Int.negOfNat 489559330402210159), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-5204552415634931307356099539247813/5629499534213120000000000000000000), (-26636045434885583004541897795247/5629499534213120000000000000000000), (69083093357421926682363169344181/5629499534213120000000000000000000), (-1526653621122453211633441410743/2814749767106560000000000000000000), (-1906732257239001781209641979963/5629499534213120000000000000000000), (35584680316271734424689696281/5629499534213120000000000000000000), (45124599152901451169717033307/5629499534213120000000000000000000), (58227676550862656583444591/1125899906842624000000000000000000), (-638533441778281323300183131/5629499534213120000000000000000000), (-12071654319126545979797003/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial159.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial159.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial159.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial159 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 5032526142894080682585911912742953), (Int.ofNat 163029967166612538024940250750311), (Int.ofNat 17740026074102513489310612084163), (Int.negOfNat 10622192018407760383343858035229), (Int.ofNat 550848135465421924820770182132), (Int.ofNat 336804036205316837576020907093), (Int.negOfNat 11629335859747494335400643221), (Int.negOfNat 6431016474082859154384198424), (Int.ofNat 65522772534358846181688415), (Int.ofNat 71839904895382851848669664), (Int.ofNat 288750447851849669941168), (Int.negOfNat 509692862569105326895230), (Int.negOfNat 5917100958492622755181), (Int.ofNat 2501115209752361538347), (Int.ofNat 39491466589049241861), (Int.negOfNat 9192660159996483291), (Int.negOfNat 195565949137572917), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-5032526142894080682585911912742953/5629499534213120000000000000000000), (163029967166612538024940250750311/5629499534213120000000000000000000), (17740026074102513489310612084163/5629499534213120000000000000000000), (-10622192018407760383343858035229/5629499534213120000000000000000000), (137712033866355481205192545533/1407374883553280000000000000000000), (336804036205316837576020907093/5629499534213120000000000000000000), (-11629335859747494335400643221/5629499534213120000000000000000000), (-803877059260357394298024803/703687441776640000000000000000000), (13104554506871769236337683/1125899906842624000000000000000000), (2244997027980714120270927/175921860444160000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial159.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial159.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial159.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial159 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 4702406984405899475938762906936188), (Int.ofNat 146209644279712967581161043212642), (Int.negOfNat 12503696714478904563289737773872), (Int.ofNat 2281303448932719357098438874342), (Int.ofNat 1766019218898665934071283192300), (Int.negOfNat 181276154524421274868066467579), (Int.negOfNat 52407871897650681370850965245), (Int.ofNat 2674974505183568058766266688), (Int.ofNat 793860080446582380386767715), (Int.negOfNat 16772264060526089722643888), (Int.negOfNat 7021460623778188775336037), (Int.ofNat 43697784757177340547635), (Int.ofNat 40963057262840883550316), (Int.ofNat 67234651426396910894), (Int.negOfNat 170779899571044596703), (Int.negOfNat 1018437448886280627), (Int.ofNat 570877637081104046), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-1175601746101474868984690726734047/1407374883553280000000000000000000), (73104822139856483790580521606321/2814749767106560000000000000000000), (-781481044654931535205608610867/351843720888320000000000000000000), (1140651724466359678549219437171/2814749767106560000000000000000000), (17660192188986659340712831923/56294995342131200000000000000000), (-181276154524421274868066467579/5629499534213120000000000000000000), (-10481574379530136274170193049/1125899906842624000000000000000000), (41796476643493250918222917/87960930222080000000000000000000), (158772016089316476077353543/1125899906842624000000000000000000), (-1048266503782880607665243/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial159.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial159.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial159.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial159 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 4422120585783128430665317044606429), (Int.ofNat 157456901104241248064072161588880), (Int.ofNat 19554556107876187653359072340329), (Int.ofNat 3502069850508634616459620978151), (Int.negOfNat 1708205554140016759476707183968), (Int.negOfNat 314964114566822732982649440725), (Int.ofNat 42044546128494082403770512585), (Int.ofNat 7423543723201324798575828606), (Int.negOfNat 418967703019560491688381096), (Int.negOfNat 85224190876238311258201362), (Int.ofNat 2343107927935301817446597), (Int.ofNat 600951172161190596106081), (Int.negOfNat 8239773003890336388485), (Int.negOfNat 2923224557009464980169), (Int.ofNat 18071102888717442378), (Int.ofNat 10633795377030232391), (Int.negOfNat 103781129761393), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-4422120585783128430665317044606429/5629499534213120000000000000000000), (1968211263803015600800902019861/70368744177664000000000000000000), (19554556107876187653359072340329/5629499534213120000000000000000000), (3502069850508634616459620978151/5629499534213120000000000000000000), (-53381423566875523733647099499/175921860444160000000000000000000), (-12598564582672909319305977629/225179981368524800000000000000000), (8408909225698816480754102517/1125899906842624000000000000000000), (3711771861600662399287914303/2814749767106560000000000000000000), (-52370962877445061461047637/703687441776640000000000000000000), (-42612095438119155629100681/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial159.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial159.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial159.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial159 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 4034888393808144573995714749774140), (Int.ofNat 208631590135543057858726155204057), (Int.negOfNat 11648370748444661221391260762878), (Int.negOfNat 13027159749728718746587836512085), (Int.negOfNat 1014640714325626148208461436250), (Int.ofNat 488554135173685111892865967362), (Int.ofNat 57447217967779545903632788652), (Int.negOfNat 6635003009809629240226000792), (Int.negOfNat 911876997271012126460473238), (Int.ofNat 50238740511811866240254498), (Int.ofNat 7923556949990650105211319), (Int.negOfNat 250810060877277824086639), (Int.negOfNat 45322324701306326016330), (Int.ofNat 901379797609012220150), (Int.ofNat 186597252046476326552), (Int.negOfNat 2358710627715230560), (Int.negOfNat 586972700337553163), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-201744419690407228699785737488707/281474976710656000000000000000000), (208631590135543057858726155204057/5629499534213120000000000000000000), (-5824185374222330610695630381439/2814749767106560000000000000000000), (-2605431949945743749317567302417/1125899906842624000000000000000000), (-811712571460500918566769149/4503599627370496000000000000000), (244277067586842555946432983681/2814749767106560000000000000000000), (14361804491944886475908197163/1407374883553280000000000000000000), (-829375376226203655028250099/703687441776640000000000000000000), (-455938498635506063230236619/2814749767106560000000000000000000), (25119370255905933120127249/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial159.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial159.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial159.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial159 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 3766409445598481772948029062577620), (Int.ofNat 19604088750074300290336733196174), (Int.negOfNat 67070984947672983758476117879695), (Int.ofNat 2616235430953544576632888186808), (Int.ofNat 4731858547977548106811349575799), (Int.ofNat 365701594208016756772021538107), (Int.negOfNat 83247044286321247762818770508), (Int.negOfNat 8683283725064211148251149903), (Int.ofNat 797799910254872238680585762), (Int.ofNat 94454119404879906802790769), (Int.negOfNat 5015757641209800005252722), (Int.negOfNat 639629940419193200966611), (Int.ofNat 22692354142633658083876), (Int.ofNat 3031540817781188470070), (Int.negOfNat 78141366301727232095), (Int.negOfNat 10781195767786052169), (Int.ofNat 195773511397095703), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-188320472279924088647401453128881/281474976710656000000000000000000), (9802044375037150145168366598087/2814749767106560000000000000000000), (-13414196989534596751695223575939/1125899906842624000000000000000000), (327029428869193072079111023351/703687441776640000000000000000000), (4731858547977548106811349575799/5629499534213120000000000000000000), (365701594208016756772021538107/5629499534213120000000000000000000), (-20811761071580311940704692627/1407374883553280000000000000000000), (-8683283725064211148251149903/5629499534213120000000000000000000), (398899955127436119340292881/2814749767106560000000000000000000), (94454119404879906802790769/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial159.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial159.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial159.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial159 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 3893336140456641641031488922947366), (Int.negOfNat 55480576843274139291368312546170), (Int.ofNat 67423791596153105559867201606055), (Int.ofNat 38753751238150825545732194883731), (Int.ofNat 2146554848727871286154752136849), (Int.negOfNat 870995846468499952664676159856), (Int.negOfNat 76372851576577379009859592407), (Int.ofNat 10348359234186998573998663699), (Int.ofNat 1032580166479391704379491753), (Int.negOfNat 79924895748428334330613163), (Int.negOfNat 8268384525338073811894556), (Int.ofNat 439148083772475292695581), (Int.ofNat 45145775873963185280317), (Int.negOfNat 1810674432455274610983), (Int.negOfNat 180731383539246518094), (Int.ofNat 5712712639181512987), (Int.ofNat 603067763594002280), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-1946668070228320820515744461473683/2814749767106560000000000000000000), (-5548057684327413929136831254617/562949953421312000000000000000000), (13484758319230621111973440321211/1125899906842624000000000000000000), (38753751238150825545732194883731/5629499534213120000000000000000000), (2146554848727871286154752136849/5629499534213120000000000000000000), (-54437240404281247041542259991/351843720888320000000000000000000), (-76372851576577379009859592407/5629499534213120000000000000000000), (10348359234186998573998663699/5629499534213120000000000000000000), (1032580166479391704379491753/5629499534213120000000000000000000), (-79924895748428334330613163/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial159.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial159.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial159.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial159 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 3421446361009612828439585509746541), (Int.ofNat 669078990885629413248345708652357), (Int.ofNat 271810465560479087037950387631930), (Int.ofNat 15978469067590257532794731008200), (Int.negOfNat 7501686250891372255661396660609), (Int.negOfNat 666614884900046821127433935903), (Int.ofNat 111306251262962243151439488348), (Int.ofNat 10619866966581494600377983227), (Int.negOfNat 1060083580005595079948251666), (Int.negOfNat 98966112337491662607625284), (Int.ofNat 7066139387587423677659627), (Int.ofNat 619369716816534733456332), (Int.negOfNat 34685106843919614729249), (Int.negOfNat 2804188520538362447569), (Int.ofNat 130061576798360117591), (Int.ofNat 9604305687641876655), (Int.negOfNat 396808262749913052), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-3421446361009612828439585509746541/5629499534213120000000000000000000), (669078990885629413248345708652357/5629499534213120000000000000000000), (27181046556047908703795038763193/562949953421312000000000000000000), (79892345337951287663973655041/28147497671065600000000000000000), (-7501686250891372255661396660609/5629499534213120000000000000000000), (-666614884900046821127433935903/5629499534213120000000000000000000), (27826562815740560787859872087/1407374883553280000000000000000000), (10619866966581494600377983227/5629499534213120000000000000000000), (-530041790002797539974125833/2814749767106560000000000000000000), (-24741528084372915651906321/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial159.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial159.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial159.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial159.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial159 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial159 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial159 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 5022214824415713608683945836679114), (Int.negOfNat 907373649619126712453132321683861), (Int.ofNat 319298680301537092095534328807121), (Int.negOfNat 13951409133656348437641356570818), (Int.negOfNat 7755358758310401916494853424274), (Int.ofNat 660771199468149931994029565097), (Int.ofNat 111873236253267072124445478387), (Int.negOfNat 10611108503217146069461712227), (Int.negOfNat 1060778838383923193165450666), (Int.ofNat 98958037485412195602293284), (Int.ofNat 7066675595925439385508627), (Int.negOfNat 619364427989203314600332), (Int.negOfNat 34685106843919614729249), (Int.ofNat 2804188520538362447569), (Int.ofNat 130061576798360117591), (Int.negOfNat 9604305687641876655), (Int.negOfNat 396808262749913052), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-2511107412207856804341972918339557/2814749767106560000000000000000000), (-907373649619126712453132321683861/5629499534213120000000000000000000), (319298680301537092095534328807121/5629499534213120000000000000000000), (-6975704566828174218820678285409/2814749767106560000000000000000000), (-3877679379155200958247426712137/2814749767106560000000000000000000), (660771199468149931994029565097/5629499534213120000000000000000000), (111873236253267072124445478387/5629499534213120000000000000000000), (-10611108503217146069461712227/5629499534213120000000000000000000), (-530389419191961596582725333/2814749767106560000000000000000000), (24739509371353048900573321/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial159.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial159.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial159.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 5768733114385625057355979684760908), (Int.ofNat 22990538367541108747063962662828), (Int.ofNat 120659416206708446254078198515419), (Int.negOfNat 38895477331919187681124345399095), (Int.ofNat 1870113098791773304418155657486), (Int.ofNat 872368384963008631281530416226), (Int.negOfNat 75764682655456430345349948407), (Int.negOfNat 10351353238782233522877060699), (Int.ofNat 1031840491098026614733293753), (Int.ofNat 79928143223946764976266163), (Int.negOfNat 8267815896199006602891556), (Int.negOfNat 439150067082724574766581), (Int.ofNat 45145775873963185280317), (Int.ofNat 1810674432455274610983), (Int.negOfNat 180731383539246518094), (Int.negOfNat 5712712639181512987), (Int.ofNat 603067763594002280), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-1442183278596406264338994921190227/1407374883553280000000000000000000), (5747634591885277186765990665707/1407374883553280000000000000000000), (120659416206708446254078198515419/5629499534213120000000000000000000), (-7779095466383837536224869079819/1125899906842624000000000000000000), (935056549395886652209077828743/2814749767106560000000000000000000), (436184192481504315640765208113/2814749767106560000000000000000000), (-75764682655456430345349948407/5629499534213120000000000000000000), (-10351353238782233522877060699/5629499534213120000000000000000000), (1031840491098026614733293753/5629499534213120000000000000000000), (79928143223946764976266163/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial159.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial159.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial159.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 5499318601093358261258146516938548), (Int.ofNat 150526005225359174154735119838737), (Int.negOfNat 21067871313812618327878014935545), (Int.negOfNat 4820263030847762958460221645298), (Int.ofNat 4503986167551500531858976425791), (Int.negOfNat 357602861177632972698930030978), (Int.negOfNat 82759591503960213748674422908), (Int.ofNat 8669449608231135332441018903), (Int.ofNat 797215881462060495539693762), (Int.negOfNat 94440484459547750371047769), (Int.negOfNat 5015311518748146292639722), (Int.ofNat 639621346074779645325611), (Int.ofNat 22692354142633658083876), (Int.negOfNat 3031540817781188470070), (Int.negOfNat 78141366301727232095), (Int.ofNat 10781195767786052169), (Int.ofNat 195773511397095703), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-1374829650273339565314536629234637/1407374883553280000000000000000000), (150526005225359174154735119838737/5629499534213120000000000000000000), (-4213574262762523665575602987109/1125899906842624000000000000000000), (-2410131515423881479230110822649/2814749767106560000000000000000000), (4503986167551500531858976425791/5629499534213120000000000000000000), (-178801430588816486349465015489/2814749767106560000000000000000000), (-20689897875990053437168605727/1407374883553280000000000000000000), (8669449608231135332441018903/5629499534213120000000000000000000), (398607940731030247769846881/2814749767106560000000000000000000), (-94440484459547750371047769/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial159.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial159.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial159.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 5264514642127035055166043728392860), (Int.ofNat 112505438443805069136926505514044), (Int.ofNat 16416252064956825409549588413089), (Int.ofNat 9393380943001677906931834044574), (Int.negOfNat 1136745692105392838363548636711), (Int.negOfNat 475998877517692936738364377208), (Int.ofNat 57686100116903360845177388691), (Int.ofNat 6614164125606847571576240792), (Int.negOfNat 912148591773675938530217238), (Int.negOfNat 50218478292496743465071498), (Int.ofNat 7923758464188225695734319), (Int.ofNat 250797499912365704303639), (Int.negOfNat 45322324701306326016330), (Int.negOfNat 901379797609012220150), (Int.ofNat 186597252046476326552), (Int.ofNat 2358710627715230560), (Int.negOfNat 586972700337553163), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-263225732106351752758302186419643/281474976710656000000000000000000), (28126359610951267284231626378511/1407374883553280000000000000000000), (16416252064956825409549588413089/5629499534213120000000000000000000), (4696690471500838953465917022287/2814749767106560000000000000000000), (-1136745692105392838363548636711/5629499534213120000000000000000000), (-59499859689711617092295547151/703687441776640000000000000000000), (57686100116903360845177388691/5629499534213120000000000000000000), (826770515700855946447030099/703687441776640000000000000000000), (-456074295886837969265108619/2814749767106560000000000000000000), (-25109239146248371732535749/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial159.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial159.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial159.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 4927823865436925683829880787912878), (Int.ofNat 229466633379993318551035784818030), (Int.ofNat 23933343835909029981070003537343), (Int.negOfNat 7584302031379035346427836361855), (Int.negOfNat 1696480250012213314988078970315), (Int.ofNat 328555900931723513791306743967), (Int.ofNat 41975362935387232191874738316), (Int.negOfNat 7445687064855121382383025606), (Int.negOfNat 418855932469766631200844096), (Int.ofNat 85245526791358449900035362), (Int.ofNat 2343010825934026677950597), (Int.negOfNat 600965055332935570603081), (Int.negOfNat 8239773003890336388485), (Int.ofNat 2923224557009464980169), (Int.ofNat 18071102888717442378), (Int.negOfNat 10633795377030232391), (Int.negOfNat 103781129761393), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-2463911932718462841914940393956439/2814749767106560000000000000000000), (22946663337999331855103578481803/562949953421312000000000000000000), (23933343835909029981070003537343/5629499534213120000000000000000000), (-1516860406275807069285567272371/1125899906842624000000000000000000), (-339296050002442662997615794063/1125899906842624000000000000000000), (328555900931723513791306743967/5629499534213120000000000000000000), (10493840733846808047968684579/1407374883553280000000000000000000), (-3722843532427560691191512803/2814749767106560000000000000000000), (-6544623944840103612513189/87960930222080000000000000000000), (42622763395679224950017681/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial159.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial159.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial159.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 4448790582257779387478323311046610), (Int.ofNat 210681767161996732147381353735330), (Int.negOfNat 31280739037818113422400277944917), (Int.negOfNat 5749218379506483473243526013882), (Int.ofNat 1903520606180547214525364763602), (Int.ofNat 192269615629438480047613124195), (Int.negOfNat 52760726359606569215546630245), (Int.negOfNat 2692419418235759302189422688), (Int.ofNat 794321296277897125675844715), (Int.ofNat 16788850325021946782079888), (Int.negOfNat 7021827914531408268500037), (Int.negOfNat 43708362411840178259635), (Int.ofNat 40963057262840883550316), (Int.negOfNat 67234651426396910894), (Int.negOfNat 170779899571044596703), (Int.ofNat 1018437448886280627), (Int.ofNat 570877637081104046), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-444879058225777938747832331104661/562949953421312000000000000000000), (21068176716199673214738135373533/562949953421312000000000000000000), (-31280739037818113422400277944917/5629499534213120000000000000000000), (-2874609189753241736621763006941/2814749767106560000000000000000000), (951760303090273607262682381801/2814749767106560000000000000000000), (38453923125887696009522624839/1125899906842624000000000000000000), (-10552145271921313843109326049/1125899906842624000000000000000000), (-84138106819867478193419459/175921860444160000000000000000000), (158864259255579425135168943/1125899906842624000000000000000000), (1049303145313871673879993/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial159.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial159.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial159.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 4165451283116036733387958053624567), (Int.ofNat 82342762226495933010482462021845), (Int.negOfNat 17760505282066964321120910142585), (Int.ofNat 8628710376081746815479094657698), (Int.ofNat 772806380157494439146543318201), (Int.negOfNat 331273386171442493417103128369), (Int.negOfNat 12164992160849632186540792221), (Int.ofNat 6422937339803215023291313424), (Int.ofNat 66204407558852064111172415), (Int.negOfNat 71832565412343725471159664), (Int.ofNat 288214548993794640081168), (Int.ofNat 509688895948606762753230), (Int.negOfNat 5917100958492622755181), (Int.negOfNat 2501115209752361538347), (Int.ofNat 39491466589049241861), (Int.ofNat 9192660159996483291), (Int.negOfNat 195565949137572917), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-4165451283116036733387958053624567/5629499534213120000000000000000000), (16468552445299186602096492404369/1125899906842624000000000000000000), (-3552101056413392864224182028517/1125899906842624000000000000000000), (4314355188040873407739547328849/2814749767106560000000000000000000), (772806380157494439146543318201/5629499534213120000000000000000000), (-331273386171442493417103128369/5629499534213120000000000000000000), (-12164992160849632186540792221/5629499534213120000000000000000000), (401433583737700938955707089/351843720888320000000000000000000), (13240881511770412822234483/1125899906842624000000000000000000), (-4489535338271482841947479/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial159.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial159.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial159.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 4000988901350825082898611704426657), (Int.ofNat 113524232182846079807220246515323), (Int.ofNat 27258384361072395473505664796545), (Int.ofNat 2967740793248672959671515568844), (Int.negOfNat 1663083379666121415059191339772), (Int.negOfNat 36844809272279914257249057337), (Int.ofNat 44555260354900074407127208307), (Int.negOfNat 287785284405794660687509955), (Int.negOfNat 637819780175037918038638131), (Int.ofNat 12067802937602502225282003), (Int.ofNat 5575970581965393054357611), (Int.negOfNat 140571782088555958154023), (Int.negOfNat 32559067517789213395074), (Int.ofNat 925721258450383554967), (Int.ofNat 136004107125015827484), (Int.negOfNat 4091481154666388014), (Int.negOfNat 489559330402210159), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-4000988901350825082898611704426657/5629499534213120000000000000000000), (113524232182846079807220246515323/5629499534213120000000000000000000), (5451676872214479094701132959309/1125899906842624000000000000000000), (741935198312168239917878892211/1407374883553280000000000000000000), (-415770844916530353764797834943/1407374883553280000000000000000000), (-36844809272279914257249057337/5629499534213120000000000000000000), (44555260354900074407127208307/5629499534213120000000000000000000), (-57557056881158932137501991/1125899906842624000000000000000000), (-637819780175037918038638131/5629499534213120000000000000000000), (12067802937602502225282003/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial159.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial159.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial159.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 3666290445977085802046375018299184), (Int.ofNat 209830994274324579457254429280349), (Int.ofNat 11674019939885138710870705547576), (Int.negOfNat 5844728396278007012583927287994), (Int.negOfNat 39154989640034643888019777452), (Int.ofNat 250165826841766079519083746468), (Int.negOfNat 7773920619371985292366960767), (Int.negOfNat 4817034844310847018167855299), (Int.ofNat 199377247119182787787194673), (Int.ofNat 52839820943757884436338979), (Int.negOfNat 2382808407182818683385457), (Int.negOfNat 371863341486116226054537), (Int.ofNat 17304845745582477460318), (Int.ofNat 1816780863613635772249), (Int.negOfNat 85194480113126292196), (Int.negOfNat 6572933031767429254), (Int.ofNat 315282393811496379), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-229143152873567862627898438643699/351843720888320000000000000000000), (209830994274324579457254429280349/5629499534213120000000000000000000), (1459252492485642338858838193447/703687441776640000000000000000000), (-2922364198139003506291963643997/2814749767106560000000000000000000), (-9788747410008660972004944363/1407374883553280000000000000000000), (62541456710441519879770936617/1407374883553280000000000000000000), (-7773920619371985292366960767/5629499534213120000000000000000000), (-4817034844310847018167855299/5629499534213120000000000000000000), (199377247119182787787194673/5629499534213120000000000000000000), (52839820943757884436338979/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial159.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial159.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial159.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 3240350512429520924699574164882859), (Int.ofNat 201810042797261853241614248036414), (Int.negOfNat 8859321107600383289343162750792), (Int.ofNat 498748509340604552338123725385), (Int.ofNat 1038673366626302436997779400391), (Int.negOfNat 79867779586812933104519517363), (Int.negOfNat 29534667292212375667373723595), (Int.ofNat 2322971713580275960632495590), (Int.ofNat 422026759301411678593165159), (Int.negOfNat 32404964872521893937408958), (Int.negOfNat 3641367250752682512273820), (Int.ofNat 272277521958756718851270), (Int.ofNat 21004952114333004703991), (Int.negOfNat 1535942979391332193929), (Int.negOfNat 86737785049482698659), (Int.ofNat 6296005602009429537), (Int.ofNat 348382801386354541), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-3240350512429520924699574164882859/5629499534213120000000000000000000), (100905021398630926620807124018207/2814749767106560000000000000000000), (-1107415138450047911167895343849/703687441776640000000000000000000), (99749701868120910467624745077/1125899906842624000000000000000000), (1038673366626302436997779400391/5629499534213120000000000000000000), (-79867779586812933104519517363/5629499534213120000000000000000000), (-5906933458442475133474744719/1125899906842624000000000000000000), (232297171358027596063249559/562949953421312000000000000000000), (422026759301411678593165159/5629499534213120000000000000000000), (-16202482436260946968704479/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial159.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial159.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial159.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 2855619247981817205896914642755744), (Int.ofNat 194918244635280016071679946451690), (Int.ofNat 7718441458691657237093555488514), (Int.ofNat 2728238023330062260513231739893), (Int.negOfNat 575048887761823749526277563227), (Int.negOfNat 135172607680806031001524048504), (Int.ofNat 21123763381023667510245955369), (Int.ofNat 2687920903825165269150412642), (Int.negOfNat 365133896866193753711355409), (Int.negOfNat 29237059267638440054288430), (Int.ofNat 3673739084924435545403031), (Int.ofNat 201380994912622758753575), (Int.negOfNat 24215409174557004141356), (Int.negOfNat 958319920576791904742), (Int.ofNat 112924661220611906177), (Int.ofNat 3256367319836766601), (Int.negOfNat 364410573977492032), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-89238101499431787684278582586117/175921860444160000000000000000000), (19491824463528001607167994645169/562949953421312000000000000000000), (3859220729345828618546777744257/2814749767106560000000000000000000), (2728238023330062260513231739893/5629499534213120000000000000000000), (-575048887761823749526277563227/5629499534213120000000000000000000), (-16896575960100753875190506063/703687441776640000000000000000000), (21123763381023667510245955369/5629499534213120000000000000000000), (1343960451912582634575206321/2814749767106560000000000000000000), (-365133896866193753711355409/5629499534213120000000000000000000), (-2923705926763844005428843/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial159.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial159.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial159.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 2425017794030938426554347139374362), (Int.ofNat 234154630845753633822849234856809), (Int.ofNat 5606076184341896685454693568877), (Int.negOfNat 3143502903976759000592807807168), (Int.negOfNat 378981351034276986863669777280), (Int.ofNat 154506959901702447856119277689), (Int.ofNat 11982651615760611579608535020), (Int.negOfNat 3440642015474045193006671148), (Int.negOfNat 172503079097615111378493300), (Int.ofNat 42647394712538608589718420), (Int.ofNat 1434308321308865830196245), (Int.negOfNat 334833239465963918828779), (Int.negOfNat 7781185956713537178717), (Int.ofNat 1810633285568105893187), (Int.ofNat 29529041573981252718), (Int.negOfNat 7200638710494874737), (Int.negOfNat 152713071119020231), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-1212508897015469213277173569687181/2814749767106560000000000000000000), (234154630845753633822849234856809/5629499534213120000000000000000000), (5606076184341896685454693568877/5629499534213120000000000000000000), (-49117232874636859384262621987/87960930222080000000000000000000), (-592158360991057791974484027/8796093022208000000000000000000), (154506959901702447856119277689/5629499534213120000000000000000000), (599132580788030578980426751/281474976710656000000000000000000), (-860160503868511298251667787/1407374883553280000000000000000000), (-1725030790976151113784933/56294995342131200000000000000000), (2132369735626930429485921/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial159.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial159.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial159.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 1960246801326665223178002664046546), (Int.ofNat 219774411135281248429401465353960), (Int.negOfNat 9531955701474138424064558731474), (Int.negOfNat 76913605488702359816517239225), (Int.ofNat 905239255889765728751021845866), (Int.ofNat 19462536046737031796897442889), (Int.negOfNat 27036591334934506537739656862), (Int.negOfNat 447590249924811115546498046), (Int.ofNat 424101528581991625690389306), (Int.ofNat 4313226126349752922990140), (Int.negOfNat 4044488003784574126183429), (Int.negOfNat 21212540315359301753439), (Int.ofNat 25794098818605562765562), (Int.ofNat 46376227416479722086), (Int.negOfNat 117233538751493064208), (Int.ofNat 149701919495978292), (Int.ofNat 348315510721042915), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-980123400663332611589001332023273/2814749767106560000000000000000000), (5494360278382031210735036633849/140737488355328000000000000000000), (-4765977850737069212032279365737/2814749767106560000000000000000000), (-3076544219548094392660689569/225179981368524800000000000000000), (452619627944882864375510922933/2814749767106560000000000000000000), (19462536046737031796897442889/5629499534213120000000000000000000), (-13518295667467253268869828431/2814749767106560000000000000000000), (-223795124962405557773249023/2814749767106560000000000000000000), (212050764290995812845194653/2814749767106560000000000000000000), (215661306317487646149507/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial159.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial159.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial159.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 1546015417357651834092021477010989), (Int.ofNat 206280632210084654355090783167467), (Int.ofNat 7234128235669672019677844174481), (Int.ofNat 4089988512556164505311272032727), (Int.negOfNat 207357246721749125641886462047), (Int.negOfNat 174609796065608806105732695628), (Int.ofNat 4640440824932923719561289798), (Int.ofNat 3573978595363354442335605511), (Int.negOfNat 69341773441310172510455974), (Int.negOfNat 42267202398868373888166493), (Int.ofNat 720721210191060659504550), (Int.ofNat 322846134496914389110109), (Int.negOfNat 5197904294301126404372), (Int.negOfNat 1716925158250672049126), (Int.ofNat 26353740504395778145), (Int.ofNat 6790076908360458459), (Int.negOfNat 42956659148314079), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-1546015417357651834092021477010989/5629499534213120000000000000000000), (206280632210084654355090783167467/5629499534213120000000000000000000), (7234128235669672019677844174481/5629499534213120000000000000000000), (4089988512556164505311272032727/5629499534213120000000000000000000), (-207357246721749125641886462047/5629499534213120000000000000000000), (-43652449016402201526433173907/1407374883553280000000000000000000), (2320220412466461859780644899/2814749767106560000000000000000000), (3573978595363354442335605511/5629499534213120000000000000000000), (-34670886720655086255227987/2814749767106560000000000000000000), (-42267202398868373888166493/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial159.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial159.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial159.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1079986531640242227588645706623519), (Int.ofNat 266023621285065133786780480239033), (Int.ofNat 16041877368826210440661025829799), (Int.negOfNat 2137200928048706105176173469736), (Int.negOfNat 900317555251511163661494149821), (Int.ofNat 79325716744800362403110928335), (Int.ofNat 25052786469699072851954878247), (Int.negOfNat 1523934970873577932412451567), (Int.negOfNat 376053823189802098303855271), (Int.ofNat 17978908966238650820745035), (Int.ofNat 3497990586876759542522172), (Int.negOfNat 141426081408787459096459), (Int.negOfNat 22006291930007832574755), (Int.ofNat 783395888629876564921), (Int.ofNat 99537890256279445106), (Int.negOfNat 3318024250274172865), (Int.negOfNat 332220447464593798), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-1079986531640242227588645706623519/5629499534213120000000000000000000), (266023621285065133786780480239033/5629499534213120000000000000000000), (16041877368826210440661025829799/5629499534213120000000000000000000), (-267150116006088263147021683717/703687441776640000000000000000000), (-900317555251511163661494149821/5629499534213120000000000000000000), (15865143348960072480622185667/1125899906842624000000000000000000), (25052786469699072851954878247/5629499534213120000000000000000000), (-1523934970873577932412451567/5629499534213120000000000000000000), (-376053823189802098303855271/5629499534213120000000000000000000), (3595781793247730164149007/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial159.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial159.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial159.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 511411584799201883698567600703869), (Int.ofNat 285880199669222988733238599542115), (Int.negOfNat 7610363454982765154643533469973), (Int.negOfNat 3543331497891829435160659187980), (Int.ofNat 659343820032689226100230373207), (Int.ofNat 141864787078223718668199924281), (Int.negOfNat 17719517556931158299944898899), (Int.negOfNat 2775453572861286388851676947), (Int.ofNat 264037986560456352790629970), (Int.ofNat 31994768930870905910781518), (Int.negOfNat 2483620044341296736971065), (Int.negOfNat 241465648367167353451808), (Int.ofNat 15936799055913568893359), (Int.ofNat 1279082964336134265907), (Int.negOfNat 73708661591167900649), (Int.negOfNat 5094875840228246673), (Int.ofNat 233261368330165350), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-511411584799201883698567600703869/5629499534213120000000000000000000), (57176039933844597746647719908423/1125899906842624000000000000000000), (-7610363454982765154643533469973/5629499534213120000000000000000000), (-177166574894591471758032959399/281474976710656000000000000000000), (659343820032689226100230373207/5629499534213120000000000000000000), (141864787078223718668199924281/5629499534213120000000000000000000), (-17719517556931158299944898899/5629499534213120000000000000000000), (-2775453572861286388851676947/5629499534213120000000000000000000), (26403798656045635279062997/562949953421312000000000000000000), (15997384465435452955390759/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial159.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial159.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial159.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 15241587563319658881792544280722), (Int.ofNat 241050507596485007896396981488698), (Int.negOfNat 7228279614971753452510367252018), (Int.ofNat 3615552577903294846823814980921), (Int.ofNat 621240159889773269651339030198), (Int.negOfNat 146335860146407230689983363656), (Int.negOfNat 16261560571443051836904219911), (Int.ofNat 2902710354759683977508860823), (Int.ofNat 235771857642791982828051570), (Int.negOfNat 33991761518145027946424152), (Int.negOfNat 2163038922041777975551835), (Int.ofNat 260640101400772196202132), (Int.ofNat 13599926099230512245641), (Int.negOfNat 1400954515633008991093), (Int.negOfNat 61883832238952711971), (Int.ofNat 5602866478203261167), (Int.ofNat 191043918448738180), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(7620793781659829440896272140361/2814749767106560000000000000000000), (120525253798242503948198490744349/2814749767106560000000000000000000), (-3614139807485876726255183626009/2814749767106560000000000000000000), (3615552577903294846823814980921/5629499534213120000000000000000000), (310620079944886634825669515099/2814749767106560000000000000000000), (-18291982518300903836247920457/703687441776640000000000000000000), (-16261560571443051836904219911/5629499534213120000000000000000000), (2902710354759683977508860823/5629499534213120000000000000000000), (23577185764279198282805157/562949953421312000000000000000000), (-4248970189768128493303019/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial159.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial159.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial159.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 501983123063787034327593520901150), (Int.ofNat 262030259440003320097841313362028), (Int.ofNat 15964745666999860475361703730557), (Int.ofNat 1974342829823877052456227308952), (Int.negOfNat 894941370493488246071221660949), (Int.negOfNat 69412382873098558515112364523), (Int.ofNat 24990357616456346156061414563), (Int.ofNat 1253580314121848330221992383), (Int.negOfNat 378214680495954843119659429), (Int.negOfNat 13993289485176968330049635), (Int.ofNat 3560613260462701606224608), (Int.ofNat 105736947171415298445681), (Int.negOfNat 22703370512161735930965), (Int.negOfNat 571302419465572213379), (Int.ofNat 103823551967856317614), (Int.ofNat 2420483130362715035), (Int.negOfNat 352977813004088812), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(10039662461275740686551870418023/112589990684262400000000000000000), (65507564860000830024460328340507/1407374883553280000000000000000000), (15964745666999860475361703730557/5629499534213120000000000000000000), (246792853727984631557028413619/703687441776640000000000000000000), (-894941370493488246071221660949/5629499534213120000000000000000000), (-69412382873098558515112364523/5629499534213120000000000000000000), (24990357616456346156061414563/5629499534213120000000000000000000), (1253580314121848330221992383/5629499534213120000000000000000000), (-378214680495954843119659429/5629499534213120000000000000000000), (-2798657897035393666009927/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial159.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial159.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial159.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1090816729410489234074337972386406), (Int.ofNat 320349307106550209900928904100665), (Int.ofNat 6919479253011956395525469145438), (Int.negOfNat 3957697163036407856475924044325), (Int.negOfNat 169317655798901994777141483397), (Int.ofNat 167581648964072346893081242058), (Int.ofNat 2918470487131811674308513732), (Int.negOfNat 3427286313896353006656186199), (Int.negOfNat 32307063511035344949513766), (Int.ofNat 40838737669591943522046037), (Int.ofNat 281817354581075479335830), (Int.negOfNat 316020469246422217680311), (Int.negOfNat 1982963617210633187568), (Int.ofNat 1704587283955699828994), (Int.ofNat 10683709780325914175), (Int.negOfNat 6779756558347436681), (Int.ofNat 9990832904079169), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(545408364705244617037168986193203/2814749767106560000000000000000000), (64069861421310041980185780820133/1125899906842624000000000000000000), (3459739626505978197762734572719/2814749767106560000000000000000000), (-158307886521456314259036961773/225179981368524800000000000000000), (-169317655798901994777141483397/5629499534213120000000000000000000), (83790824482036173446540621029/2814749767106560000000000000000000), (729617621782952918577128433/1407374883553280000000000000000000), (-3427286313896353006656186199/5629499534213120000000000000000000), (-16153531755517672474756883/2814749767106560000000000000000000), (40838737669591943522046037/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial159.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial159.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial159.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 1729945589064519889095104062725196), (Int.ofNat 307607082050608048353211274047009), (Int.negOfNat 8961724460457812499850207008880), (Int.ofNat 91608670073093701765264589364), (Int.ofNat 841248710523118637509249130032), (Int.negOfNat 24151924623970229986084554038), (Int.negOfNat 24715148430488762730304415477), (Int.ofNat 669241617041169638713717924), (Int.ofNat 387482524787761016061819714), (Int.negOfNat 8450820820497559188144830), (Int.negOfNat 3742996656333072481885771), (Int.ofNat 61753860220859985793061), (Int.ofNat 24297758045097668488578), (Int.negOfNat 293831565102880035654), (Int.negOfNat 112544968186680106872), (Int.ofNat 933518881103567392), (Int.ofNat 336882749747639695), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(432486397266129972273776015681299/1407374883553280000000000000000000), (307607082050608048353211274047009/5629499534213120000000000000000000), (-112021555755722656248127587611/70368744177664000000000000000000), (22902167518273425441316147341/1407374883553280000000000000000000), (52578044407694914844328070627/351843720888320000000000000000000), (-12075962311985114993042277019/2814749767106560000000000000000000), (-24715148430488762730304415477/5629499534213120000000000000000000), (167310404260292409678429481/1407374883553280000000000000000000), (193741262393880508030909857/2814749767106560000000000000000000), (-845082082049755918814483/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial159.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial159.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial159.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 2321327993575466606846935503977429), (Int.ofNat 293761216682735694669098015930608), (Int.ofNat 4979439268711409929528658012947), (Int.ofNat 2872496687124171705755289152981), (Int.negOfNat 340720680746526262064881392437), (Int.negOfNat 134062147543230466936718312486), (Int.ofNat 12001284289362747733837334660), (Int.ofNat 2922737940150984248505546302), (Int.negOfNat 196122129001302002694221500), (Int.negOfNat 36685163783521349266715030), (Int.ofNat 1832482703414899189316895), (Int.ofNat 295457023140931538861381), (Int.negOfNat 11026612861646439076123), (Int.negOfNat 1638886293057110380293), (Int.ofNat 46321014291871520542), (Int.ofNat 6632356167591616903), (Int.negOfNat 205660563171413479), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(2321327993575466606846935503977429/5629499534213120000000000000000000), (18360076042670980916818625995663/351843720888320000000000000000000), (4979439268711409929528658012947/5629499534213120000000000000000000), (2872496687124171705755289152981/5629499534213120000000000000000000), (-340720680746526262064881392437/5629499534213120000000000000000000), (-67031073771615233468359156243/2814749767106560000000000000000000), (600064214468137386691866733/281474976710656000000000000000000), (1461368970075492124252773151/2814749767106560000000000000000000), (-392244258002604005388443/11258999068426240000000000000000), (-3668516378352134926671503/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial159.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial159.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial159.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 2943082264410688649231218123997849), (Int.ofNat 329861540831240749128811015625436), (Int.ofNat 7664489088705279757218987892030), (Int.negOfNat 2168535257975853917096225655188), (Int.negOfNat 475293959641388485113312867206), (Int.ofNat 115564653124578184612189027010), (Int.ofNat 15865497225034687650971315601), (Int.negOfNat 2608125069509736990986888428), (Int.negOfNat 277795822774102177007766791), (Int.ofNat 31567769877180436588170840), (Int.ofNat 2930010346364564221443089), (Int.negOfNat 235268439894733807741665), (Int.negOfNat 20239894143016543806864), (Int.ofNat 1185705872695299010898), (Int.ofNat 97742847640737730023), (Int.negOfNat 4310666957705078579), (Int.negOfNat 320787686491190578), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(2943082264410688649231218123997849/5629499534213120000000000000000000), (82465385207810187282202753906359/1407374883553280000000000000000000), (766448908870527975721898789203/562949953421312000000000000000000), (-542133814493963479274056413797/1407374883553280000000000000000000), (-237646979820694242556656433603/2814749767106560000000000000000000), (11556465312457818461218902701/562949953421312000000000000000000), (15865497225034687650971315601/5629499534213120000000000000000000), (-652031267377434247746722107/1407374883553280000000000000000000), (-277795822774102177007766791/5629499534213120000000000000000000), (789194246929510914704271/140737488355328000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial159.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial159.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial159.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 3612837431440103030993703664972189), (Int.ofNat 330210771570463270054670574064729), (Int.negOfNat 5779909639013309461489343574591), (Int.negOfNat 565275106805572584562113037361), (Int.ofNat 745553893556031258499385651363), (Int.ofNat 41150284013188592095050902043), (Int.negOfNat 25056170246179323199500016155), (Int.negOfNat 1285214729784957834191117520), (Int.ofNat 410049775340815746191040981), (Int.ofNat 20807074784688739129911132), (Int.negOfNat 3867506358956392627160060), (Int.negOfNat 197116926722267360563330), (Int.ofNat 23544100737296866564389), (Int.ofNat 1202209035572084941671), (Int.negOfNat 100617974575779623581), (Int.negOfNat 5191220950557867803), (Int.ofNat 401330293438747789), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(3612837431440103030993703664972189/5629499534213120000000000000000000), (330210771570463270054670574064729/5629499534213120000000000000000000), (-5779909639013309461489343574591/5629499534213120000000000000000000), (-565275106805572584562113037361/5629499534213120000000000000000000), (745553893556031258499385651363/5629499534213120000000000000000000), (41150284013188592095050902043/5629499534213120000000000000000000), (-5011234049235864639900003231/1125899906842624000000000000000000), (-16065184122311972927388969/70368744177664000000000000000000), (410049775340815746191040981/5629499534213120000000000000000000), (5201768696172184782477783/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial159.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial159.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial159.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 4257206070602900489536158992826020), (Int.ofNat 322517456659409781813211481487812), (Int.ofNat 5918936382628187344482464311025), (Int.ofNat 3098317842106642166939957382685), (Int.negOfNat 220020590642410410988774247482), (Int.negOfNat 176181277625347212020826090158), (Int.ofNat 2518516859691505345023680867), (Int.ofNat 4196402070528705932392194771), (Int.ofNat 41852600087157562964124107), (Int.negOfNat 52263422095406567059730131), (Int.negOfNat 1148681633226837785789763), (Int.ofNat 391751601955909150788223), (Int.ofNat 10919705067332050996322), (Int.negOfNat 1980713683131517733371), (Int.negOfNat 61226774339127446104), (Int.ofNat 7383710663485185966), (Int.ofNat 239469379812296691), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(212860303530145024476807949641301/281474976710656000000000000000000), (80629364164852445453302870371953/1407374883553280000000000000000000), (236757455305127493779298572441/225179981368524800000000000000000), (619663568421328433387991476537/1125899906842624000000000000000000), (-110010295321205205494387123741/2814749767106560000000000000000000), (-88090638812673606010413045079/2814749767106560000000000000000000), (2518516859691505345023680867/5629499534213120000000000000000000), (4196402070528705932392194771/5629499534213120000000000000000000), (41852600087157562964124107/5629499534213120000000000000000000), (-52263422095406567059730131/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial159.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial159.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial159.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 4942227075598177961491043317836983), (Int.ofNat 364522529887340836096664729544357), (Int.ofNat 8390647619639714020757381622079), (Int.negOfNat 3162595865313329843754976983674), (Int.negOfNat 817854012869529808352126217447), (Int.ofNat 122661652901248442069794443939), (Int.ofNat 32950457935517225518092715043), (Int.negOfNat 1648850968745830372710495905), (Int.negOfNat 588867549802660252780863769), (Int.ofNat 6134521554002951700027553), (Int.ofNat 5607388550541950843053849), (Int.ofNat 32022345499456679295737), (Int.negOfNat 33975618671440774135326), (Int.negOfNat 455067189167538234773), (Int.ofNat 144590629020447307216), (Int.ofNat 2571493822328813766), (Int.negOfNat 521046738112671251), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(4942227075598177961491043317836983/5629499534213120000000000000000000), (364522529887340836096664729544357/5629499534213120000000000000000000), (8390647619639714020757381622079/5629499534213120000000000000000000), (-1581297932656664921877488491837/2814749767106560000000000000000000), (-817854012869529808352126217447/5629499534213120000000000000000000), (122661652901248442069794443939/5629499534213120000000000000000000), (32950457935517225518092715043/5629499534213120000000000000000000), (-329770193749166074542099181/1125899906842624000000000000000000), (-588867549802660252780863769/5629499534213120000000000000000000), (6134521554002951700027553/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial159.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial159.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial159.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 5672129301857300893147895148618543), (Int.ofNat 348802738328366972096704626178659), (Int.negOfNat 14564207244596881629809106915533), (Int.negOfNat 1388884354026313652020263975011), (Int.ofNat 1361710284771846352844955313038), (Int.ofNat 170840674366972400005951756767), (Int.negOfNat 34645245789455866275425685249), (Int.negOfNat 5481272956561177099680675706), (Int.ofNat 313658940176564291105548565), (Int.ofNat 69708455695743923573592086), (Int.negOfNat 1382578342816370197703528), (Int.negOfNat 515386302684563228598370), (Int.ofNat 2270976336558590454561), (Int.ofNat 2574877686220781263133), (Int.ofNat 8589847255126548979), (Int.negOfNat 9588235110828227489), (Int.negOfNat 98292850796441073), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(5672129301857300893147895148618543/5629499534213120000000000000000000), (348802738328366972096704626178659/5629499534213120000000000000000000), (-14564207244596881629809106915533/5629499534213120000000000000000000), (-1388884354026313652020263975011/5629499534213120000000000000000000), (680855142385923176422477656519/2814749767106560000000000000000000), (170840674366972400005951756767/5629499534213120000000000000000000), (-34645245789455866275425685249/5629499534213120000000000000000000), (-2740636478280588549840337853/2814749767106560000000000000000000), (62731788035312858221109713/1125899906842624000000000000000000), (34854227847871961786796043/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial159.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial159.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial159.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 6324815788537059504900622631700768), (Int.ofNat 322482885151294726611778169292138), (Int.ofNat 12305925557630810420768379838582), (Int.ofNat 8620494351574012671474448710658), (Int.ofNat 49869143907365608274860104080), (Int.negOfNat 449607626149052817363097681961), (Int.negOfNat 40991882234691155398217072945), (Int.ofNat 5855386836351745624588160262), (Int.ofNat 757219605042282428809747605), (Int.negOfNat 40290667699224960140138502), (Int.negOfNat 6970364563468473981154323), (Int.ofNat 172459386275159724942125), (Int.ofNat 41148613180685766536664), (Int.negOfNat 479991744453569381134), (Int.negOfNat 173040898165939008897), (Int.ofNat 745071889601848887), (Int.ofNat 570174918278666904), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(197650493391783109528144457240649/175921860444160000000000000000000), (161241442575647363305889084646069/2814749767106560000000000000000000), (6152962778815405210384189919291/2814749767106560000000000000000000), (4310247175787006335737224355329/2814749767106560000000000000000000), (623364298842070103435751301/70368744177664000000000000000000), (-449607626149052817363097681961/5629499534213120000000000000000000), (-8198376446938231079643414589/1125899906842624000000000000000000), (2927693418175872812294080131/2814749767106560000000000000000000), (151443921008456485761949521/1125899906842624000000000000000000), (-20145333849612480070069251/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial159.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial159.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial159.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 7072672283984491599352832339540809), (Int.ofNat 436182277895577109603241244888300), (Int.ofNat 24452386903596736729316083294911), (Int.negOfNat 11199617709407751442498265221661), (Int.negOfNat 4662106984913062088680424256482), (Int.negOfNat 238915574433477861362344719335), (Int.ofNat 80047546216293867081678760185), (Int.ofNat 7306759959282754070522089864), (Int.negOfNat 719713335616686739569986224), (Int.negOfNat 84873427145019587226842748), (Int.ofNat 4163228334342959552932503), (Int.ofNat 595534028252186906506079), (Int.negOfNat 16967119846754070446435), (Int.negOfNat 2889951094229060805191), (Int.ofNat 51474443931968877762), (Int.ofNat 10492868219313672689), (Int.negOfNat 97376879470893237), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(7072672283984491599352832339540809/5629499534213120000000000000000000), (4361822778955771096032412448883/56294995342131200000000000000000), (24452386903596736729316083294911/5629499534213120000000000000000000), (-11199617709407751442498265221661/5629499534213120000000000000000000), (-2331053492456531044340212128241/2814749767106560000000000000000000), (-47783114886695572272468943867/1125899906842624000000000000000000), (16009509243258773416335752037/1125899906842624000000000000000000), (913344994910344258815261233/703687441776640000000000000000000), (-44982083476042921223124139/351843720888320000000000000000000), (-21218356786254896806710687/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial159.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial159.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial159.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 7876846432799074353119256831051760), (Int.ofNat 249033227350545664241913409855553), (Int.negOfNat 151245252174222897596836588317062), (Int.negOfNat 42813307557764936135349079144325), (Int.negOfNat 1272824283261138281972899553250), (Int.ofNat 890478137667593519517812100318), (Int.ofNat 65918526804574906787811375638), (Int.negOfNat 9998242065872284399441377258), (Int.negOfNat 947638161867408437630627902), (Int.ofNat 72765103934489924529018192), (Int.ofNat 7867719175065278620523121), (Int.negOfNat 374224079452866041845861), (Int.negOfNat 44134184968892492061570), (Int.ofNat 1438328255933319903990), (Int.ofNat 180415315037632521928), (Int.negOfNat 4151141128934593780), (Int.negOfNat 554079855022217787), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(98460580409988429413990710388147/70368744177664000000000000000000), (249033227350545664241913409855553/5629499534213120000000000000000000), (-75622626087111448798418294158531/2814749767106560000000000000000000), (-1712532302310597445413963165773/225179981368524800000000000000000), (-5091297133044553127891598213/22517998136852480000000000000000), (445239068833796759758906050159/2814749767106560000000000000000000), (32959263402287453393905687819/2814749767106560000000000000000000), (-4999121032936142199720688629/2814749767106560000000000000000000), (-473819080933704218815313951/2814749767106560000000000000000000), (4547818995905620283063637/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial159.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial159.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial159.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 7438296325231798991195317102405860), (Int.negOfNat 831790105307237315212014628210444), (Int.negOfNat 359618460065790365823705374815605), (Int.negOfNat 13635195057215385958529728491478), (Int.ofNat 8104632786928434503695314469041), (Int.ofNat 612347618378191059200832241193), (Int.negOfNat 112561791930716512295062314442), (Int.negOfNat 9996603222045896220853018827), (Int.ofNat 1023494931878203361693833098), (Int.ofNat 96017916146323040671910421), (Int.negOfNat 6498813926014801051602898), (Int.negOfNat 618811974400179901679809), (Int.ofNat 30353352305043089288824), (Int.ofNat 2873300627859016049930), (Int.negOfNat 108372457939835261625), (Int.negOfNat 10082306417179256411), (Int.ofNat 293046609738227547), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(371914816261589949559765855120293/281474976710656000000000000000000), (-207947526326809328803003657052611/1407374883553280000000000000000000), (-71923692013158073164741074963121/1125899906842624000000000000000000), (-6817597528607692979264864245739/2814749767106560000000000000000000), (8104632786928434503695314469041/5629499534213120000000000000000000), (612347618378191059200832241193/5629499534213120000000000000000000), (-56280895965358256147531157221/2814749767106560000000000000000000), (-9996603222045896220853018827/5629499534213120000000000000000000), (511747465939101680846916549/2814749767106560000000000000000000), (96017916146323040671910421/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial159.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial159.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial159.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 4368249841928088409042580398487376), (Int.negOfNat 2150410645776402810665120227639170), (Int.negOfNat 229476458004354072601977896131415), (Int.ofNat 54316284952273073618901486922769), (Int.ofNat 6100090231843032569934392512181), (Int.negOfNat 992829086664559070792898080654), (Int.negOfNat 102023210910251544845514840623), (Int.ofNat 11722599278006908906971605271), (Int.ofNat 1096103304655937562072565067), (Int.negOfNat 93383018821493323468209167), (Int.negOfNat 8015733202485756657867464), (Int.ofNat 530911589943548920994559), (Int.ofNat 42099123306022905393163), (Int.negOfNat 2253214942247355261197), (Int.negOfNat 165985275736277484026), (Int.ofNat 7319463459712788353), (Int.ofNat 537984791765768670), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(273015615120505525565161274905461/351843720888320000000000000000000), (-215041064577640281066512022763917/562949953421312000000000000000000), (-45895291600870814520395579226283/1125899906842624000000000000000000), (54316284952273073618901486922769/5629499534213120000000000000000000), (6100090231843032569934392512181/5629499534213120000000000000000000), (-496414543332279535396449040327/2814749767106560000000000000000000), (-102023210910251544845514840623/5629499534213120000000000000000000), (11722599278006908906971605271/5629499534213120000000000000000000), (1096103304655937562072565067/5629499534213120000000000000000000), (-93383018821493323468209167/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial159.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial159.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial159.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 354919260802443990459321630976929), (Int.negOfNat 2314208137246777941779558309041757), (Int.ofNat 148248054618028155419931900018440), (Int.ofNat 55010253715831291676659280660420), (Int.negOfNat 5897091816690651588405523014811), (Int.negOfNat 975173789387406569066140689337), (Int.ofNat 104909237651710546813519121682), (Int.ofNat 11682575472809704680325635563), (Int.negOfNat 1110581814859923971908113994), (Int.negOfNat 96236041925386215374501046), (Int.ofNat 7878640597751510748458513), (Int.ofNat 568489628082907212041608), (Int.negOfNat 40121509089039488477511), (Int.negOfNat 2502714778978550487311), (Int.ofNat 153987098171025869429), (Int.ofNat 8387105349047044625), (Int.negOfNat 483351318920078818), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-354919260802443990459321630976929/5629499534213120000000000000000000), (-2314208137246777941779558309041757/5629499534213120000000000000000000), (3706201365450703885498297500461/140737488355328000000000000000000), (2750512685791564583832964033021/281474976710656000000000000000000), (-5897091816690651588405523014811/5629499534213120000000000000000000), (-975173789387406569066140689337/5629499534213120000000000000000000), (52454618825855273406759560841/2814749767106560000000000000000000), (11682575472809704680325635563/5629499534213120000000000000000000), (-555290907429961985954056997/2814749767106560000000000000000000), (-48118020962693107687250523/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial159.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial159.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial159.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial159.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial159.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial159.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial159.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial159.reflect := by
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

end Bin159
end
end ErdosOverlap.OuterNumerics
